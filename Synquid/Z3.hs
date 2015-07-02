{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, TemplateHaskell #-}

-- | Interface to Z3
module Synquid.Z3 (Z3State, evalZ3State) where

import Synquid.Logic
import Synquid.SMTSolver
import Synquid.Util
import Synquid.Pretty
import Z3.Monad

import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Bimap as Bimap
import Data.Bimap (Bimap)

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Applicative
import Control.Lens hiding (both)

import System.IO.Unsafe

-- | Z3 state while building constraints
data Z3Data = Z3Data {
  _mainEnv :: Z3Env,                          -- ^ Z3 environment for the main solver
  _intSort :: Maybe Sort,                     -- ^ Int sort
  _boolSort :: Maybe Sort,                    -- ^ Boolean sort
  _setSort :: Maybe Sort,                     -- ^ Sort for integer sets
  _typeVarSorts :: Map Id Sort,
  _datatypeSorts :: Map Id Sort,              -- ^ Sorts for user-defined datatypes
  _vars :: Map Id AST,                        -- ^ AST nodes for scalar variables
  _measures :: Map Id FuncDecl,               -- ^ Function declarations for measures
  _controlLiterals :: Bimap Formula AST,      -- ^ Control literals for computing UNSAT cores
  _auxEnv :: Z3Env,                           -- ^ Z3 environment for the auxiliary solver
  _boolSortAux :: Maybe Sort,                 -- ^ Boolean sort in the auxiliary solver  
  _controlLiteralsAux :: Bimap Formula AST    -- ^ Control literals for computing UNSAT cores in the auxiliary solver
}

makeLenses ''Z3Data

initZ3Data env env' = Z3Data {
  _mainEnv = env,
  _intSort = Nothing,
  _boolSort = Nothing,
  _setSort = Nothing,
  _typeVarSorts = Map.empty,
  _datatypeSorts = Map.empty,
  _vars = Map.empty,
  _measures = Map.empty,
  _controlLiterals = Bimap.empty,
  _auxEnv = env',
  _boolSortAux = Nothing,
  _controlLiteralsAux = Bimap.empty  
} 

type Z3State = StateT Z3Data IO

-- | Get the literal in the auxiliary solver that corresponds to a given literal in the main solver
litToAux :: AST -> Z3State AST
litToAux lit = do
  fml <- uses controlLiterals (Bimap.!> lit)
  uses controlLiteralsAux (Bimap.! fml)

-- | Get the literal in the main solver that corresponds to a given literal in the auxiliary solver  
litFromAux :: AST -> Z3State AST
litFromAux lit = do
  fml <- uses controlLiteralsAux (Bimap.!> lit)
  uses controlLiterals (Bimap.! fml)
  
instance MonadZ3 Z3State where
  getSolver = gets (envSolver . _mainEnv)
  getContext = gets (envContext . _mainEnv)
        
-- | Use auxiliary solver to execute a Z3 computation
withAuxSolver :: Z3State a -> Z3State a
withAuxSolver c = do
  m <- use mainEnv
  a <- use auxEnv
  mainEnv .= a
  res <- c
  mainEnv .= m
  return res

evalZ3State :: Z3State a -> IO a
evalZ3State f = do
  -- env <- newEnv (Just QF_AUFLIA) stdOpts
  -- env' <- newEnv (Just QF_AUFLIA) stdOpts
  env <- newEnv Nothing stdOpts
  env' <- newEnv Nothing stdOpts  
  evalStateT f $ initZ3Data env env'
                
-- | Convert a first-order constraint to a Z3 AST.
toZ3 :: Formula -> Z3State AST
toZ3 expr = case expr of
  BoolLit True  -> mkTrue
  BoolLit False -> mkFalse
  SetLit xs -> setLiteral xs
  IntLit i -> mkIntNum i  
  Var b ident -> var b ident
  Unknown _ ident -> error $ unwords ["toZ3: encountered a second-order unknown", ident]
  Unary op e -> toZ3 e >>= unOp op
  Binary op e1 e2 -> join (binOp op <$> toZ3 e1 <*> toZ3 e2)  
  Measure b ident arg -> do
    decl <- measure b ident (baseTypeOf arg)
    mapM toZ3 [arg] >>= mkApp decl
  where
    sort BoolT = fromJust <$> use boolSort
    sort IntT = fromJust <$> use intSort
    sort SetT = fromJust <$> use setSort
    sort (TypeVarT name) = do
      resMb <- uses typeVarSorts (Map.lookup name)
      case resMb of
        Just s -> return s
        Nothing -> do
          s <- mkStringSymbol name >>= mkUninterpretedSort
          typeVarSorts %= Map.insert name s
          return s                      
    sort (DatatypeT name) = do
      resMb <- uses datatypeSorts (Map.lookup name)
      case resMb of
        Just s -> return s
        Nothing -> do
          s <- mkStringSymbol name >>= mkUninterpretedSort
          datatypeSorts %= Map.insert name s
          return s
    
    setLiteral xs = do
      emp <- (fromJust <$> use intSort) >>= mkEmptySet
      elems <- mapM toZ3 xs
      foldM mkSetAdd emp elems
  
    unOp :: UnOp -> AST -> Z3State AST
    unOp Neg = mkUnaryMinus
    unOp Not = mkNot

    binOp :: BinOp -> AST -> AST -> Z3State AST
    binOp op =
      case op of
        Eq -> mkEq
        Neq -> list2 mkDistinct
        Gt -> mkGt
        Lt -> mkLt
        Le -> mkLe
        Ge -> mkGe  
        Times -> list2 mkMul
        Plus -> list2 mkAdd
        Minus -> list2 mkSub
        And   -> list2 mkAnd
        Or    -> list2 mkOr
        Implies -> mkImplies
        Iff -> mkIff
        Union -> list2 mkSetUnion
        Intersect -> list2 mkSetIntersect
        Diff -> mkSetDifference
        Member -> mkSetMember
        Subset -> mkSetSubset
    list2 o x y = o [x, y]
      
    -- | Lookup or create a variable with name `ident' and type `baseT' 
    var baseT ident = do
      s <- sort baseT
      let ident' = ident ++ show baseT
      varMb <- uses vars (Map.lookup ident')
            
      case varMb of
        Just v -> return v
        Nothing -> createVar s ident'

    -- | Create and cache a variable with name `ident' and type `baseT'
    createVar sort ident = do
      symb <- mkStringSymbol ident
      v <- mkConst symb sort
      vars %= Map.insert ident v
      return v        
      
    -- | Lookup or create a measure declaration with name `ident', type `baseT', and argument type `argType'
    measure baseT ident argType = do
      declMb <- uses measures (Map.lookup ident)
      case declMb of
        Just d -> return d
        Nothing -> do
          symb <- mkStringSymbol ident
          argSort <- sort argType
          decl <- sort baseT >>= mkFuncDecl symb [argSort]
          measures %= Map.insert ident decl
          return decl      
          
instance SMTSolver Z3State where
  initSolver = do
    int <- mkIntSort
    intSort .= Just int
    bool <- mkBoolSort
    boolSort .= Just bool
    set <- mkSetSort int
    setSort .= Just set    
    
    boolAux <- withAuxSolver mkBoolSort
    boolSortAux .= Just boolAux

  isValid fml = do
      res <- local $ (toZ3 >=> assert) (fnot fml) >> check      
      
      case res of
        Unsat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "VALID") $ return True
        Sat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "INVALID") $ return False    
        _ -> error $ unwords ["isValid: Z3 returned Unknown for", show fml]
        
  unsatCore = getMinUnsatCore  
  allUnsatCores = getAllMUSs
    
-- | 'getMinUnsatCore' @assumptions mustHaves fmls@ : Get minimal UNSAT core of @fmls@ assuming @assumptions@ and @mustHaves@,
-- such that at least one of @mustHaves@ is required for unsatisfiability.   
getMinUnsatCore assumptions mustHaves fmls = do
  push
  mapM_ (toZ3 >=> assert) assumptions
  
  bool <- fromJust <$> use boolSort  
  
  controlLiterals <- mapM (\i -> mkStringSymbol ("ctrl" ++ show i) >>= flip mkConst bool) [1 .. length fmls] -- ToDo: unique ids
  condAssumptions <- mapM toZ3 fmls >>= zipWithM mkImplies controlLiterals                      
  mapM_ assert condAssumptions
  
  push
  mapM_ (toZ3 >=> assert) mustHaves  
  
  res <- checkAssumptions controlLiterals
  case res of
    Sat -> pop 2 >> return UCSat
    Unsat -> do
      unsatLits <- getUnsatCore
      unsatLitsMin <- minimize [] unsatLits
      let unsatAssumptions = [a | (l, a) <- zip controlLiterals fmls, l `elem` unsatLitsMin]
      pop 1 -- remove mustHaves
      res <- local $ mapM_ assert unsatLitsMin >> check
      pop 1
      case res of
        Sat -> return $ UCGood unsatAssumptions
        Unsat -> return $ UCBad unsatAssumptions
  where
    minimize checked [] = return checked
    minimize checked (lit:lits) = do
      res <- local $ mapM_ assert (checked ++ lits) >> check
      case res of
        Sat -> minimize (lit:checked) lits -- lit required for UNSAT: leave it in the minimal core
        Unsat -> minimize checked lits -- lit can be omitted
        
-- | 'getAllMUSs' @assumption mustHave fmls@ : find all minimal unsatisfiable subsets of @fmls@ with @mustHave@, which contain @mustHave@, assuming @assumption@
-- (implements Marco algorithm by Mark H. Liffiton et al.)
getAllMUSs :: Formula -> Formula -> [Formula] -> Z3State [[Formula]]
getAllMUSs assumption mustHave fmls = do
  push
  withAuxSolver push
  
  let allFmls = mustHave : fmls  
  (controlLits, controlLitsAux) <- unzip <$> mapM getControlLits allFmls
  
  toZ3 assumption >>= assert 
  condAssumptions <- mapM toZ3 allFmls >>= zipWithM mkImplies controlLits  
  mapM_ assert $ condAssumptions
  withAuxSolver $ assert $ head controlLitsAux
    
  res <- getAllMUSs' controlLitsAux (head controlLits) []
  withAuxSolver $ pop 1
  pop 1  
  return res
  
  where
    getControlLits fml = do
      litMb <- uses controlLiterals (Bimap.lookup fml)      
      case litMb of
        Just lit -> do
          litAux <- uses controlLiteralsAux (Bimap.! fml)
          return (lit, litAux)
        Nothing -> do
          bool <- fromJust <$> use boolSort
          boolAux <- fromJust <$> use boolSortAux
          name <- ((++ "lit") . show . Bimap.size) <$> use controlLiterals
          lit <- mkStringSymbol name >>= flip mkConst bool
          litAux <- withAuxSolver $ mkStringSymbol name >>= flip mkConst boolAux          
          controlLiterals %= Bimap.insert fml lit
          controlLiteralsAux %= Bimap.insert fml litAux
          return (lit, litAux)          
                    
getAllMUSs' controlLitsAux mustHave cores = do      
  seedMb <- getNextSeed
  case seedMb of
    Nothing -> return cores -- No uncovered subsets left, return the cores accumulated so far
    Just s -> do
      (seed, rest) <- bothM (mapM litFromAux) s
      mapM litToFml seed >>= debugOutput "Seed"
      res <- checkAssumptions seed  -- Check if seed is satisfiable
      case res of
        Unsat -> do                 -- Unsatisfiable: extract MUS
          mus <- getUnsatCore >>= minimize
          blockUp mus
          unsatFmls <- mapM litToFml (delete mustHave mus)
          if mustHave `elem` mus
            then do
                  debugOutput "MUS" unsatFmls
                  getAllMUSs' controlLitsAux mustHave (unsatFmls : cores)
            else do
                  debugOutput "MUSeless" unsatFmls
                  getAllMUSs' controlLitsAux mustHave cores
        Sat -> do
          mss <- maximize seed rest  -- Satisfiable: expand to MSS                    
          blockDown mss
          mapM litToFml mss >>= debugOutput "MSS"
          getAllMUSs' controlLitsAux mustHave cores
              
  where
    -- | Get the formula mapped to a given control literal in the main solver
    litToFml = uses controlLiterals . flip (Bimap.!>)
    
    -- | Get an unexplored subset of control literals inside the auxiliary solver
    getNextSeed = withAuxSolver $ do
      (res, modelMb) <- getModel
      case res of
        Unsat -> return Nothing -- No unexplored subsets left
        Sat -> Just <$> partitionM (getCtrlLitModel True (fromJust modelMb)) controlLitsAux -- Found unexplored subset: partition @controlLitsAux@ according to the model
    
    -- | Extract the Boolean value for literal @lit@ from the model @m@ with default @bias@
    getCtrlLitModel bias m lit = do
      resMb <- fromJust <$> eval m lit >>= getBoolValue
      case resMb of
        Nothing -> return bias
        Just b -> return b        
        
    -- | Mark all supersets of @mus@ explored
    blockUp mus = withAuxSolver $ mapM (litToAux >=> mkNot) mus >>= mkOr >>= assert

    -- | Mark all subsets of @mss@ explored
    blockDown mss = withAuxSolver $ do
      mss' <- mapM litToAux mss
      let rest = controlLitsAux \\ mss'
      (if null rest then mkFalse else mkOr rest) >>= assert        
                  
    -- | Shrink unsatisfiable set @lits@ to some MUS
    minimize lits = local $ minimize' [] lits
    minimize' checked [] = return checked
    minimize' checked (lit:lits) = do
      res <- checkAssumptions lits
      case res of
        Sat -> assert lit >> minimize' (lit:checked) lits -- lit required for UNSAT: leave it in the minimal core
        Unsat -> minimize' checked lits -- lit can be omitted    
        
    -- | Grow satisfiable set @checked@ with literals from @rest@ to some MSS
    maximize checked rest = local $ mapM_ assert checked >> maximize' checked rest    
    maximize' checked [] = return checked -- checked includes all literals and thus must be maximal
    maximize' checked rest = do
      mkOr rest >>= assert
      (res, modelMb) <- getModel
      case res of
        Unsat -> return checked -- cannot add any literals, checked is maximal
        Sat -> do -- found some literals to add; fix them and continue
          (setRest, unsetRest) <- partitionM (getCtrlLitModel True (fromJust modelMb)) rest
          mapM_ assert setRest
          maximize' (checked ++ setRest) unsetRest
          
    debugOutput label fmls = debug 2 (text label <+> pretty fmls) $ return ()
          
      
        