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

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Applicative
import Control.Lens hiding (both)

import System.IO.Unsafe

-- | Z3 state while building constraints
data Z3Data = Z3Data {
  _mainEnv :: Z3Env,          -- ^ Z3 environment for the main solver
  _intSort :: Maybe Sort,     -- ^ Int sort
  _boolSort :: Maybe Sort,    -- ^ Boolean sort
  _symbols :: Map Id Symbol,  -- ^ Variable symbols
  _auxEnv :: Z3Env,           -- ^ Z3 environment for the auxiliary solver
  _boolSortAux :: Maybe Sort  -- ^ Boolean sort
}

makeLenses ''Z3Data

type Z3State = StateT Z3Data IO

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
  mainEnv <- newEnv (Just QF_AUFLIA) stdOpts
  auxEnv <- newEnv (Just QF_AUFLIA) stdOpts
  evalStateT f $ Z3Data mainEnv Nothing Nothing Map.empty auxEnv Nothing
                
-- | Convert a first-order constraint to a Z3 AST.
toZ3 :: Formula -> Z3State AST
toZ3 expr = case expr of
  BoolLit True  -> mkTrue
  BoolLit False -> mkFalse
  IntLit i -> mkIntNum i  
  Var ident -> var ident
  Unknown _ ident -> error $ unwords ["toZ3: encountered a second-order unknown", ident]
  Unary op e -> toZ3 e >>= unOp op
  Binary op e1 e2 -> join (binOp op <$> toZ3 e1 <*> toZ3 e2)  
  where
    unOp :: UnOp -> AST -> Z3State AST
    unOp Neg = mkUnaryMinus
    unOp Not = mkNot

    binOp :: BinOp -> AST -> AST -> Z3State AST
    binOp op =
      case op of
        Eq -> mkEq
        Neq -> \ x y -> mkEq x y >>= mkNot
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
    list2 o x y = o [x, y]
    
    var ident = do
      is <- fromJust <$> use intSort
      symbMb <- uses symbols (Map.lookup ident)
      case symbMb of
        Just s -> mkConst s is
        Nothing -> do
          s <- mkStringSymbol ident
          symbols %= Map.insert ident s
          mkConst s is
          
instance SMTSolver Z3State where
  initSolver = do
    int <- mkIntSort
    intSort .= Just int
    bool <- mkBoolSort
    boolSort .= Just bool
    
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
        
-- | 'getAllMUSs' @assumption mustHaves fmls@ : find all minimal unsatisfiable subsets of @mustHaves@ union @fmls@, which contain all elements of @mustHaves@, assuming @assumption@
-- (implements Marco algorithm by Mark H. Liffiton et al.)
getAllMUSs :: Formula -> [Formula] -> [Formula] -> Z3State [[Formula]]
getAllMUSs assumption mustHaves fmls = do
  push
  withAuxSolver push

  bool <- fromJust <$> use boolSort
  boolAux <- fromJust <$> use boolSortAux

  let allFmls = mustHaves ++ fmls  
  controlLits <- mkContolLits bool allFmls
  controlLitsAux <- withAuxSolver $ mkContolLits boolAux allFmls
  
  toZ3 assumption >>= assert
  condAssumptions <- mapM toZ3 allFmls >>= zipWithM mkImplies controlLits  
  mapM_ assert condAssumptions
  
  withAuxSolver $ mapM_ assert $ take (length mustHaves) controlLitsAux
    
  res <- getAllMUSs' allFmls controlLits controlLitsAux (length mustHaves) []    
  withAuxSolver $ pop 1
  pop 1  
  return res
  
  where
    mkContolLits bool fmls = mapM (\i -> mkStringSymbol ("ctrl" ++ show i) >>= flip mkConst bool) [1 .. length fmls] -- ToDo: unique ids

getAllMUSs' fmls controlLits controlLitsAux mustHavesCount cores = do      
  seedMb <- (fmap $ both $ map litFromAux) <$> getNextSeed
  case seedMb of
    Nothing -> return cores -- No uncovered subsets left, return the cores accumulated so far
    Just (seed, rest) -> do
      debug 2 (text "Seed" <+> pretty [a | (l, a) <- zip controlLits fmls, l `elem` seed]) $ return ()
      res <- checkAssumptions seed  -- Check if seed is satisfiable
      case res of
        Unsat -> do
          mus <- getUnsatCore >>= minimize
          withAuxSolver $ mapM (mkNot . litToAux) mus >>= mkOr >>= assert -- Remove all supersets of mus from unexplored sets
          let unsatFmls = [a | (l, a) <- zip (drop mustHavesCount controlLits) (drop mustHavesCount fmls), l `elem` mus]          
          if all (`elem` mus) (take mustHavesCount controlLits)
            then debug 2 (text "MUS" <+> pretty unsatFmls) $ 
                    getAllMUSs' fmls controlLits controlLitsAux mustHavesCount (unsatFmls : cores)
            else debug 2 (text "MUSeless" <+> pretty unsatFmls) $ 
                    getAllMUSs' fmls controlLits controlLitsAux mustHavesCount cores
        Sat -> do
          mss <- maximize seed rest  -- Satisfiable: maximize
          debug 2 (text "MSS" <+> pretty [a | (l, a) <- zip controlLits fmls, l `elem` mss]) $ return ()
          if length mss == length controlLits
            then return []  -- The conjunction of fmls is SAT: no UNSAT cores
            else do
              withAuxSolver $ mkOr (controlLitsAux \\ map litToAux mss) >>= assert  -- Remove all subsets of mss from the unexplored set
              getAllMUSs' fmls controlLits controlLitsAux mustHavesCount cores
              
  where
    litToAux :: AST -> AST
    litToAux lit = controlLitsAux !! fromJust (elemIndex lit controlLits)
    
    litFromAux :: AST -> AST
    litFromAux lit = controlLits !! fromJust (elemIndex lit controlLitsAux)    
                  
    getNextSeed = withAuxSolver $ do
      (res, modelMb) <- getModel -- Get the next seed (uncovered subset of fmls)
      case res of
        Unsat -> return Nothing -- No uncovered subsets left, return the cores accumulated so far
        Sat -> Just <$> partitionM (getCtrlLitModel True (fromJust modelMb)) controlLitsAux
        
    getCtrlLitModel bias m lit = do
      resMb <- fromJust <$> eval m lit >>= getBoolValue
      case resMb of
        Nothing -> return bias
        Just b -> return b
  
    minimize lits = local $ minimize' [] lits
    minimize' checked [] = return checked
    minimize' checked (lit:lits) = do
      res <- checkAssumptions lits
      case res of
        Sat -> assert lit >> minimize' (lit:checked) lits -- lit required for UNSAT: leave it in the minimal core
        Unsat -> minimize' checked lits -- lit can be omitted    
        
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
          
      
        