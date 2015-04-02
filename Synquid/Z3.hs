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
import Control.Lens

import System.IO.Unsafe

-- | Z3 state while building constraints
data Z3Data = Z3Data {
  _intSort :: Maybe Sort,     -- ^ Int sort
  _boolSort :: Maybe Sort,    -- ^ Boolean sort
  _symbols :: Map Id Symbol   -- ^ Variable symbols
}

makeLenses ''Z3Data

type Z3State = StateT Z3Data Z3   

instance MonadZ3 Z3State where
  getSolver = lift getSolver
  getContext = lift getContext
        
emptyData :: Z3Data
emptyData = Z3Data Nothing Nothing Map.empty

evalZ3State :: Z3State a -> IO a
evalZ3State f = do
  env <- newEnv (Just QF_AUFLIA) stdOpts
  evalZ3WithEnv (evalStateT f emptyData) env
                
-- | Convert a first-order constraint to a Z3 AST.
toZ3 :: Formula -> Z3State AST
toZ3 expr = case expr of
  BoolLit True  -> mkTrue
  BoolLit False -> mkFalse
  IntLit i -> mkInt i  
  Var ident -> var ident
  Parameter ident -> var ident
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
    
-- | 'extractModel' @fmls model@: a mapping from variables of @fmls@ to values encoded in Z3 @model@
extractModel :: [Formula] -> Model -> Z3State SMTModel
extractModel fmls model = foldM addVar Map.empty allVars
  where
    allVars = Set.toList $ Set.unions $ map (\fml -> varsOf fml `Set.union` paramsOf fml) fmls
    addVar smtMod ident = do
      symbMb <- uses symbols (Map.lookup ident)
      case symbMb of
        Nothing -> error $ unwords ["extractModel: symbol not found for", ident]
        Just s -> do
          is <- fromJust <$> use intSort
          node <- mkConst s is
          resMb <- eval model node
          case resMb of
            Nothing -> error $ unwords ["extractModel: model not found for", ident]
            Just val -> do
              kind <- getAstKind val
              case kind of
                Z3_NUMERAL_AST -> getInt val >>= (\i -> return $ Map.insert ident i smtMod) -- Exact value: extract it
                Z3_APP_AST -> return $ Map.insert ident 0 smtMod -- Value did not matter: return 0
        
instance SMTSolver Z3State where
  initSolver = do
    int <- mkIntSort
    intSort .= Just int
    bool <- mkBoolSort
    boolSort .= Just bool

  isValid fml = do
      res <- local $ (toZ3 >=> assertCnstr) (fnot fml) >> check
      case res of
        Unsat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "VALID") $ return True
        Sat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "INVALID") $ return False    
        _ -> error $ unwords ["isValid: Z3 returned Unknown for", show fml]
        
  modelOf = getModelOf
  
  unsatCore = getMinUnsatCore
        
-- | 'getModelOf' @fmls assumptions@: a model of conjunction of @fmls@ under as many optional @assumptions@ as possible (together with the assumptions that were satisfied)
getModelOf :: [Formula] -> [Formula] -> Z3State (Maybe (SMTModel, [Formula]))
getModelOf fmls assumptions = do
  push
  mapM_ (toZ3 >=> assertCnstr) fmls
  
  bool <- fromJust <$> use boolSort
  controlLiterals <- mapM (\i -> mkStringSymbol ("ctrl" ++ show i) >>= flip mkConst bool) [1 .. length assumptions] -- ToDo: unique ids
  assumptionsZ3 <- mapM toZ3 assumptions
  condAssumptions <- zipWithM mkImplies controlLiterals assumptionsZ3                      
  mapM_ assertCnstr condAssumptions
  
  satLitsMb <- go [controlLiterals]
  case satLitsMb of
    Nothing -> debug 2 (text "SMT MODEL" <+> problemDoc <+> text "UNSAT") $ pop 1 >> return Nothing
    Just satLiterals -> do
      let satAssumptions = [a | (l, a) <- zip controlLiterals assumptions, l `elem` satLiterals]
      mapM_ assertCnstr satLiterals
      (_, Just model) <- getModel
      m <- extractModel fmls model          
      debug 2 (text "SMT MODEL" <+> problemDoc <+> text "SAT" <+> pretty m) $ pop 1          
      return $ Just (m, satAssumptions)    
    
  where
    go [] = return Nothing
    go (lits : rest) = do      
      res <- checkAssumptions lits
      case res of
        Sat -> return $ Just lits
        Unsat -> do          
          unsatLits <- getUnsatCore
          coreDebugMsg lits unsatLits
          go $ rest ++ map (flip delete lits) unsatLits
        _ -> error $ unwords ["modelOf: Z3 returned Unknown for", show fmls, "(under", show (length lits), "assumptions)"]
        
    problemDoc = commaSep (map pretty fmls) <+> braces (commaSep (map pretty assumptions))
    coreDebugMsg lits unsatLits = do
      strs <- mapM astToString lits
      strs' <- mapM astToString unsatLits
      debug 2 (text "UNSAT CORE OF" <+> braces (hsep (map text strs)) <+> text "IS" <+> braces (hsep (map text strs'))) $ return ()      
      
      
getMinUnsatCore fmls assumptions = do
  push
  mapM_ (toZ3 >=> assertCnstr) fmls
  
  bool <- fromJust <$> use boolSort
  controlLiterals <- mapM (\i -> mkStringSymbol ("ctrl" ++ show i) >>= flip mkConst bool) [1 .. length assumptions] -- ToDo: unique ids
  assumptionsZ3 <- mapM toZ3 assumptions
  condAssumptions <- zipWithM mkImplies controlLiterals assumptionsZ3                      
  mapM_ assertCnstr condAssumptions
  res <- checkAssumptions controlLiterals
  case res of
    Sat -> pop 1 >> return Nothing
    Unsat -> do
      unsatLits <- getUnsatCore
      unsatLits' <- minimize [] unsatLits
      let unsatAssumptions = [a | (l, a) <- zip controlLiterals assumptions, l `elem` unsatLits']
      pop 1
      return $ Just unsatAssumptions
  where
    minimize checked [] = return checked
    minimize checked (lit:lits) = do
      res <- local $ mapM_ assertCnstr (checked ++ lits) >> check
      case res of
        Sat -> minimize (lit:checked) lits -- lit required for UNSAT: leave it in the minimal core
        Unsat -> minimize checked lits -- lit can be omitted
      
        