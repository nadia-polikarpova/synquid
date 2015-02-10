{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, TemplateHaskell #-}

-- | Interface to Z3
module Synquid.Z3 (Z3State, evalZ3State) where

import Synquid.Logic
import Synquid.SMTSolver
import Synquid.Util
import Synquid.Pretty
import Z3.Monad

import Data.Maybe
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
  _intSort :: Maybe Sort,     -- ^ Sorts (so far only int)
  _symbols :: Map Id Symbol   -- ^ Variable symbols
}

makeLenses ''Z3Data

type Z3State = StateT Z3Data Z3   

instance MonadZ3 Z3State where
  getSolver = lift getSolver
  getContext = lift getContext
        
emptyData :: Z3Data
emptyData = Z3Data Nothing Map.empty

evalZ3State :: Z3State a -> IO a
evalZ3State f = do
  env <- newEnv Nothing stdOpts
  evalZ3WithEnv (evalStateT f emptyData) env
                
-- | Convert a first-order constraint to a Z3 AST.
toZ3 :: Formula -> Z3State AST
toZ3 expr = case expr of
  BoolLit True  -> mkTrue
  BoolLit False -> mkFalse
  IntLit i -> mkInt i  
  Var ident -> var ident
  Parameter ident -> var ident
  Unknown ident -> error $ "toZ3: encountered a second-order unknown " ++ ident
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
    
extractModel :: Formula -> Model -> Z3State SMTModel
extractModel fml model = foldM addVar Map.empty (Set.toList $ varsOf fml `Set.union` paramsOf fml)
  where
    addVar smtMod ident = do
      symbMb <- uses symbols (Map.lookup ident)
      case symbMb of
        Nothing -> error $ "extractModel: symbol not found for " ++ ident
        Just s -> do
          is <- fromJust <$> use intSort
          node <- mkConst s is
          resMb <- eval model node
          case resMb of
            Nothing -> error $ "extractModel: model not found for " ++ ident
            Just val -> do
              kind <- getAstKind val
              case kind of
                Z3_NUMERAL_AST -> getInt val >>= (\i -> return $ Map.insert ident i smtMod) -- Exact value: extract it
                Z3_APP_AST -> return $ Map.insert ident 0 smtMod -- Value did not matter: return 0
        
instance SMTSolver Z3State where
  initSolver = do
    is <- mkIntSort
    intSort .= Just is

  isValid fml = do
      res <- local $ (toZ3 >=> assertCnstr) (fnot fml) >> check
      case res of
        Unsat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "VALID") $ return True
        Sat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "INVALID") $ return False    
        _ -> error $ "isValid: Z3 returned Unknown for " ++ show fml
        
  modelOf fml = do
      push
      (res, modelMb) <- (toZ3 >=> assertCnstr) fml >> getModel      
      case res of
        Unsat -> debug 2 (text "SMT MODEL" <+> pretty fml <+> text "UNSAT") $ pop 1 >> return Nothing
        Sat -> do
          let model = fromJust modelMb
          m <- extractModel fml model          
          debug 2 (text "SMT MODEL" <+> pretty fml <+> text "SAT" <+> pretty m) $ delModel model
          pop 1          
          return (Just m)
        _ -> error $ "modelOf: Z3 returned Unknown for " ++ show fml
      