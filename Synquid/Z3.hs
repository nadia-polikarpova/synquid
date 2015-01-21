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
evalZ3State f = evalZ3 $ evalStateT f emptyData
      
-- | Convert a list of first-order constraints to a Z3 AST and check their satisfiability.
buildAndSolve :: Formula -> Z3State Result
buildAndSolve constraint = (toZ3 >=> assertCnstr) constraint >> check
          
-- | Convert a first-order constraint to a Z3 AST.
toZ3 :: Formula -> Z3State AST
toZ3 expr = case expr of
  BoolLit True  -> mkTrue
  BoolLit False -> mkFalse
  IntLit i -> mkInt i  
  Var ident -> do
    is <- fromJust <$> use intSort
    symbMb <- uses symbols (Map.lookup ident)
    case symbMb of
      Just s -> mkConst s is
      Nothing -> do
        s <- mkStringSymbol ident
        symbols %= Map.insert ident s
        mkConst s is
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
        Plus -> list2 mkAdd
        Minus -> list2 mkSub
        And   -> list2 mkAnd
        Or    -> list2 mkOr
        Implies -> mkImplies
        Iff -> mkIff
    list2 o x y = o [x, y]
        
instance SMTSolver Z3State where
  initSolver = do
    is <- mkIntSort
    intSort .= Just is

  isValid fml = do  
      res <- local $ buildAndSolve $ fnot fml
      case res of
        Unsat -> debug2 (text "SMT" <+> pretty fml <+> text "VALID") $ return True
        Sat -> debug2 (text "SMT" <+> pretty fml <+> text "INVALID") $ return False    
        _ -> error $ "isValid: Z3 returned Unknown"
      