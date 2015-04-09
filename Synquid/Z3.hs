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

  isValid fml = do
      res <- local $ (toZ3 >=> assert) (fnot fml) >> check
      case res of
        Unsat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "VALID") $ return True
        Sat -> debug 2 (text "SMT CHECK" <+> pretty fml <+> text "INVALID") $ return False    
        _ -> error $ unwords ["isValid: Z3 returned Unknown for", show fml]
        
  unsatCore = getMinUnsatCore
  
getMinUnsatCore fmls mustHaves assumptions = do
  push
  mapM_ (toZ3 >=> assert) fmls
  
  bool <- fromJust <$> use boolSort
  controlLiterals <- mapM (\i -> mkStringSymbol ("ctrl" ++ show i) >>= flip mkConst bool) [1 .. length assumptions] -- ToDo: unique ids
  assumptionsZ3 <- mapM toZ3 assumptions
  condAssumptions <- zipWithM mkImplies controlLiterals assumptionsZ3                      
  mapM_ assert condAssumptions
  
  push
  mapM_ (toZ3 >=> assert) mustHaves  
  
  res <- checkAssumptions controlLiterals
  case res of
    Sat -> pop 2 >> return UCSat
    Unsat -> do
      unsatLits <- getUnsatCore
      unsatLitsMin <- minimize [] unsatLits
      let unsatAssumptions = [a | (l, a) <- zip controlLiterals assumptions, l `elem` unsatLitsMin]
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
  

-- getMinUnsatCore fmls assumptions = do
  -- push
  -- mapM_ (toZ3 >=> assert) fmls
  
  -- bool <- fromJust <$> use boolSort
  -- controlLiterals <- mapM (\i -> mkStringSymbol ("ctrl" ++ show i) >>= flip mkConst bool) [1 .. length assumptions] -- ToDo: unique ids
  -- assumptionsZ3 <- mapM toZ3 assumptions
  -- condAssumptions <- zipWithM mkImplies controlLiterals assumptionsZ3                      
  -- mapM_ assert condAssumptions
  -- res <- checkAssumptions controlLiterals
  -- case res of
    -- Sat -> pop 1 >> return Nothing
    -- Unsat -> do
      -- unsatLits <- getUnsatCore
      -- unsatLits' <- minimize [] unsatLits
      -- let unsatAssumptions = [a | (l, a) <- zip controlLiterals assumptions, l `elem` unsatLits']
      -- pop 1
      -- return $ Just unsatAssumptions
  -- where
    -- minimize checked [] = return checked
    -- minimize checked (lit:lits) = do
      -- res <- local $ mapM_ assert (checked ++ lits) >> check
      -- case res of
        -- Sat -> minimize (lit:checked) lits -- lit required for UNSAT: leave it in the minimal core
        -- Unsat -> minimize checked lits -- lit can be omitted
      
        