{-# LANGUAGE TemplateHaskell #-}

-- | Executable programs
module Synquid.Program where

import Synquid.Logic

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
import Control.Lens

data Program s c =
  PSymbol s |
  PApp (Program s c) (Program s c) |
  PIf c (Program s c) (Program s c)  
  
data BaseType = BoolT | IntT
  deriving (Eq, Ord)

data Type =
  ScalarT BaseType Id Formula | -- Use deBrujn indexes instead?
  FunctionT Type Type
  deriving (Eq, Ord)
  
boundVars (ScalarT _ v _) = [v]
boundVars (FunctionT arg fun) = boundVars arg ++ boundVars fun

unifyVarsWith t1 t2 = snd $ unifyVarsWith' Map.empty t1 t2
  where
    unifyVarsWith' m (ScalarT _ v' _) (ScalarT base v fml) = let m' = Map.insert v (Var v') m in (m', ScalarT base v' $ substitute m' fml)
    unifyVarsWith' m (FunctionT tArg' tFun') (FunctionT tArg tFun) = let 
        (m', resArg) = unifyVarsWith' m tArg' tArg
        (m'', resFun) = unifyVarsWith' m' tFun' tFun
      in (m'', FunctionT resArg resFun)
      
typeConjunction (ScalarT base v fml) (ScalarT _ _ fml') = ScalarT base v (fml |&| fml')       
typeConjunction (FunctionT t1 t2) t = FunctionT (typeConjunction t1 t) (typeConjunction t2 t) 
  
data TypeSkeleton =
  ScalarS BaseType |
  FunctionS TypeSkeleton TypeSkeleton 
  deriving (Eq, Ord)
  
shape :: Type -> TypeSkeleton  
shape (ScalarT base _ _) = ScalarS base
shape (FunctionT tArg tFun) = FunctionS (shape tArg) (shape tFun)

type Template = Program TypeSkeleton ()
type LiquidProgram = Program (Environment, Type) Formula
type SimpleProgram = Program Formula Formula

typeApplySolution :: PSolution -> Type -> Type
typeApplySolution sol (ScalarT base name fml) = ScalarT base name (applySolution sol fml)
typeApplySolution sol (FunctionT arg fun) = FunctionT (typeApplySolution sol arg) (typeApplySolution sol fun)

typeSkeletonOf :: Template -> TypeSkeleton
typeSkeletonOf (PSymbol t) = t
typeSkeletonOf (PApp fun _) = let (FunctionS _ t) = typeSkeletonOf fun in t
typeSkeletonOf (PIf _ p _) = typeSkeletonOf p

int_ = ScalarS IntT
(|->|) = FunctionS
sym = PSymbol
choice = PIf ()
(|$|) = PApp

infixr 5 |->|
infixl 5 |$|
  
data Environment = Environment {
  _symbols :: Map Type Formula,
  _assumptions :: Set Formula,
  _negAssumptions :: Set Formula
}

makeLenses ''Environment  

emptyEnv = Environment Map.empty Set.empty Set.empty

addSymbol :: Formula -> Type -> Environment -> Environment
addSymbol sym t = symbols %~ Map.insert t sym

symbolByType :: Type -> Environment -> Formula
symbolByType t env = case view (symbols . to (Map.lookup t)) env of
  Just sym -> sym
  Nothing -> error $ "symbolByType: can't find type"

symbolsByShape :: TypeSkeleton -> Environment -> Map Type Formula
symbolsByShape s env = Map.filterWithKey (\t _ -> shape t == s) $ view symbols env  

addAssumption :: Formula -> Environment -> Environment
addAssumption f = assumptions %~ Set.insert f

addNegAssumption :: Formula -> Environment -> Environment
addNegAssumption f = negAssumptions %~ Set.insert f

restrict :: Type -> Environment -> Environment
restrict t env = over symbols restrict' env
  where
    restrict' symbs = Map.mapKeys (unifyVarsWith t) $ Map.filterWithKey (\t' _ -> shape t' == shape t) symbs
    
extract :: LiquidProgram -> PSolution -> SimpleProgram
extract prog sol = case prog of
  PSymbol (env, t) -> PSymbol $ symbolByType (typeApplySolution sol t) env
  PApp t1 t2 -> PApp (extract t1 sol) (extract t2 sol)
  PIf cond t1 t2 -> PIf (applySolution sol cond) (extract t1 sol) (extract t2 sol)      
      
data Constraint = Subtype Environment Type Type
  | WellFormed Environment Type
  | WellFormedCond Environment Formula
  | WellFormedSymbol Environment Type
  