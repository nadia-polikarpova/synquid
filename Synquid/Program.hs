{-# LANGUAGE TemplateHaskell #-}

-- | Executable programs
module Synquid.Program where

import Synquid.Logic
import Synquid.Util

import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
import Control.Lens
  
-- | Base types  
data BaseType = BoolT | IntT
  deriving (Eq, Ord)

-- | Type skeletons parametrized by refinements  
data TypeSkeleton r =
  ScalarT BaseType r |
  FunctionT (TypeSkeleton r) (TypeSkeleton r)
  deriving (Eq, Ord)
  
-- | Unrefined typed  
type SType = TypeSkeleton ()  

-- | Refinement types  
type RType = TypeSkeleton (Id, Formula)

-- | Forget refinements
shape :: RType -> SType  
shape (ScalarT base _) = ScalarT base ()
shape (FunctionT tArg tFun) = FunctionT (shape tArg) (shape tFun)
  
-- | The value variable of a refinement type
valueVar :: RType -> Formula
valueVar (ScalarT _ (v, _)) = Var v
valueVar (FunctionT _ res) = valueVar res

-- | 'unifyVarsWith' @t' t@: @t@ with value variables replaced by the corresponding ones from @t'@
-- (the types must have the same shape)
unifyVarsWith :: RType -> RType -> RType
unifyVarsWith t' t = snd $ unifyVarsWith' Map.empty t' t
  where
    unifyVarsWith' m (ScalarT _ (v', _)) (ScalarT base (v, fml)) = let m' = Map.insert v (Var v') m in (m', ScalarT base (v', substitute m' fml))
    unifyVarsWith' m (FunctionT tArg' tFun') (FunctionT tArg tFun) = let 
        (m', resArg) = unifyVarsWith' m tArg' tArg
        (m'', resFun) = unifyVarsWith' m' tFun' tFun
      in (m'', FunctionT resArg resFun)

-- | 'typeApplySolution' @sol t@: replace all unknowns in @t@ with their valuations in @sol@
typeApplySolution :: PSolution -> RType -> RType
typeApplySolution sol (ScalarT base (v, fml)) = ScalarT base (v, applySolution sol fml)
typeApplySolution sol (FunctionT arg fun) = FunctionT (typeApplySolution sol arg) (typeApplySolution sol fun)

-- | Typing environment
data Environment = Environment {
  _symbols :: Map Formula RType,                -- ^ Variables and constants (with their refinement types)
  _symbolsOfShape :: Map SType (Set Formula),   -- ^ Variables and constants indexed by their simple type
  _assumptions :: Set Formula,                  -- ^ Positive unknown assumptions
  _negAssumptions :: Set Formula                -- ^ Negative unknown assumptions
}

makeLenses ''Environment  

-- | Environment with no symbols or assumptions
emptyEnv = Environment Map.empty Map.empty Set.empty Set.empty

-- | 'addSymbol' @sym t env@ : add type binding @sym@ :: @t@ to @env@
addSymbol :: Formula -> RType -> Environment -> Environment
addSymbol sym t = (symbols %~ Map.insert sym t) . (symbolsOfShape %~ Map.insertWith (Set.union) (shape t) (Set.singleton sym))

-- | 'varRefinement' @v x@ : refinement of a scalar variable
varRefinement v x = Var v |=| Var x

-- | 'varFromRefinement' @v fml@ : if @fml@ is a variable refinement, return the variable
varFromRefinement v (Binary Eq (Var v') (Var x))
  | v == v' = Just $ Var x
varFromRefinement _ _ = Nothing

-- | 'symbolByType' @t env@ : symbol of type @t@ in @env@
symbolByType :: RType -> Environment -> Formula
symbolByType t env = case t of
  (ScalarT _ (v, fml)) -> case varFromRefinement v fml of
    Just sym -> sym
    Nothing -> envLookup
  _ -> envLookup
  where
    envLookup = case Map.toList $ Map.filter (== t) $ symbolsByShape (shape t) env of
                  (sym, _):_ -> sym
                  _ -> error $ "symbolByType: can't find type"

                  
-- | 'symbolsByShape' @s env@ : symbols of simple type @s@ in @env@ 
symbolsByShape :: SType -> Environment -> Map Formula RType
symbolsByShape s env = restrictDomain (Map.findWithDefault Set.empty s (env ^. symbolsOfShape)) (env ^. symbols)

-- | 'addAssumption' @f env@ : @env@ with extra assumption @f@
addAssumption :: Formula -> Environment -> Environment
addAssumption f = assumptions %~ Set.insert f

-- | 'addNegAssumption' @f env@ : @env@ with extra assumption not @f@
addNegAssumption :: Formula -> Environment -> Environment
addNegAssumption f = negAssumptions %~ Set.insert f

-- | 'restrict' @t env@ : @env@ with only those symbols whose simple type matches the shape of @t@, and variables renamed accordingly
restrict :: RType -> Environment -> Environment
restrict t env = env {_symbols = Map.map (unifyVarsWith t) $ symbolsByShape (shape t) env}
    
-- | Positive and negative formulas encoded in an environment    
embedding :: Environment -> (Set Formula, Set Formula)    
embedding env = ((env ^. assumptions) `Set.union` (Map.foldlWithKey (\fmls s t -> fmls `Set.union` embedBinding s t) Set.empty $ env ^. symbols), env ^.negAssumptions)
  where
    embedBinding _ (ScalarT _ (_, BoolLit True)) = Set.empty -- Ignore trivial types
    embedBinding (Var x) (ScalarT _ (v, fml)) = Set.singleton $ substitute (Map.singleton v (Var x)) fml -- Scalar variables are embedded as variable refinements
    embedBinding _ _ = Set.empty
    
-- | Program skeletons parametrized by information stored in symbols and conditionals
data Program s c =
  PSymbol s |
  PApp (Program s c) (Program s c) |
  PFun s (Program s c) |
  PIf c (Program s c) (Program s c)    
    
-- | Program templates (skeleton + unrefined types of symbols)
type Template = Program SType ()

-- | Fully defined programs 
type SimpleProgram = Program Formula Formula

-- | Programs where symbols are represented by their refinement type, which might contain unknowns
type LiquidProgram = Program (Environment, RType) Formula

-- | Simple type of a program template
sTypeOf :: Template -> SType
sTypeOf (PSymbol t) = t
sTypeOf (PApp fun _) = let (FunctionT _ t) = sTypeOf fun in t
sTypeOf (PFun t p) = FunctionT t (sTypeOf p)
sTypeOf (PIf _ p _) = sTypeOf p

int_ = ScalarT IntT ()
(|->|) = FunctionT
sym = PSymbol
choice = PIf ()
(|$|) = PApp
(|.|) = PFun

infixr 5 |->|
infixr 5 |$|
infixr 4 |.|
    
-- | 'extract' @prog sol@ : simple program encoded in @prog@ when all unknowns are instantiated according to @sol@
extract :: LiquidProgram -> PSolution -> SimpleProgram
extract prog sol = case prog of
  PSymbol (env, t) -> PSymbol $ symbolByType (typeApplySolution sol t) env
  PApp pFun pArg -> PApp (extract pFun sol) (extract pArg sol)
  PFun (env, t) p -> PFun (symbolByType (typeApplySolution sol t) env) (extract p sol)
  PIf cond pThen pElse -> PIf (applySolution sol cond) (extract pThen sol) (extract pElse sol)      
      
-- | Typing constraints
data Constraint = Subtype Environment RType RType
  | WellFormed Environment RType
  | WellFormedCond Environment Formula
  | WellFormedSymbol Environment RType
  