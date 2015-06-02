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
  FunctionT Id (TypeSkeleton r) (TypeSkeleton r)
  deriving (Eq, Ord)
  
-- | Unrefined typed  
type SType = TypeSkeleton ()  

-- | Refinement types  
type RType = TypeSkeleton Formula

isFunctionType (FunctionT _ _ _) = True
isFunctionType _ = False
argType (FunctionT _ t _) = t

-- | Forget refinements
shape :: RType -> SType  
shape (ScalarT base _) = ScalarT base ()
shape (FunctionT _ tArg tFun) = FunctionT dontCare (shape tArg) (shape tFun)

-- | Insert trivial refinements
refine :: SType -> RType
refine (ScalarT base _) = ScalarT base ftrue
refine (FunctionT _ tArg tFun) = FunctionT dontCare (refine tArg) (refine tFun)
      
-- | 'renameVar' @old new t@: rename all occurrences of @old@ in @t@ into @new@
renameVar :: Id -> Id -> RType -> RType    
renameVar old new (ScalarT base fml) = ScalarT base (substitute (Map.singleton old (Var new)) fml)
renameVar old new (FunctionT x tArg tRes) = FunctionT x (renameVar old new tArg) (renameVar old new tRes)

typeConjunction (ScalarT _ cond) (ScalarT base fml) = ScalarT base (cond |&| fml)
typeConjunction var (FunctionT x tArg tRes) = FunctionT x tArg (typeConjunction var tRes)

-- | Typing environment
data Environment = Environment {
  _symbols :: Map Formula RType,                -- ^ Variables and constants (with their refinement types)
  _symbolsOfShape :: Map SType (Set Formula),   -- ^ Variables and constants indexed by their simple type
  _assumptions :: Set Formula,                  -- ^ Positive unknown assumptions
  _negAssumptions :: Set Formula,               -- ^ Negative unknown assumptions
  _ranks :: [Formula]                           -- ^ Ranking functions
}

makeLenses ''Environment  

-- | Environment with no symbols or assumptions
emptyEnv = Environment Map.empty Map.empty Set.empty Set.empty []

-- | 'addSymbol' @sym t env@ : add type binding @sym@ :: @t@ to @env@
addSymbol :: Formula -> RType -> Environment -> Environment
addSymbol sym t = (symbols %~ Map.insert sym t) . (symbolsOfShape %~ Map.insertWith (Set.union) (shape t) (Set.singleton sym))

-- | 'addSymbol' @sym t env@ : add type binding @sym@ :: @t@ to @env@
addRank :: Formula -> Environment -> Environment
addRank r = ranks %~ (r :)

clearSymbols = set symbols Map.empty . set symbolsOfShape Map.empty
clearAssumptions = set assumptions Set.empty . set negAssumptions Set.empty
clearRanks = set ranks []

-- | 'varRefinement' @v x@ : refinement of a scalar variable
varRefinement x = valueVar |=| Var x
                  
-- | 'symbolsByShape' @s env@ : symbols of simple type @s@ in @env@ 
symbolsByShape :: SType -> Environment -> Map Formula RType
symbolsByShape s env = restrictDomain (Map.findWithDefault Set.empty s (env ^. symbolsOfShape)) (env ^. symbols)

-- | 'addAssumption' @f env@ : @env@ with extra assumption @f@
addAssumption :: Formula -> Environment -> Environment
addAssumption f = assumptions %~ Set.insert f

-- | 'addNegAssumption' @f env@ : @env@ with extra assumption not @f@
addNegAssumption :: Formula -> Environment -> Environment
addNegAssumption f = negAssumptions %~ Set.insert f

-- | Positive and negative formulas encoded in an environment    
embedding :: Environment -> (Set Formula, Set Formula)    
embedding env = ((env ^. assumptions) `Set.union` (Map.foldlWithKey (\fmls s t -> fmls `Set.union` embedBinding s t) Set.empty $ env ^. symbols), env ^.negAssumptions)
  where
    embedBinding _ (ScalarT _ (BoolLit True)) = Set.empty -- Ignore trivial types
    embedBinding (Var x) (ScalarT _ fml) = Set.singleton $ substitute (Map.singleton valueVarName (Var x)) fml
    embedBinding _ _ = Set.empty
    
-- | Program skeletons parametrized by information stored in bound variable positions, symbols, and conditionals
data Program v s c =
  PSymbol s |                             -- ^ Symbol (variable or constant)
  PApp (Program v s c) (Program v s c) |  -- ^ Function application
  PFun v (Program v s c) |                -- ^ Lambda abstraction
  PIf c (Program v s c) (Program v s c) | -- ^ Conditional
  PFix v (Program v s c)                  -- ^ Fixpoint
    
-- | Program templates (skeleton + unrefined types of symbols)
type Template = Program SType SType ()

-- | Fully defined programs 
type SimpleProgram = Program Id Formula Formula

-- | For each symbol, the necessary condition for the symbol to be a solution at a given leaf
type LeafConstraint = Map Formula Formula

-- | Programs where conditions and symbols are represented by constraints with unknowns
type LiquidProgram = Program Id LeafConstraint Formula

-- | Simple type of a program template
sTypeOf :: Template -> SType
sTypeOf (PSymbol t) = t
sTypeOf (PApp fun _) = let (FunctionT _ _ t) = sTypeOf fun in t
sTypeOf (PFun t p) = FunctionT dontCare t (sTypeOf p)
sTypeOf (PIf _ p _) = sTypeOf p
sTypeOf (PFix t _) = t

int = ScalarT IntT
int_ = int ()
(|->|) = FunctionT dontCare
sym = PSymbol
choice = PIf ()
(|$|) = PApp
(|.|) = PFun
fix_ = PFix 

infixr 5 |->|
infixr 5 |$|
infixr 4 |.|
          
-- | Typing constraints
data Constraint = Subtype Environment RType RType
  | WellFormed Environment RType
  | WellFormedCond Environment Formula
  | WellFormedLeaf RType [RType]
  | WellFormedSymbol [[Constraint]]  
  
isWFLeaf (WellFormedLeaf _ _) = True
isWFLeaf _ = False  
  