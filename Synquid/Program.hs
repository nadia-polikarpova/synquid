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
resType (FunctionT _ _ t) = t

-- | Forget refinements
shape :: RType -> SType  
shape (ScalarT base _) = ScalarT base ()
shape (FunctionT _ tArg tFun) = FunctionT dontCare (shape tArg) (shape tFun)

-- | Insert trivial refinements
refine :: SType -> RType
refine (ScalarT base _) = ScalarT base ftrue
refine (FunctionT x tArg tFun) = FunctionT x (refine tArg) (refine tFun)
      
-- | 'renameVar' @old new t@: rename all occurrences of @old@ in @t@ into @new@
renameVar :: Id -> Id -> RType -> RType    
renameVar old new (ScalarT base fml) = ScalarT base (substitute (Map.singleton old (Var new)) fml)
renameVar old new (FunctionT x tArg tRes) = FunctionT x (renameVar old new tArg) (renameVar old new tRes)

typeConjunction (ScalarT _ cond) (ScalarT base fml) = ScalarT base (cond |&| fml)
typeConjunction var (FunctionT x tArg tRes) = FunctionT x tArg (typeConjunction var tRes)

typeApplySolution sol (ScalarT base fml) = ScalarT base (applySolution sol fml)
typeApplySolution sol (FunctionT x tArg tRes) = FunctionT x (typeApplySolution sol tArg) (typeApplySolution sol tRes) 

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
data BareProgram s c t =
  PSymbol s |                         -- ^ Symbol (variable or constant)
  PApp (Program s c t) (Program s c t) |  -- ^ Function application
  PFun Id (Program s c t) |             -- ^ Lambda abstraction
  PIf c (Program s c t) (Program s c t) | -- ^ Conditional
  PFix Id (Program s c t)               -- ^ Fixpoint
  
data Program s c t = Program {
  content :: BareProgram s c t,
  typ :: t
}
    
-- | Program templates (skeleton + unrefined types of symbols)
type Template = Program () () SType

-- | Fully defined programs 
type SimpleProgram = Program Formula Formula RType

-- | For each symbol, a sufficient condition for the symbol to be a solution at a given leaf
type LeafConstraint = Map Formula Constraint

-- | Programs where conditions and symbols are represented by constraints with unknowns
type LiquidProgram = Program LeafConstraint Formula RType

-- | Building type shapes
int = ScalarT IntT
int_ = int ()
(|->|) = FunctionT dontCare

-- | Building program templates
sym s = Program (PSymbol ()) s
(|$|) fun arg = let (FunctionT _ _ t) = typ fun in Program (PApp fun arg) t
(|.|) x p = Program (PFun x p) (FunctionT x int_ (typ p))
choice t e = Program (PIf () t e) (typ t)
fix_ f p = Program (PFix f p) (typ p)

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
  