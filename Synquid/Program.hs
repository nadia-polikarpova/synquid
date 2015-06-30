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
baseType (ScalarT b _) = b
baseType (FunctionT _ _ t) = baseType t
argType (FunctionT _ t _) = t
resType (FunctionT _ _ t) = t

-- | Forget refinements
shape :: RType -> SType  
shape (ScalarT base _) = ScalarT base ()
shape (FunctionT _ tArg tFun) = FunctionT dontCare (shape tArg) (shape tFun)

-- | Insert weakest refinements
refineTop :: SType -> RType
refineTop (ScalarT base _) = ScalarT base ftrue
refineTop (FunctionT x tArg tFun) = FunctionT x (refineBot tArg) (refineTop tFun)

-- | Insert strongest refinements
refineBot :: SType -> RType
refineBot (ScalarT base _) = ScalarT base ffalse
refineBot (FunctionT x tArg tFun) = FunctionT x (refineTop tArg) (refineBot tFun)
      
-- | 'renameVar' @old new t@: rename all occurrences of @old@ in @t@ into @new@
renameVar :: Id -> Id -> RType -> RType -> RType
renameVar old new (FunctionT _ _ _)   t = t -- function arguments cannot occur in types
renameVar old new (ScalarT b _)  (ScalarT base fml) = ScalarT base (substitute (Map.singleton old (Var b new)) fml)
renameVar old new t              (FunctionT x tArg tRes) = FunctionT x (renameVar old new t tArg) (renameVar old new t tRes)

typeApplySolution sol (ScalarT base fml) = ScalarT base (applySolution sol fml)
typeApplySolution sol (FunctionT x tArg tRes) = FunctionT x (typeApplySolution sol tArg) (typeApplySolution sol tRes) 

-- | User-defined datatype representation
data Datatype = Datatype {
  _constructors :: [Id],                    -- ^ Constructor names
  _wfMetric :: Maybe (Formula -> Formula)   -- ^ Given a datatype term, returns an integer term that can serve as a well-founded metric for recursion
}

makeLenses ''Datatype

-- | Typing environment
data Environment = Environment {
  _symbols :: Map Id RType,                -- ^ Variables and constants (with their refinement types)
  _symbolsOfShape :: Map SType (Set Id),   -- ^ Variables and constants indexed by their simple type
  _datatypes :: Map Id Datatype,           -- ^ Datatype representations
  _assumptions :: Set Formula,             -- ^ Positive unknown assumptions
  _negAssumptions :: Set Formula           -- ^ Negative unknown assumptions
}

makeLenses ''Environment  

-- | Environment with no symbols or assumptions
emptyEnv = Environment Map.empty Map.empty Map.empty Set.empty Set.empty

-- | 'addSymbol' @sym t env@ : add type binding @sym@ :: @t@ to @env@
addSymbol :: Id -> RType -> Environment -> Environment
addSymbol sym t = (symbols %~ Map.insert sym t) . (symbolsOfShape %~ Map.insertWith (Set.union) (shape t) (Set.singleton sym))

-- | 'addDatatype' @name env@ : add datatype @name@ to the environment
addDatatype :: Id -> Datatype -> Environment -> Environment
addDatatype name dt = over datatypes (Map.insert name dt)

-- | 'varRefinement' @v x@ : refinement of a scalar variable
varRefinement x b = Var b valueVarName |=| Var b x
                  
-- | 'symbolsByShape' @s env@ : symbols of simple type @s@ in @env@ 
symbolsByShape :: SType -> Environment -> Map Id RType
symbolsByShape s env = restrictDomain (Map.findWithDefault Set.empty s (env ^. symbolsOfShape)) (env ^. symbols)

-- | 'allScalars' @env@ : logic terms for all scalar symbols in @env@
allScalars :: Environment -> [Formula]
allScalars env = concatMap (\b -> map (Var b) $ Set.toList $ Map.findWithDefault Set.empty (ScalarT b ()) (env ^. symbolsOfShape)) ([BoolT, IntT] ++ map DatatypeT (Map.keys (env ^. datatypes)))

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
    embedBinding x (ScalarT baseT fml) = Set.singleton $ substitute (Map.singleton valueVarName (Var baseT x)) fml
    embedBinding _ _ = Set.empty
    
-- | One case inside a pattern match expression
data Case s c t = Case {
  constructor :: Id,      -- ^ Constructor name
  argNames :: [Id],       -- ^ Bindings for constructor arguments
  expr :: Program s c t   -- ^ Result of the match in this case
}    
    
-- | Program skeletons parametrized by information stored symbols, conditionals, and by node types
data BareProgram s c t =
  PSymbol s |                               -- ^ Symbol (variable or constant)
  PApp (Program s c t) (Program s c t) |    -- ^ Function application
  PFun Id (Program s c t) |                 -- ^ Lambda abstraction
  PIf c (Program s c t) (Program s c t) |   -- ^ Conditional
  PMatch (Program s c t) [Case s c t] |     -- ^ Pattern match on datatypes
  PFix Id (Program s c t)                   -- ^ Fixpoint
  
-- | Programs annotated with types  
data Program s c t = Program {
  content :: BareProgram s c t,
  typ :: t
}

-- | Fully defined programs 
type SimpleProgram = Program Id Formula RType

-- | For each symbol, a sufficient condition for the symbol to be a solution at a given leaf
type LeafConstraint = Map Id Constraint

-- | Programs where conditions and symbols are represented by constraints with unknowns
type LiquidProgram = Program LeafConstraint Formula RType

-- | Building types
int = ScalarT IntT
int_ = int ()
(|->|) = FunctionT dontCare
intAll = int ftrue
nat = int (valInt |>=| IntLit 0)

infixr 5 |->|
          
-- | Typing constraints
data Constraint = Unconstrained
  | Subtype Environment RType RType
  | WellFormed Environment RType
  | WellFormedCond Environment Formula
  | WellFormedLeaf RType [RType]
  | WellFormedSymbol [[Constraint]]  
  
isWFLeaf (WellFormedLeaf _ _) = True
isWFLeaf _ = False
  