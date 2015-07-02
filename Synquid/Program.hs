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

{- Type skeletons -}
  
-- | Type skeletons parametrized by refinements  
data TypeSkeleton r =
  ScalarT BaseType r |
  FunctionT Id (TypeSkeleton r) (TypeSkeleton r)  
  deriving (Eq, Ord)
  
isFunctionType (FunctionT _ _ _) = True
isFunctionType _ = False
argType (FunctionT _ t _) = t
resType (FunctionT _ _ t) = t

arity (FunctionT _ _ t) = arity t + 1
arity _ = 0

data SchemaSkeleton r = 
  Monotype (TypeSkeleton r) |
  Forall Id (SchemaSkeleton r)
  
toMonotype :: SchemaSkeleton r -> TypeSkeleton r
toMonotype (Monotype t) = t
toMonotype (Forall _ t) = toMonotype t
  
-- | Mapping from type variables to types
type TypeSubstitution r = Map Id (TypeSkeleton r)

-- | 'typeSubstitute' @combineR subst t@ : substitute all free type variables in @t@ combining refinements using @combineR@
typeSubstitute :: (r -> r -> r) -> TypeSubstitution r -> TypeSkeleton r -> TypeSkeleton r
typeSubstitute combineR subst t@(ScalarT baseT r) = case baseT of
  TypeVarT name -> case Map.lookup name subst of
    Just (ScalarT baseT' r') -> ScalarT baseT' (combineR r r')
    Just t' -> t' -- TODO: how to combine refinements?
    Nothing -> t
  _ -> t -- TODO: datatype
typeSubstitute combineR subst (FunctionT x tArg tRes) = FunctionT x (typeSubstitute combineR subst tArg) (typeSubstitute combineR subst tRes)

-- | 'renameTypeVar' @old new t@ : rename type variable @old@ into @new@ in @t@
renameTypeVar old new t@(ScalarT (TypeVarT name) r)
  | name == old   = ScalarT (TypeVarT new) r
  | otherwise     = t
renameTypeVar old new t@(ScalarT _ _) = t
renameTypeVar old new (FunctionT x tArg tRes) = FunctionT x (renameTypeVar old new tArg) (renameTypeVar old new tRes)

-- | 'schemaRenameTypeVar' @old new sch@ : rename type variable @old@ into @new@ in @sch@
schemaRenameTypeVar old new (Monotype t) = Monotype $ renameTypeVar old new t
schemaRenameTypeVar old new (Forall a sch) = Forall a $ schemaRenameTypeVar old new sch

-- | 'typeVarsOf' @t@ : all type variables in @t@
typeVarsOf :: TypeSkeleton r -> Set Id
typeVarsOf t@(ScalarT baseT r) = case baseT of
  TypeVarT name -> Set.singleton name
  _ -> Set.empty
typeVarsOf (FunctionT _ tArg tRes) = typeVarsOf tArg `Set.union` typeVarsOf tRes

{- Refinement types -}

-- | Unrefined typed
type SType = TypeSkeleton ()

-- | Refinement types  
type RType = TypeSkeleton Formula

-- | Unrefined schemas
type SSchema = SchemaSkeleton ()

-- | Refinement schemas  
type RSchema = SchemaSkeleton Formula

-- | Forget refinements of a type
shape :: RType -> SType  
shape (ScalarT base _) = ScalarT base ()
shape (FunctionT _ tArg tFun) = FunctionT dontCare (shape tArg) (shape tFun)

-- | Forget refinements of a schema
polyShape :: RSchema -> SSchema
polyShape (Monotype t) = Monotype (shape t)
polyShape (Forall a sch) = Forall a (polyShape sch)

-- | Insert trivial refinements
refine :: SType -> RType
refine (ScalarT base _) = ScalarT base ftrue
refine (FunctionT x tArg tFun) = FunctionT x (refine tArg) (refine tFun)
      
-- | 'renameVar' @old new t@: rename all occurrences of @old@ in @t@ into @new@
renameVar :: Id -> Id -> RType -> RType -> RType
renameVar old new (FunctionT _ _ _)   t = t -- function arguments cannot occur in types
renameVar old new (ScalarT b _)  (ScalarT base fml) = ScalarT base (substitute (Map.singleton old (Var b new)) fml)
renameVar old new t              (FunctionT x tArg tRes) = FunctionT x (renameVar old new t tArg) (renameVar old new t tRes)

-- | Instantiate unknowns in a type
typeApplySolution sol (ScalarT base fml) = ScalarT base (applySolution sol fml)
typeApplySolution sol (FunctionT x tArg tRes) = FunctionT x (typeApplySolution sol tArg) (typeApplySolution sol tRes) 

-- | User-defined datatype representation
data Datatype = Datatype {
  _constructors :: [Id],                    -- ^ Constructor names
  _wfMetric :: Maybe (Formula -> Formula)   -- ^ Given a datatype term, returns an integer term that can serve as a well-founded metric for recursion
}

makeLenses ''Datatype

{- Evaluation environment -}

-- | Typing environment
data Environment = Environment {
  _symbols :: Map Id RSchema,                -- ^ Variables and constants (with their refinement types)
  _boundTypeVars :: [Id],
  -- _instantiations :: TypeSubstitution Formula,
  _datatypes :: Map Id Datatype,           -- ^ Datatype representations
  _assumptions :: Set Formula,             -- ^ Positive unknown assumptions
  _negAssumptions :: Set Formula           -- ^ Negative unknown assumptions
}

makeLenses ''Environment  

-- | Environment with no symbols or assumptions
emptyEnv = Environment Map.empty [] Map.empty Set.empty Set.empty

-- | 'addSymbol' @sym t env@ : add type binding @sym@ :: Monotype @t@ to @env@
addSymbol :: Id -> RType -> Environment -> Environment
addSymbol sym t = symbols %~ Map.insert sym (Monotype t)

-- | 'addPolySymbol' @sym sch env@ : add type binding @sym@ :: @sch@ to @env@
addPolySymbol :: Id -> RSchema -> Environment -> Environment
addPolySymbol sym sch = symbols %~ Map.insert sym sch

-- | 'addDatatype' @name env@ : add datatype @name@ to the environment
addDatatype :: Id -> Datatype -> Environment -> Environment
addDatatype name dt = over datatypes (Map.insert name dt)

-- | 'addTypeVar' @a@ : Add bound type variable @a@ to the environment
addTypeVar :: Id -> Environment -> Environment
addTypeVar a = over boundTypeVars (a :)

-- | 'varRefinement' @v x@ : refinement of a scalar variable
varRefinement x b = Var b valueVarName |=| Var b x

-- | 'allScalars' @env@ : logic terms for all scalar symbols in @env@
allScalars :: Environment -> [Formula]
allScalars env = map (uncurry $ flip Var) $ Map.toList $ Map.mapMaybe baseType (env ^. symbols)
  where
    baseType (Forall _ _) = Nothing -- TODO: what to do with polymorphic scalars like Nil?
    baseType (Monotype (ScalarT b _)) = Just b
    baseType (Monotype (FunctionT _ _ _)) = Nothing

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
    embedBinding _ (Monotype (ScalarT _ (BoolLit True))) = Set.empty -- Ignore trivial types
    embedBinding x (Monotype (ScalarT baseT fml)) = Set.singleton $ substitute (Map.singleton valueVarName (Var baseT x)) fml
    embedBinding _ _ = Set.empty
    
{- Program terms -}    
    
-- | One case inside a pattern match expression
data Case s c t = Case {
  constructor :: Id,      -- ^ Constructor name
  argNames :: [Id],       -- ^ Bindings for constructor arguments
  expr :: Program s c t   -- ^ Result of the match in this case
}    
    
-- | Program skeletons parametrized by information stored symbols, conditionals, and by node types
data BareProgram s c t =
  PSymbol s (TypeSubstitution t) |          -- ^ Symbol (variable or constant)
  PApp (Program s c t) (Program s c t) |    -- ^ Function application
  PFun Id (Program s c t) |                 -- ^ Lambda abstraction
  PIf c (Program s c t) (Program s c t) |   -- ^ Conditional
  PMatch (Program s c t) [Case s c t] |     -- ^ Pattern match on datatypes
  PFix Id (Program s c t)                   -- ^ Fixpoint  
  
-- | Programs annotated with types  
data Program s c t = Program {
  content :: BareProgram s c t,
  typ :: TypeSkeleton t
}

-- | Fully defined programs 
type SimpleProgram = Program Id Formula Formula

-- | For each symbol, a sufficient condition for the symbol to be a solution at a given leaf
type LeafConstraint = Map Id Constraint

-- | Programs where conditions and symbols are represented by constraints with unknowns
type LiquidProgram = Program LeafConstraint Formula Formula

-- | Building types
int = ScalarT IntT
int_ = int ()
(|->|) = FunctionT dontCare
intAll = int ftrue
nat = int (valInt |>=| IntLit 0)

infixr 5 |->|

-- | 'instantiateSymbols' @subst p@ : apply @subst@ to polymorphic symbols
instantiateSymbols :: TypeSubstitution Formula -> LiquidProgram -> LiquidProgram
instantiateSymbols subst (Program body t) = (flip Program (typeSubstitute andClean subst t)) $ case body of
  PSymbol s subst' -> PSymbol s (Map.union subst' $ restrictDomain (typeVarsOf t) subst)
  PApp f arg -> PApp (instantiateSymbols subst f) (instantiateSymbols subst arg)
  PFun x body -> PFun x (instantiateSymbols subst body)
  PIf c t e -> PIf c (instantiateSymbols subst t) (instantiateSymbols subst e)
  PMatch scr cases -> PMatch (instantiateSymbols subst scr) (map instantiateCase cases)
  PFix f body -> PFix f (instantiateSymbols subst body)
  where
    instantiateCase (Case cons args e) = Case cons args (instantiateSymbols subst e)  

{- Typing constraints -}
          
-- | Typing constraints
data Constraint = Unconstrained
  | Subtype Environment RType RType
  | WellFormed Environment RType
  | WellFormedCond Environment Formula
  | WellFormedLeaf RType [RType]
  | WellFormedSymbol [[Constraint]]  
  
isWFLeaf (WellFormedLeaf _ _) = True
isWFLeaf _ = False
  