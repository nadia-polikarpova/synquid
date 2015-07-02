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

data SchemaSkeleton r = 
  Monotype (TypeSkeleton r) |
  Forall Id (SchemaSkeleton r)
  
-- isMonotype (Monotype _) = True
-- isMonotype (_) = False
toMonotype :: SchemaSkeleton r -> TypeSkeleton r
toMonotype (Monotype t) = t
toMonotype (Forall _ t) = toMonotype t
  
-- | Mapping from type variables to types
type TypeSubstitution r = Map Id (TypeSkeleton r)

-- | 'typeSubstitute' @subst t@ : substitute all free type variables in @t@
typeSubstitute :: TypeSubstitution r -> TypeSkeleton r -> TypeSkeleton r
typeSubstitute subst t@(ScalarT baseT r) = case baseT of
  TypeVarT name -> case Map.lookup name subst of
    Just t' -> t'
    Nothing -> t
  _ -> t -- TODO: datatype
typeSubstitute subst (FunctionT x tArg tRes) = FunctionT x (typeSubstitute subst tArg) (typeSubstitute subst tRes)

schemaSubstitute :: TypeSubstitution r -> SchemaSkeleton r -> SchemaSkeleton r
schemaSubstitute subst (Monotype t) = Monotype $ typeSubstitute subst t
schemaSubstitute subst (Forall a sch) = Forall a (schemaSubstitute (Map.delete a subst) sch)
  
typeVarsOf :: TypeSkeleton r -> Set Id
typeVarsOf t@(ScalarT baseT r) = case baseT of
  TypeVarT name -> Set.singleton name
  _ -> Set.empty
typeVarsOf (FunctionT _ tArg tRes) = typeVarsOf tArg `Set.union` typeVarsOf tRes

-- | Assumptions: FV(lhs) and FV(rhs) are disjoint, lhs does not contain forall types
unifier :: [Id] -> TypeSkeleton r -> SchemaSkeleton r -> Maybe (TypeSubstitution r)
-- unifier bvs lhs@(ScalarT (TypeVarT name) _) rhs
  -- | not $ name `elem` bvs = if Set.member name (typeVarsOf rhs) 
      -- then error $ unwords ["unifier: free type variable occurs on both sides", name] 
      -- else Just $ Map.singleton name rhs   -- Free type variable on the left
unifier bvs lhs (Monotype (ScalarT (TypeVarT name) _))
  | not $ name `elem` bvs = if Set.member name (typeVarsOf lhs) 
      then error $ unwords ["unifier: free type variable occurs on both sides", name] 
      else Just $ Map.singleton name lhs   -- Free type variable on the right
unifier _ lhs@(ScalarT baseL _) rhs@(Monotype (ScalarT baseR _))
  | baseL == baseR = Just Map.empty                           -- TODO: polymorphic datatypes
unifier bvs (FunctionT _ argL resL) (Monotype (FunctionT _ argR resR)) = do
  uL <- unifier bvs argL (Monotype argR)
  uR <- unifier bvs (typeSubstitute uL resL) (Monotype $ typeSubstitute uL resR)
  return $ Map.union uL uR
unifier bvs lhs (Forall a sch) = if a `elem` bvs
  then error $ unwords ["unifier: bound type variable of rhs already bound in the context", a] 
  else unifier bvs lhs sch
unifier _ _ _ = Nothing  

{- Refinement types -}

-- | Unrefined typed
type SType = TypeSkeleton ()

-- | Refinement types  
type RType = TypeSkeleton Formula

-- | Unrefined schemas
type SSchema = SchemaSkeleton ()

-- | Refinement schemas  
type RSchema = SchemaSkeleton Formula

-- | Forget refinements
shape :: RType -> SType  
shape (ScalarT base _) = ScalarT base ()
shape (FunctionT _ tArg tFun) = FunctionT dontCare (shape tArg) (shape tFun)

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
  _datatypes :: Map Id Datatype,           -- ^ Datatype representations
  _assumptions :: Set Formula,             -- ^ Positive unknown assumptions
  _negAssumptions :: Set Formula           -- ^ Negative unknown assumptions
}

makeLenses ''Environment  

-- | Environment with no symbols or assumptions
emptyEnv = Environment Map.empty [] Map.empty Set.empty Set.empty

-- | 'addSymbol' @sym t env@ : add type binding @sym@ :: @t@ to @env@
addSymbol :: Id -> RType -> Environment -> Environment
addSymbol sym t = symbols %~ Map.insert sym (Monotype t)

addPolySymbol :: Id -> RSchema -> Environment -> Environment
addPolySymbol sym sch = symbols %~ Map.insert sym sch

-- | 'addDatatype' @name env@ : add datatype @name@ to the environment
addDatatype :: Id -> Datatype -> Environment -> Environment
addDatatype name dt = over datatypes (Map.insert name dt)

addTypeVar :: Id -> Environment -> Environment
addTypeVar a = over boundTypeVars (a :)

-- | 'varRefinement' @v x@ : refinement of a scalar variable
varRefinement x b = Var b valueVarName |=| Var b x
                  
-- | 'symbolsByShape' @s env@ : symbols of simple type @s@ in @env@ 
symbolsByShape :: SType -> Environment -> Map Id (TypeSubstitution (), RSchema)
symbolsByShape s env = Map.map (over _1 fromJust) $ Map.filter (isJust . fst) $ Map.map unify (env ^. symbols)
  where
    unify sch = (unifier (env ^. boundTypeVars) s (polyShape sch), sch)

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
  