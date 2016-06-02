-- | Refinement Types
module Synquid.Type where

import Synquid.Logic
import Synquid.Tokens
import Synquid.Util

import Data.Maybe
import Data.Either
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
import Control.Lens

{- Type skeletons -}

data BaseType r = BoolT | IntT | DatatypeT Id [TypeSkeleton r] [r] | TypeVarT Id
  deriving (Eq, Ord)
  
-- | Type skeletons (parametrized by refinements)
data TypeSkeleton r =
  ScalarT (BaseType r) r |
  FunctionT Id (TypeSkeleton r) (TypeSkeleton r) |
  AnyT
  deriving (Eq, Ord)

isScalarType (ScalarT _ _) = True
isScalarType _ = False
baseTypeOf (ScalarT baseT _) = baseT
baseTypeOf _ = error "baseTypeOf: applied to a function type"
isFunctionType (FunctionT _ _ _) = True
isFunctionType _ = False
argType (FunctionT _ t _) = t
resType (FunctionT _ _ t) = t

toSort BoolT = BoolS
toSort IntT = IntS
toSort (DatatypeT name tArgs _) = DataS name (map (toSort . baseTypeOf) tArgs)
toSort (TypeVarT name) = VarS name

fromSort BoolS = ScalarT BoolT ftrue
fromSort IntS = ScalarT IntT ftrue
fromSort (VarS name) = ScalarT (TypeVarT name) ftrue
fromSort (DataS name sArgs) = ScalarT (DatatypeT name (map fromSort sArgs) []) ftrue -- TODO: what to do with pArgs?
fromSort AnyS = AnyT

arity :: TypeSkeleton r -> Int
arity (FunctionT _ _ t) = 1 + arity t
arity _ = 0

lastType (FunctionT _ _ tRes) = lastType tRes
lastType t = t

allArgTypes (FunctionT x tArg tRes) = tArg : (allArgTypes tRes)
allArgTypes _ = []

allArgs (ScalarT _ _) = []
allArgs (FunctionT x (ScalarT baseT _) tRes) = (Var (toSort baseT) x) : (allArgs tRes)
allArgs (FunctionT x _ tRes) = (allArgs tRes)

-- | Free variables of a type
varsOfType :: RType -> Set Id
varsOfType (ScalarT baseT fml) = varsOfBase baseT `Set.union` (Set.map varName $ varsOf fml)
  where
    varsOfBase (DatatypeT name tArgs pArgs) = Set.unions (map varsOfType tArgs) `Set.union` (Set.map varName $ Set.unions (map varsOf pArgs))
    varsOfBase _ = Set.empty
varsOfType (FunctionT x tArg tRes) = varsOfType tArg `Set.union` (Set.delete x $ varsOfType tRes)
varsOfType AnyT = Set.empty    
  
varRefinement x s = Var s valueVarName |=| Var s x
isVarRefinemnt (Binary Eq (Var _ v) (Var _ _)) = v == valueVarName
isVarRefinemnt _ = False

-- | Polymorphic type skeletons (parametrized by refinements)
data SchemaSkeleton r = 
  Monotype (TypeSkeleton r) |
  ForallT Id (SchemaSkeleton r) |       -- Type-polymorphic
  ForallP PredSig (SchemaSkeleton r)    -- Predicate-polymorphic
  deriving (Eq, Ord)
  
toMonotype :: SchemaSkeleton r -> TypeSkeleton r
toMonotype (Monotype t) = t
toMonotype (ForallT _ t) = toMonotype t
toMonotype (ForallP _ t) = toMonotype t

boundVarsOf :: SchemaSkeleton r -> [Id]
boundVarsOf (ForallT a sch) = a : boundVarsOf sch
boundVarsOf _ = []

-- | Building types
bool = ScalarT BoolT  
bool_ = bool ()
boolAll = bool ftrue

int = ScalarT IntT
int_ = int ()
intAll = int ftrue
nat = int (valInt |>=| IntLit 0)
pos = int (valInt |>| IntLit 0)

vart n = ScalarT (TypeVarT n)
vart_ n = vart n ()
vartAll n = vart n ftrue
  
-- | Mapping from type variables to types
type TypeSubstitution = Map Id RType

asSortSubst :: TypeSubstitution -> SortSubstitution
asSortSubst = Map.map (toSort . baseTypeOf)

-- | 'typeSubstitute' @t@ : substitute all free type variables in @t@
typeSubstitute :: TypeSubstitution -> RType -> RType
typeSubstitute subst (ScalarT baseT r) = addRefinement substituteBase (sortSubstituteFml (asSortSubst subst) r)
  where
    substituteBase = case baseT of
      TypeVarT a -> case Map.lookup a subst of
        Just t -> typeSubstitute subst t
        Nothing -> ScalarT (TypeVarT a) ftrue
      DatatypeT name tArgs pArgs -> 
        let 
          tArgs' = map (typeSubstitute subst) tArgs 
          pArgs' = map (sortSubstituteFml (asSortSubst subst)) pArgs
        in ScalarT (DatatypeT name tArgs' pArgs') ftrue
      _ -> ScalarT baseT ftrue
typeSubstitute subst (FunctionT x tArg tRes) = FunctionT x (typeSubstitute subst tArg) (typeSubstitute subst tRes)
typeSubstitute _ AnyT = AnyT

noncaptureTypeSubst :: [Id] -> [RType] -> RType -> RType  
noncaptureTypeSubst tVars tArgs t =
  let tFresh = typeSubstitute (Map.fromList $ zip tVars (map vartAll distinctTypeVars)) t
  in typeSubstitute (Map.fromList $ zip distinctTypeVars tArgs) tFresh  

schemaSubstitute :: TypeSubstitution -> RSchema -> RSchema
schemaSubstitute tass (Monotype t) = Monotype $ typeSubstitute tass t
schemaSubstitute tass (ForallT a sch) = ForallT a $ schemaSubstitute (Map.delete a tass) sch
schemaSubstitute tass (ForallP sig sch) = ForallP sig $ schemaSubstitute tass sch

typeSubstitutePred :: Substitution -> RType -> RType
typeSubstitutePred pSubst t = let tsp = typeSubstitutePred pSubst
  in case t of
    ScalarT (DatatypeT name tArgs pArgs) fml -> ScalarT (DatatypeT name (map tsp tArgs) (map (substitutePredicate pSubst) pArgs)) (substitutePredicate pSubst fml)
    ScalarT baseT fml -> ScalarT baseT (substitutePredicate pSubst fml)
    FunctionT x tArg tRes -> FunctionT x (tsp tArg) (tsp tRes)
    AnyT -> AnyT
  
-- | 'typeVarsOf' @t@ : all type variables in @t@
typeVarsOf :: TypeSkeleton r -> Set Id
typeVarsOf t@(ScalarT baseT r) = case baseT of
  TypeVarT name -> Set.singleton name  
  DatatypeT _ tArgs _ -> Set.unions (map typeVarsOf tArgs)
  _ -> Set.empty
typeVarsOf (FunctionT _ tArg tRes) = typeVarsOf tArg `Set.union` typeVarsOf tRes
typeVarsOf _ = Set.empty

{- Refinement types -}

-- | Unrefined typed
type SType = TypeSkeleton ()

-- | Refined types  
type RType = TypeSkeleton Formula

-- | Unrefined schemas
type SSchema = SchemaSkeleton ()

-- | Refined schemas  
type RSchema = SchemaSkeleton Formula

-- | Forget refinements of a type
shape :: RType -> SType  
shape (ScalarT (DatatypeT name tArgs pArgs) _) = ScalarT (DatatypeT name (map shape tArgs) (replicate (length pArgs) ())) ()
shape (ScalarT IntT _) = ScalarT IntT ()
shape (ScalarT BoolT _) = ScalarT BoolT ()
shape (ScalarT (TypeVarT a) _) = ScalarT (TypeVarT a) ()
shape (FunctionT x tArg tFun) = FunctionT x (shape tArg) (shape tFun)
shape AnyT = AnyT

-- | Insert weakest refinement
refineTop :: SType -> RType
refineTop (ScalarT (DatatypeT name tArgs pArgs) _) = ScalarT (DatatypeT name (map refineTop tArgs) (replicate (length pArgs) ftrue)) ftrue
refineTop (ScalarT IntT _) = ScalarT IntT ftrue
refineTop (ScalarT BoolT _) = ScalarT BoolT ftrue
refineTop (ScalarT (TypeVarT a) _) = ScalarT (TypeVarT a) ftrue
refineTop (FunctionT x tArg tFun) = FunctionT x (refineBot tArg) (refineTop tFun)

-- | Insert strongest refinement
refineBot :: SType -> RType
refineBot (ScalarT (DatatypeT name tArgs pArgs) _) = ScalarT (DatatypeT name (map refineBot tArgs) (replicate (length pArgs) ffalse)) ffalse
refineBot (ScalarT IntT _) = ScalarT IntT ffalse
refineBot (ScalarT BoolT _) = ScalarT BoolT ffalse
refineBot (ScalarT (TypeVarT a) _) = ScalarT (TypeVarT a) ffalse
refineBot (FunctionT x tArg tFun) = FunctionT x (refineTop tArg) (refineBot tFun)

-- | Conjoin refinement to a type
addRefinement (ScalarT base fml) fml' = if isVarRefinemnt fml'
  then ScalarT base fml' -- the type of a polymorphic variable does not require any other refinements
  else ScalarT base (fml `andClean` fml')
addRefinement t (BoolLit True) = t
addRefinement AnyT _ = AnyT
addRefinement t _ = error $ "addRefinement: applied to function type"

-- | Conjoin refinement to the return type
addRefinementToLast t@(ScalarT _ _) fml = addRefinement t fml
addRefinementToLast (FunctionT x tArg tRes) fml = FunctionT x tArg (addRefinementToLast tRes fml)

-- | Conjoin refinement to the return type inside a schema
addRefinementToLastSch (Monotype t) fml = Monotype $ addRefinementToLast t fml
addRefinementToLastSch (ForallT a sch) fml = ForallT a $ addRefinementToLastSch sch fml
addRefinementToLastSch (ForallP sig sch) fml = ForallP sig $ addRefinementToLastSch sch fml

-- | Apply variable substitution in all formulas inside a type
substituteInType :: Substitution -> RType -> RType
substituteInType subst (ScalarT baseT fml) = case baseT of
  DatatypeT name tArgs pArgs -> ScalarT (DatatypeT name (map (substituteInType subst) tArgs) (map (substitute subst) pArgs)) (substitute subst fml)
  _ -> ScalarT baseT (substitute subst fml)
substituteInType subst (FunctionT x tArg tRes) = FunctionT x (substituteInType subst tArg) (substituteInType subst tRes)
substituteInType subst AnyT = AnyT
      
-- | 'renameVar' @old new t typ@: rename all occurrences of @old@ in @typ@ into @new@ of type @t@
renameVar :: Id -> Id -> RType -> RType -> RType
renameVar old new (ScalarT b _)       t = substituteInType (Map.singleton old (Var (toSort b) new)) t
renameVar old new _                   t = t -- function arguments cannot occur in types (and AnyT is assumed to be function)
    
-- | Intersection of two types (assuming the types were already checked for consistency)
intersection t AnyT = t
intersection AnyT t = t
intersection (ScalarT baseT fml) (ScalarT baseT' fml') = case baseT of
  DatatypeT name tArgs pArgs -> let DatatypeT _ tArgs' pArgs' = baseT' in
                                  ScalarT (DatatypeT name (zipWith intersection tArgs tArgs') (zipWith andClean pArgs pArgs')) (fml `andClean` fml')
  _ -> ScalarT baseT (fml `andClean` fml')
intersection (FunctionT x tArg tRes) (FunctionT y tArg' tRes') = FunctionT x tArg (intersection tRes (renameVar y x tArg tRes')) 

-- | Instantiate unknowns in a type
typeApplySolution :: Solution -> RType -> RType
typeApplySolution sol (ScalarT (DatatypeT name tArgs pArgs) fml) = ScalarT (DatatypeT name (map (typeApplySolution sol) tArgs) (map (applySolution sol) pArgs)) (applySolution sol fml)
typeApplySolution sol (ScalarT base fml) = ScalarT base (applySolution sol fml)
typeApplySolution sol (FunctionT x tArg tRes) = FunctionT x (typeApplySolution sol tArg) (typeApplySolution sol tRes) 
typeApplySolution _ AnyT = AnyT
