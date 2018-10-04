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
import Control.Lens hiding (set)

{- Type skeletons -}

data BaseType r = BoolT | IntT | DatatypeT Id [TypeSkeleton r] [r] | TypeVarT Substitution Id
  deriving (Show, Eq, Ord)

-- | Type skeletons (parametrized by refinements)
data TypeSkeleton r =
  ScalarT (BaseType r) r |
  FunctionT Id (TypeSkeleton r) (TypeSkeleton r) |
  LetT Id (TypeSkeleton r) (TypeSkeleton r) |
  AnyT
  deriving (Show, Eq, Ord)

contextual x tDef (FunctionT y tArg tRes) = FunctionT y (contextual x tDef tArg) (contextual x tDef tRes)
contextual _ _ AnyT = AnyT
contextual x tDef t = LetT x tDef t

isScalarType (ScalarT _ _) = True
-- isScalarType (LetT _ _ t) = isScalarType t
isScalarType (LetT _ _ _) = True
isScalarType _ = False
baseTypeOf (ScalarT baseT _) = baseT
baseTypeOf (LetT _ _ t) = baseTypeOf t
baseTypeOf _ = error "baseTypeOf: applied to a function type"
isFunctionType (FunctionT _ _ _) = True
-- isFunctionType (LetT _ _ t) = isFunctionType t
isFunctionType _ = False
argType (FunctionT _ t _) = t
resType (FunctionT _ _ t) = t

hasAny AnyT = True
hasAny (ScalarT baseT _) = baseHasAny baseT
  where
    baseHasAny (DatatypeT _ tArgs _) = any hasAny tArgs
    baseHasAny _ = False
hasAny (FunctionT _ tArg tRes) = hasAny tArg || hasAny tRes
hasAny (LetT _ tDef tBody) = hasAny tDef || hasAny tBody

-- | Convention to indicate "any datatype" (for synthesizing match scrtuinees)
anyDatatype = ScalarT (DatatypeT dontCare [] []) ftrue

toSort :: BaseType t -> Sort
toSort BoolT = BoolS
toSort IntT = IntS
toSort (DatatypeT name tArgs _) = DataS name (map (toSort . baseTypeOf) tArgs)
toSort (TypeVarT _ name) = VarS name

fromSort :: Sort -> TypeSkeleton Formula
fromSort = flip refineSort ftrue

refineSort :: Sort -> Formula -> TypeSkeleton Formula
refineSort BoolS f = ScalarT BoolT f
refineSort IntS f = ScalarT IntT f
refineSort (VarS name) f = ScalarT (TypeVarT Map.empty name) f
refineSort (DataS name sArgs) f = ScalarT (DatatypeT name (map fromSort sArgs) []) f
refineSort (SetS s) f = ScalarT dt f
  where
    dt = DatatypeT setTypeName [fromSort s] []
    tvar = ScalarT (TypeVarT Map.empty setTypeVar) f
refineSort AnyS f = AnyT

typeIsData :: TypeSkeleton r -> Bool
typeIsData (ScalarT DatatypeT{} _) = True
typeIsData _ = False

arity :: TypeSkeleton r -> Int
arity (FunctionT _ _ t) = 1 + arity t
arity (LetT _ _ t) = arity t
arity _ = 0

-- TODO: make sure the AnyT case is OK
hasSet :: TypeSkeleton r -> Bool
hasSet (ScalarT (DatatypeT name _ _) _) = name == setTypeName
hasSet (FunctionT _ t1 t2) = hasSet t1 || hasSet t2
hasSet (LetT _ t1 t2) = hasSet t1 || hasSet t2
hasSet _ = False

lastType (FunctionT _ _ tRes) = lastType tRes
lastType (LetT _ _ t) = lastType t
lastType t = t

allArgTypes (FunctionT x tArg tRes) = tArg : (allArgTypes tRes)
allArgTypes (LetT _ _ t) = allArgTypes t
allArgTypes _ = []

allArgs (ScalarT _ _) = []
allArgs (FunctionT x (ScalarT baseT _) tRes) = (Var (toSort baseT) x) : (allArgs tRes)
allArgs (FunctionT x _ tRes) = (allArgs tRes)
allArgs (LetT _ _ t) = allArgs t

-- | Free variables of a type
varsOfType :: RType -> Set Id
varsOfType (ScalarT baseT fml) = varsOfBase baseT `Set.union` (Set.map varName $ varsOf fml)
  where
    varsOfBase (DatatypeT name tArgs pArgs) = Set.unions (map varsOfType tArgs) `Set.union` (Set.map varName $ Set.unions (map varsOf pArgs))
    varsOfBase _ = Set.empty
varsOfType (FunctionT x tArg tRes) = varsOfType tArg `Set.union` (Set.delete x $ varsOfType tRes)
varsOfType (LetT x tDef tBody) = varsOfType tDef `Set.union` (Set.delete x $ varsOfType tBody)
varsOfType AnyT = Set.empty

-- | Free variables of a type
predsOfType :: RType -> Set Id
predsOfType (ScalarT baseT fml) = predsOfBase baseT `Set.union` predsOf fml
  where
    predsOfBase (DatatypeT name tArgs pArgs) = Set.unions (map predsOfType tArgs) `Set.union` (Set.unions (map predsOf pArgs))
    predsOfBase _ = Set.empty
predsOfType (FunctionT x tArg tRes) = predsOfType tArg `Set.union` predsOfType tRes
predsOfType (LetT x tDef tBody) = predsOfType tDef `Set.union` predsOfType tBody
predsOfType AnyT = Set.empty

varRefinement x s = Var s valueVarName |=| Var s x
isVarRefinemnt (Binary Eq (Var _ v) (Var _ _)) = v == valueVarName
isVarRefinemnt _ = False

-- | Polymorphic type skeletons (parametrized by refinements)
data SchemaSkeleton r =
  Monotype (TypeSkeleton r) |
  ForallT Id (SchemaSkeleton r) |       -- Type-polymorphic
  ForallP PredSig (SchemaSkeleton r)    -- Predicate-polymorphic
  deriving (Show, Eq, Ord)

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

vart n = ScalarT (TypeVarT Map.empty n)
vart_ n = vart n ()
vartAll n = vart n ftrue

set n = ScalarT (DatatypeT setTypeName [tvar] [])
  where
    tvar = ScalarT (TypeVarT Map.empty n) ftrue
setAll n = (set n) ftrue

-- | Mapping from type variables to types
type TypeSubstitution = Map Id RType

asSortSubst :: TypeSubstitution -> SortSubstitution
asSortSubst = Map.map (toSort . baseTypeOf)

-- | 'typeSubstitute' @t@ : substitute all free type variables in @t@
typeSubstitute :: TypeSubstitution -> RType -> RType
typeSubstitute subst (ScalarT baseT r) = addRefinement substituteBase (sortSubstituteFml (asSortSubst subst) r)
  where
    substituteBase = case baseT of
      TypeVarT varSubst a -> case Map.lookup a subst of
        Just t -> substituteInType (not . (`Map.member` subst)) varSubst $ typeSubstitute subst t
        Nothing -> ScalarT (TypeVarT varSubst a) ftrue
      DatatypeT name tArgs pArgs ->
        let
          tArgs' = map (typeSubstitute subst) tArgs
          pArgs' = map (sortSubstituteFml (asSortSubst subst)) pArgs
        in ScalarT (DatatypeT name tArgs' pArgs') ftrue
      _ -> ScalarT baseT ftrue
typeSubstitute subst (FunctionT x tArg tRes) = FunctionT x (typeSubstitute subst tArg) (typeSubstitute subst tRes)
typeSubstitute subst (LetT x tDef tBody) = LetT x (typeSubstitute subst tDef) (typeSubstitute subst tBody)
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
    LetT x tDef tBody -> FunctionT x (tsp tDef) (tsp tBody)
    AnyT -> AnyT

-- | 'typeVarsOf' @t@ : all type variables in @t@
typeVarsOf :: TypeSkeleton r -> Set Id
typeVarsOf t@(ScalarT baseT r) = case baseT of
  TypeVarT _ name -> Set.singleton name
  DatatypeT _ tArgs _ -> Set.unions (map typeVarsOf tArgs)
  _ -> Set.empty
typeVarsOf (FunctionT _ tArg tRes) = typeVarsOf tArg `Set.union` typeVarsOf tRes
typeVarsOf (LetT _ tDef tBody) = typeVarsOf tDef `Set.union` typeVarsOf tBody
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
shape (ScalarT (TypeVarT _ a) _) = ScalarT (TypeVarT Map.empty a) ()
shape (FunctionT x tArg tFun) = FunctionT x (shape tArg) (shape tFun)
shape (LetT _ _ t) = shape t
shape AnyT = AnyT

-- | Conjoin refinement to a type
addRefinement :: TypeSkeleton Formula -> Formula -> TypeSkeleton Formula
addRefinement (ScalarT base fml) fml' = if isVarRefinemnt fml'
  then ScalarT base fml' -- the type of a polymorphic variable does not require any other refinements
  else ScalarT base (fml `andClean` fml')
addRefinement (LetT x tDef tBody) fml = LetT x tDef (addRefinement tBody fml)
addRefinement t (BoolLit True) = t
addRefinement AnyT _ = AnyT
addRefinement t _ = error $ "addRefinement: applied to function type"

-- | Conjoin refinement to the return type
addRefinementToLast t@(ScalarT _ _) fml = addRefinement t fml
addRefinementToLast (FunctionT x tArg tRes) fml = FunctionT x tArg (addRefinementToLast tRes fml)
addRefinementToLast (LetT x tDef tBody) fml = LetT x tDef (addRefinementToLast tBody fml)

-- | Conjoin refinement to the return type inside a schema
addRefinementToLastSch (Monotype t) fml = Monotype $ addRefinementToLast t fml
addRefinementToLastSch (ForallT a sch) fml = ForallT a $ addRefinementToLastSch sch fml
addRefinementToLastSch (ForallP sig sch) fml = ForallP sig $ addRefinementToLastSch sch fml

-- | Apply variable substitution in all formulas inside a type
substituteInType :: (Id -> Bool) -> Substitution -> RType -> RType
substituteInType isBound subst (ScalarT baseT fml) = ScalarT (substituteBase baseT) (substitute subst fml)
  where
    substituteBase (TypeVarT oldSubst a) = TypeVarT oldSubst a
      -- Looks like pending substitutions on types are not actually needed, since renamed variables are always out of scope
       -- if isBound a
          -- then TypeVarT oldSubst a
          -- else TypeVarT (oldSubst `composeSubstitutions` subst) a
    substituteBase (DatatypeT name tArgs pArgs) = DatatypeT name (map (substituteInType isBound subst) tArgs) (map (substitute subst) pArgs)
    substituteBase baseT = baseT
substituteInType isBound subst (FunctionT x tArg tRes) =
  if Map.member x subst
    then error $ unwords ["Attempt to substitute variable", x, "bound in a function type"]
    else FunctionT x (substituteInType isBound subst tArg) (substituteInType isBound subst tRes)
substituteInType isBound subst (LetT x tDef tBody) =
  if Map.member x subst
    then error $ unwords ["Attempt to substitute variable", x, "bound in a contextual type"]
    else LetT x (substituteInType isBound subst tDef) (substituteInType isBound subst tBody)
substituteInType isBound subst AnyT = AnyT

-- | 'renameVar' @old new t typ@: rename all occurrences of @old@ in @typ@ into @new@ of type @t@
renameVar :: (Id -> Bool) -> Id -> Id -> RType -> RType -> RType
renameVar isBound old new (ScalarT b _)     t = substituteInType isBound (Map.singleton old (Var (toSort b) new)) t
renameVar isBound old new (LetT _ _ tBody)  t = renameVar isBound old new tBody t
renameVar _ _ _ _                           t = t -- function arguments cannot occur in types (and AnyT is assumed to be function)

-- | Intersection of two types (assuming the types were already checked for consistency)
intersection _ t AnyT = t
intersection _ AnyT t = t
intersection isBound (ScalarT baseT fml) (ScalarT baseT' fml') = case baseT of
  DatatypeT name tArgs pArgs -> let DatatypeT _ tArgs' pArgs' = baseT' in
                                  ScalarT (DatatypeT name (zipWith (intersection isBound) tArgs tArgs') (zipWith andClean pArgs pArgs')) (fml `andClean` fml')
  _ -> ScalarT baseT (fml `andClean` fml')
intersection isBound (FunctionT x tArg tRes) (FunctionT y tArg' tRes') = FunctionT x tArg (intersection isBound tRes (renameVar isBound y x tArg tRes'))

-- | Instantiate unknowns in a type
typeApplySolution :: Solution -> RType -> RType
typeApplySolution sol (ScalarT (DatatypeT name tArgs pArgs) fml) = ScalarT (DatatypeT name (map (typeApplySolution sol) tArgs) (map (applySolution sol) pArgs)) (applySolution sol fml)
typeApplySolution sol (ScalarT base fml) = ScalarT base (applySolution sol fml)
typeApplySolution sol (FunctionT x tArg tRes) = FunctionT x (typeApplySolution sol tArg) (typeApplySolution sol tRes)
typeApplySolution sol (LetT x tDef tBody) = LetT x (typeApplySolution sol tDef) (typeApplySolution sol tBody)
typeApplySolution _ AnyT = AnyT

typeFromSchema :: RSchema -> RType
typeFromSchema (Monotype t) = t
typeFromSchema (ForallT _ t) = typeFromSchema t
typeFromSchema (ForallP _ t) = typeFromSchema t 

allRefinementsOf :: RSchema -> [Formula]
allRefinementsOf sch = allRefinementsOf' $ typeFromSchema sch

allRefinementsOf' (ScalarT _ ref) = [ref]
allRefinementsOf' (FunctionT _ argT resT) = allRefinementsOf' argT ++ allRefinementsOf' resT
allRefinementsOf' _ = error "allRefinementsOf called on contextual or any type"

-- Set strings: used for "fake" set type for typechecking measures
emptySetCtor = "Emptyset"
singletonCtor = "Singleton"
insertSetCtor = "Insert"
setTypeName = "DSet"
setTypeVar = "setTypeVar"
setConstructors = [emptySetCtor, singletonCtor, insertSetCtor]