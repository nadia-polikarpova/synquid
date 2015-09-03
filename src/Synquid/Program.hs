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
  ScalarT BaseType [TypeSkeleton r] r |
  FunctionT Id (TypeSkeleton r) (TypeSkeleton r)  
  deriving (Eq, Ord)
  
isFunctionType (FunctionT _ _ _) = True
isFunctionType _ = False
argType (FunctionT _ t _) = t
resType (FunctionT _ _ t) = t
typeArgs (ScalarT _ tArgs _) = tArgs

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
typeSubstitute :: (r -> r) -> (r -> r -> r) -> TypeSubstitution r -> TypeSkeleton r -> TypeSkeleton r
typeSubstitute updateR combineR subst t@(ScalarT baseT tArgs r) = let rUp = updateR r in case baseT of
  TypeVarT name -> case Map.lookup name subst of
    Just (ScalarT baseT' tArgs' r') -> ScalarT baseT' tArgs' (combineR rUp r')
    Just t' -> error $ unwords ["typeSubstitute: cannot substitute function type for", name] -- t' -- Function types can't have refinements
    Nothing -> ScalarT baseT tArgs rUp
  DatatypeT name -> let tArgs' = map (typeSubstitute updateR combineR subst) tArgs in ScalarT baseT tArgs' rUp
  _ -> ScalarT baseT tArgs rUp
typeSubstitute updateR combineR subst (FunctionT x tArg tRes) = FunctionT x (typeSubstitute updateR combineR subst tArg) (typeSubstitute updateR combineR subst tRes)

rTypeSubstitute subst = typeSubstitute (typeSubstituteFML subst) andClean subst

schemaSubstitute updateR combineR subst (Monotype t) = Monotype $ typeSubstitute updateR combineR subst t
schemaSubstitute updateR combineR subst (Forall a sch) = Forall a $ schemaSubstitute updateR combineR subst sch

rSchemaSubstitute subst = schemaSubstitute (typeSubstituteFML subst) andClean subst

typeSubstituteFML :: TypeSubstitution r -> Formula -> Formula
typeSubstituteFML subst fml = case fml of 
  SetLit b es -> SetLit (substBaseType b) (map (typeSubstituteFML subst) es)
  Var b name -> Var (substBaseType b) name
  -- Unknown s name -> WHAT TO DO?
  Unary op e -> Unary op (typeSubstituteFML subst e)
  Binary op l r -> Binary op (typeSubstituteFML subst l) (typeSubstituteFML subst r)
  Measure b name e -> Measure (substBaseType b) name (typeSubstituteFML subst e)
  _ -> fml
  where
    substBaseType b@(TypeVarT name) = case Map.lookup name subst of
      Just (ScalarT b' _ _) -> b'
      Just _ -> error $ unwords ["typeSubstituteFML: cannot substitute function type for", name]
      Nothing -> b
    substBaseType (SetT b) = SetT (substBaseType b)
    substBaseType b = b

-- | 'typeVarsOf' @t@ : all type variables in @t@
typeVarsOf :: TypeSkeleton r -> Set Id
typeVarsOf t@(ScalarT baseT tArgs r) = case baseT of
  TypeVarT name -> Set.singleton name  
  _ -> Set.unions (map typeVarsOf tArgs)
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
shape (ScalarT base tArgs _) = ScalarT base (map shape tArgs) ()
shape (FunctionT _ tArg tFun) = FunctionT dontCare (shape tArg) (shape tFun)

-- | Forget refinements of a schema
polyShape :: RSchema -> SSchema
polyShape (Monotype t) = Monotype (shape t)
polyShape (Forall a sch) = Forall a (polyShape sch)

-- | Insert trivial refinements
refine :: SType -> RType
refine (ScalarT base tArgs _) = ScalarT base (map refine tArgs) ftrue
refine (FunctionT x tArg tFun) = FunctionT x (refine tArg) (refine tFun)
      
-- | 'renameVar' @old new t@: rename all occurrences of @old@ in @t@ into @new@
renameVar :: Id -> Id -> RType -> RType -> RType
renameVar old new (FunctionT _ _ _)   t = t -- function arguments cannot occur in types
renameVar old new t@(ScalarT b _ _)  (ScalarT base tArgs fml) = ScalarT base (map (renameVar old new t) tArgs) (substitute (Map.singleton old (Var b new)) fml)
renameVar old new t                (FunctionT x tArg tRes) = FunctionT x (renameVar old new t tArg) (renameVar old new t tRes)

unknownsOfType (ScalarT _ tArgs fml) = Set.unions $ unknownsOf fml : map unknownsOfType tArgs
unknownsOfType (FunctionT _ tArg tRes) = unknownsOfType tArg `Set.union` unknownsOfType tRes

-- | Instantiate unknowns in a type
typeApplySolution sol (ScalarT base tArgs fml) = ScalarT base (map (typeApplySolution sol) tArgs) (applySolution sol fml)
typeApplySolution sol (FunctionT x tArg tRes) = FunctionT x (typeApplySolution sol tArg) (typeApplySolution sol tRes) 

-- | User-defined datatype representation
data Datatype = Datatype {
  _typeArgCount :: Int,
  _constructors :: [Id],                    -- ^ Constructor names
  _wfMetric :: Maybe (Formula -> Formula)   -- ^ Given a datatype term, returns an integer term that can serve as a well-founded metric for recursion
}

makeLenses ''Datatype

{- Evaluation environment -}

-- | Typing environment
data Environment = Environment {
  _symbols :: Map Int (Map Id RSchema),    -- ^ Variables and constants (with their refinement types)
  _constants :: Set Id,                    -- ^ Subset of symbols that are constants
  _boundTypeVars :: [Id],                  -- ^ Bound type variables
  _datatypes :: Map Id Datatype,           -- ^ Datatype representations
  _assumptions :: Set Formula,             -- ^ Positive unknown assumptions
  _negAssumptions :: Set Formula,          -- ^ Negative unknown assumptions
  _shapeConstraints :: Map Id SType        -- ^ For polymorphic recursive calls, the shape their types must have
}

makeLenses ''Environment  

-- | Environment with no symbols or assumptions
emptyEnv :: Environment
emptyEnv = Environment Map.empty Set.empty [] Map.empty Set.empty Set.empty Map.empty

addVariable :: Id -> RType -> Environment -> Environment
addVariable name t = addPolyVariable name (Monotype t)

addPolyVariable :: Id -> RSchema -> Environment -> Environment
addPolyVariable name sch = let n = arity (toMonotype sch) in (symbols %~ Map.insertWith (Map.union) n (Map.singleton name sch))

-- | 'addConstant' @name t env@ : add type binding @name@ :: Monotype @t@ to @env@
addConstant :: Id -> RType -> Environment -> Environment
addConstant name t = addPolyConstant name (Monotype t)

-- | 'addPolyConstant' @name sch env@ : add type binding @name@ :: @sch@ to @env@
addPolyConstant :: Id -> RSchema -> Environment -> Environment
addPolyConstant name sch = addPolyVariable name sch . (constants %~ Set.insert name)

symbolsOfArity n env = Map.findWithDefault Map.empty n (env ^. symbols) 

allSymbols :: Environment -> Map Id RSchema
allSymbols env = Map.unions $ Map.elems (env ^. symbols)

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
allScalars env = map (uncurry $ flip Var) $ Map.toList $ Map.mapMaybe baseType (symbolsOfArity 0 env)
  where
    baseType (Forall _ _) = Nothing -- TODO: what to do with polymorphic scalars like Nil?
    baseType (Monotype (ScalarT b _ _)) = Just b
    -- baseType (Monotype (FunctionT _ _ _)) = Nothing

-- | 'addAssumption' @f env@ : @env@ with extra assumption @f@
addAssumption :: Formula -> Environment -> Environment
addAssumption f = assumptions %~ Set.insert f

-- | 'addNegAssumption' @f env@ : @env@ with extra assumption not @f@
addNegAssumption :: Formula -> Environment -> Environment
addNegAssumption f = negAssumptions %~ Set.insert f

-- | Positive and negative formulas encoded in an environment    
embedding :: Environment -> (Set Formula, Set Formula)    
embedding env = ((env ^. assumptions) `Set.union` (Map.foldlWithKey (\fmls name t -> fmls `Set.union` embedBinding name t) Set.empty $ symbolsOfArity 0 env), env ^.negAssumptions)
  where
    embedBinding _ (Monotype (ScalarT _ _ (BoolLit True))) = Set.empty -- Ignore trivial types
    embedBinding x (Monotype (ScalarT baseT _ fml)) = Set.singleton $ substitute (Map.singleton valueVarName (Var baseT x)) fml    
    -- embedBinding x (Monotype (ScalarT baseT _ fml)) = if Set.member x (env ^. constants) 
      -- then Set.empty -- Ignore constants
      -- else Set.singleton $ substitute (Map.singleton valueVarName (Var baseT x)) fml
    embedBinding _ _ = Set.empty -- Ignore polymorphic things, since they could only be constants
    
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
  PFix [Id] (Program s c t)                 -- ^ Fixpoint  
  
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
bool = ScalarT BoolT []  
bool_ = bool ()
boolAll = bool ftrue

int = ScalarT IntT []
int_ = int ()
intAll = int ftrue
nat = int (valInt |>=| IntLit 0)
pos = int (valInt |>| IntLit 0)

vart n = ScalarT (TypeVarT n) []
vart_ n = vart n ()
vartAll n = vart n ftrue

(|->|) = FunctionT dontCare

infixr 5 |->|

-- | 'instantiateSymbols' @subst p@ : apply @subst@ to polymorphic symbols
instantiateSymbols :: TypeSubstitution Formula -> LiquidProgram -> LiquidProgram
instantiateSymbols subst (Program body t) = (flip Program (rTypeSubstitute subst t)) $ case body of
  PSymbol s subst' -> PSymbol s (Map.union subst' $ restrictDomain (typeVarsOf t) subst)
  PApp f arg -> PApp (instantiateSymbols subst f) (instantiateSymbols subst arg)
  PFun x body -> PFun x (instantiateSymbols subst body)
  PIf c t e -> PIf c (instantiateSymbols subst t) (instantiateSymbols subst e)
  PMatch scr cases -> PMatch (instantiateSymbols subst scr) (map instantiateCase cases)
  PFix fs body -> PFix fs (instantiateSymbols subst body)
  where
    instantiateCase (Case cons args e) = Case cons args (instantiateSymbols subst e)  

{- Typing constraints -}
          
-- | Typing constraints
data Constraint = Unconstrained
  | Subtype Environment RType RType
  | WellFormed Environment RType
  | WellFormedCond Environment Formula
  | WellFormedLeaf RType [RType]
  | WellFormedFunction [[Constraint]]  
  
isWFLeaf (WellFormedLeaf _ _) = True
isWFLeaf _ = False
  