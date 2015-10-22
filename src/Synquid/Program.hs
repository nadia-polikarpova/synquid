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

data BaseType = BoolT | IntT | DatatypeT Id | TypeVarT Id
  deriving (Eq, Ord)
  
-- | Type skeletons (parametrized by refinements)
data TypeSkeleton r =
  ScalarT BaseType [TypeSkeleton r]  r |
  FunctionT Id (TypeSkeleton r) (TypeSkeleton r)  
  deriving (Eq, Ord)
  
toSort BoolT = BoolS
toSort IntT = IntS
toSort (DatatypeT name) = UninterpretedS name
toSort (TypeVarT name) = UninterpretedS name
  
isFunctionType (FunctionT _ _ _) = True
isFunctionType _ = False
argType (FunctionT _ t _) = t
resType (FunctionT _ _ t) = t

arity (FunctionT _ _ t) = arity t + 1
arity _ = 0

lastType t@(ScalarT _ _ _) = t
lastType (FunctionT _ _ tRes) = lastType tRes

varRefinement x b = let s = toSort b in (Var s valueVarName |=| Var s x)
isVarRefinemnt (Binary Eq (Var _ v) (Var _ _)) = v == valueVarName
isVarRefinemnt _ = False

-- | Polymorphic type skeletons (parametrized by refinements)
data SchemaSkeleton r = 
  Monotype (TypeSkeleton r) |
  Forall Id (SchemaSkeleton r)
  
toMonotype :: SchemaSkeleton r -> TypeSkeleton r
toMonotype (Monotype t) = t
toMonotype (Forall _ t) = toMonotype t
  
-- | Mapping from type variables to types
type TypeSubstitution = Map Id RType

-- | 'typeSubstitute' @t@ : substitute all free type variables in @t@
typeSubstitute :: TypeSubstitution -> RType -> RType
typeSubstitute subst t@(ScalarT (TypeVarT a) [] r) = case Map.lookup a subst of
  Just t' -> addRefinement (typeSubstitute subst t') (typeSubstituteFML subst r) -- In {v: a | r}, we might have to substitute sorts inside r
  Nothing -> t
  where
    addRefinement (ScalarT base tArgs fml) fml' = if isVarRefinemnt fml'
      then ScalarT base tArgs fml' -- the type of a polymorphic variable does not require any other refinements
      else ScalarT base tArgs (fml `andClean` fml')
    addRefinement t (BoolLit True) = t
    addRefinement t _ = error $ "addRefinement: applied to function type"
    
    typeSubstituteFML subst fml = case fml of 
      SetLit el es -> SetLit (substSort el) (map (typeSubstituteFML subst) es)
      Var s name -> Var (substSort s) name
      Unknown s name -> Unknown (Map.map (typeSubstituteFML subst) s) name
      Unary op e -> Unary op (typeSubstituteFML subst e)
      Binary op l r -> Binary op (typeSubstituteFML subst l) (typeSubstituteFML subst r)
      Measure s name e -> Measure (substSort s) name (typeSubstituteFML subst e)
      _ -> fml
      where
        substSort s@(UninterpretedS name) = case Map.lookup name subst of
          Just (ScalarT b _ _) -> toSort b
          Just _ -> error $ unwords ["typeSubstituteFML: cannot substitute function type for", name]
          Nothing -> s
        substSort (SetS el) = SetS (substSort el)
        substSort s = s    
  
typeSubstitute subst (ScalarT baseT tArgs r) = let tArgs' = map (typeSubstitute subst) tArgs 
  in ScalarT baseT tArgs' r -- Here no need to substitute sorts inside r, since type arguments do not get reflected in the sort
typeSubstitute subst (FunctionT x tArg tRes) = FunctionT x (typeSubstitute subst tArg) (typeSubstitute subst tRes)

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
shape (FunctionT x tArg tFun) = FunctionT x (shape tArg) (shape tFun)

-- | Forget refinements of a schema
polyShape :: RSchema -> SSchema
polyShape (Monotype t) = Monotype (shape t)
polyShape (Forall a sch) = Forall a (polyShape sch)

-- | Insert weakest refinement
refineTop :: SType -> RType
refineTop (ScalarT base tArgs _) = ScalarT base (map refineTop tArgs) ftrue
refineTop (FunctionT x tArg tFun) = FunctionT x (refineBot tArg) (refineTop tFun)

-- | Insert strongest refinement
refineBot :: SType -> RType
refineBot (ScalarT base tArgs _) = ScalarT base (map refineBot tArgs) ffalse
refineBot (FunctionT x tArg tFun) = FunctionT x (refineTop tArg) (refineBot tFun)
      
-- | 'renameVar' @old new t@: rename all occurrences of @old@ in @t@ into @new@
renameVar :: Id -> Id -> RType -> RType -> RType
renameVar old new (FunctionT _ _ _)   t = t -- function arguments cannot occur in types
renameVar old new t@(ScalarT b _ _)  (ScalarT base tArgs fml) = let newFml = extractPrimitiveConst (Var (toSort b) new)
  in ScalarT base (map (renameVar old new t) tArgs) (substitute (Map.singleton old newFml) fml)
renameVar old new t                  (FunctionT x tArg tRes) = FunctionT x (renameVar old new t tArg) (renameVar old new t tRes)

-- | 'unknownsOfType' @t: all unknowns in @t@
unknownsOfType :: RType -> Set Formula 
unknownsOfType (ScalarT _ tArgs fml) = Set.unions $ unknownsOf fml : map unknownsOfType tArgs
unknownsOfType (FunctionT _ tArg tRes) = unknownsOfType tArg `Set.union` unknownsOfType tRes

-- | Instantiate unknowns in a type
typeApplySolution :: Solution -> RType -> RType
typeApplySolution sol (ScalarT base tArgs fml) = ScalarT base (map (typeApplySolution sol) tArgs) (applySolution sol fml)
typeApplySolution sol (FunctionT x tArg tRes) = FunctionT x (typeApplySolution sol tArg) (typeApplySolution sol tRes) 

-- | User-defined datatype representation
data Datatype = Datatype {
  _typeArgCount :: Int,
  _constructors :: [Id],                    -- ^ Constructor names
  _wfMetric :: Maybe (Formula -> Formula)   -- ^ Given a datatype term, returns an integer term that can serve as a well-founded metric for recursion
}

makeLenses ''Datatype

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

{- Program terms -}    
    
-- | One case inside a pattern match expression
data Case r = Case {
  constructor :: Id,      -- ^ Constructor name
  argNames :: [Id],       -- ^ Bindings for constructor arguments
  expr :: Program r       -- ^ Result of the match in this case
} deriving Eq    
    
-- | Program skeletons parametrized by information stored symbols, conditionals, and by node types
data BareProgram r =
  PSymbol Id |                            -- ^ Symbol (variable or constant)
  PApp (Program r) (Program r) |          -- ^ Function application
  PFun Id (Program r) |                   -- ^ Lambda abstraction
  PIf Formula (Program r) (Program r) |   -- ^ Conditional
  PMatch (Program r) [Case r] |           -- ^ Pattern match on datatypes
  PFix [Id] (Program r)                   -- ^ Fixpoint  
  deriving Eq
  
-- | Programs annotated with types  
data Program r = Program {
  content :: BareProgram r,
  typ :: TypeSkeleton r
} deriving Eq

-- | Fully defined programs 
type RProgram = Program Formula

hole t = Program (PSymbol "??") t

headSymbol (Program (PSymbol name) _) = name
headSymbol (Program (PApp fun _) _) = headSymbol fun

-- | Instantiate type variables in a program
programSubstituteTypes :: TypeSubstitution -> RProgram -> RProgram
programSubstituteTypes subst (Program p t) = Program (programSubstituteTypes' p) (typeSubstitute subst t)
  where
    pst = programSubstituteTypes subst
    
    programSubstituteTypes' (PSymbol name) = PSymbol name
    programSubstituteTypes' (PApp fun arg) = PApp (pst fun) (pst arg)
    programSubstituteTypes' (PFun name p) = PFun name (pst p)    
    programSubstituteTypes' (PIf fml p1 p2) = PIf fml (pst p1) (pst p2)
    programSubstituteTypes' (PMatch scr cases) = PMatch (pst scr) (map (\(Case ctr args p) -> Case ctr args (pst p)) cases)
    programSubstituteTypes' (PFix args p) = PFix args (pst p)

-- | Instantiate unknowns in a program
programApplySolution :: Solution -> RProgram -> RProgram
programApplySolution sol (Program p t) = Program (programApplySolution' p) (typeApplySolution sol t)
  where
    pas = programApplySolution sol
    
    programApplySolution' (PSymbol name) = PSymbol name
    programApplySolution' (PApp fun arg) = PApp (pas fun) (pas arg)
    programApplySolution' (PFun name p) = PFun name (pas p)    
    programApplySolution' (PIf fml p1 p2) = PIf (applySolution sol fml) (pas p1) (pas p2)
    programApplySolution' (PMatch scr cases) = PMatch (pas scr) (map (\(Case ctr args p) -> Case ctr args (pas p)) cases)
    programApplySolution' (PFix args p) = PFix args (pas p)
    
-- | Substitute a symbol for a subterm in a program    
programSubstituteSymbol :: Id -> RProgram -> RProgram -> RProgram
programSubstituteSymbol name subterm (Program p t) = Program (programSubstituteSymbol' p) t
  where
    pss = programSubstituteSymbol name subterm
    
    programSubstituteSymbol' (PSymbol x) = if x == name then content subterm else p
    programSubstituteSymbol' (PApp fun arg) = PApp (pss fun) (pss arg)
    programSubstituteSymbol' (PFun name pBody) = PFun name (pss pBody)    
    programSubstituteSymbol' (PIf fml p1 p2) = PIf fml (pss p1) (pss p2)
    programSubstituteSymbol' (PMatch scr cases) = PMatch (pss scr) (map (\(Case ctr args pBody) -> Case ctr args (pss pBody)) cases)
    programSubstituteSymbol' (PFix args pBody) = PFix args (pss pBody)

{- Evaluation environment -}

-- | Typing environment
data Environment = Environment {
  _symbols :: Map Int (Map Id RSchema),    -- ^ Variables and constants (with their refinement types), indexed by arity
  _constants :: Set Id,                    -- ^ Subset of symbols that are constants
  _ghosts :: Map Id RType,                 -- ^ Ghost variables (to be used in embedding but not in the program)
  _boundTypeVars :: [Id],                  -- ^ Bound type variables
  _datatypes :: Map Id Datatype,           -- ^ Datatype representations
  _assumptions :: Set Formula,             -- ^ Positive unknown assumptions
  _negAssumptions :: Set Formula,          -- ^ Negative unknown assumptions
  _shapeConstraints :: Map Id SType,       -- ^ For polymorphic recursive calls, the shape their types must have
  _usedScrutinees :: [RProgram]            -- ^ Program terms that has already been scrutinized
}

makeLenses ''Environment  

-- | Environment with no symbols or assumptions
emptyEnv :: Environment
emptyEnv = Environment Map.empty Set.empty Map.empty [] Map.empty Set.empty Set.empty Map.empty []

-- | 'symbolsOfArity' @n env@: all symbols of arity @n@ in @env@
symbolsOfArity n env = Map.findWithDefault Map.empty n (env ^. symbols) 

-- | All symbols in an environment
allSymbols :: Environment -> Map Id RSchema
allSymbols env = Map.unions $ Map.elems (env ^. symbols)

-- | 'isBound' @tv env@: is type variable @tv@ bound in @env@?
isBound :: Id -> Environment -> Bool
isBound tv env = tv `elem` env ^. boundTypeVars

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

-- | 'addDatatype' @name env@ : add datatype @name@ to the environment
addDatatype :: Id -> Datatype -> Environment -> Environment
addDatatype name dt = over datatypes (Map.insert name dt)

-- | 'addTypeVar' @a@ : Add bound type variable @a@ to the environment
addTypeVar :: Id -> Environment -> Environment
addTypeVar a = over boundTypeVars (a :)

-- | 'allScalars' @env@ : logic terms for all scalar symbols in @env@
allScalars :: Environment -> TypeSubstitution -> [Formula]
allScalars env subst = map (uncurry $ flip Var) $ Map.toList $ Map.mapMaybe sort (symbolsOfArity 0 env)
  where
    sort (Forall _ _) = Nothing
    sort (Monotype t@(ScalarT (TypeVarT a) [] _)) | a `Map.member` subst = sort (Monotype $ typeSubstitute subst t)
    sort (Monotype (ScalarT b _ _)) = Just $ toSort b

-- | 'addAssumption' @f env@ : @env@ with extra assumption @f@
addAssumption :: Formula -> Environment -> Environment
addAssumption f = assumptions %~ Set.insert f

-- | 'addNegAssumption' @f env@ : @env@ with extra assumption not @f@
addNegAssumption :: Formula -> Environment -> Environment
addNegAssumption f = negAssumptions %~ Set.insert f

-- | Positive and negative formulas encoded in an environment    
embedding :: Environment -> TypeSubstitution -> (Set Formula, Set Formula)    
embedding env subst = ((env ^. assumptions) `Set.union` (Map.foldlWithKey (\fmls name sch -> fmls `Set.union` embedBinding name sch) Set.empty allSymbols), env ^.negAssumptions)
  where
    allSymbols = symbolsOfArity 0 env `Map.union` Map.map Monotype (env ^. ghosts)
    embedBinding x (Monotype t@(ScalarT (TypeVarT a) [] _)) | not (isBound a env) = if a `Map.member` subst 
      then embedBinding x (Monotype $ typeSubstitute subst t) -- Substitute free variables
      else Set.empty
      -- else error $ unwords ["embedding: encountered free type variable", a, "in", show $ Map.keys subst]
    embedBinding _ (Monotype (ScalarT _ _ (BoolLit True))) = Set.empty -- Ignore trivial types
    embedBinding x (Monotype (ScalarT baseT _ fml)) = if Set.member x (env ^. constants) 
      then Set.empty -- Ignore constants
      else Set.singleton $ substitute (Map.singleton valueVarName (Var (toSort baseT) x)) fml
    embedBinding _ _ = Set.empty -- Ignore polymorphic things, since they could only be constants
    
{- Misc -}
          
-- | Typing constraints
data Constraint = Subtype Environment RType RType
  | WellFormed Environment RType
  | WellFormedCond Environment Formula
