{-# LANGUAGE TemplateHaskell, DeriveFunctor #-}

-- | Executable programs
module Synquid.Program where

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

unifySorts :: Set Id -> [Sort] -> [Sort] -> Either (Sort, Sort) SortSubstitution
unifySorts boundTvs = unifySorts' Map.empty
  where
    unifySorts' subst [] []                                 
      = Right subst
    unifySorts' subst (x : xs) (y : ys) | x == y 
      = unifySorts' subst xs ys
    unifySorts' subst (SetS x : xs) (SetS y : ys)           
      = unifySorts' subst (x:xs) (y:ys)
    unifySorts' subst (DataS name args : xs) (DataS name' args' :ys) 
      = if name == name' 
          then unifySorts' subst (args ++ xs) (args' ++ ys) 
          else Left (DataS name [], DataS name' [])
    unifySorts' subst (AnyS : xs) (_ : ys) = unifySorts' subst xs ys
    unifySorts' subst (_ : xs) (AnyS : ys) = unifySorts' subst xs ys
    unifySorts' subst (VarS x : xs) (y : ys)                 
      | not (Set.member x boundTvs)
      = case Map.lookup x subst of
            Just s -> unifySorts' subst (s : xs) (y : ys)
            Nothing -> if x `Set.member` typeVarsOf (fromSort y) 
              then Left (VarS x, y) 
              else unifySorts' (Map.insert x y subst) xs ys
    unifySorts' subst (x : xs) (VarS y : ys)
      | not (Set.member y boundTvs)
      = unifySorts' subst (VarS y : ys) (x:xs)
    unifySorts' subst (x: _) (y: _)                 
      = Left (x, y)

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

-- | Unrefined base
type SBaseType = BaseType ()

-- | Refined base
type RBaseType = BaseType Formula

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

-- | 'unknownsOfType' @t: all unknowns in @t@
unknownsOfType :: RType -> Set Formula 
unknownsOfType (ScalarT (DatatypeT _ tArgs pArgs) fml) = Set.unions $ unknownsOf fml : map unknownsOf pArgs ++ map unknownsOfType tArgs
unknownsOfType (ScalarT _ fml) = unknownsOf fml
unknownsOfType (FunctionT _ tArg tRes) = unknownsOfType tArg `Set.union` unknownsOfType tRes

-- | Instantiate unknowns in a type
typeApplySolution :: Solution -> RType -> RType
typeApplySolution sol (ScalarT (DatatypeT name tArgs pArgs) fml) = ScalarT (DatatypeT name (map (typeApplySolution sol) tArgs) (map (applySolution sol) pArgs)) (applySolution sol fml)
typeApplySolution sol (ScalarT base fml) = ScalarT base (applySolution sol fml)
typeApplySolution sol (FunctionT x tArg tRes) = FunctionT x (typeApplySolution sol tArg) (typeApplySolution sol tRes) 
typeApplySolution _ AnyT = AnyT

-- | Predicate signature: name and argument sorts  
data PredSig = PredSig {
  predSigName :: Id,
  predSigArgSorts :: [Sort],
  predSigResSort :: Sort
} deriving (Eq, Ord)

nominalPredApp (PredSig pName argSorts resSort) = Pred resSort pName (zipWith Var argSorts deBrujns)

-- | User-defined datatype representation
data DatatypeDef = DatatypeDef {
  _typeParams :: [Id],              -- ^ Type parameters
  _predParams :: [PredSig],         -- ^ Signatures of predicate parameters
  _predVariances :: [Bool],         -- ^ For each predicate parameter, whether it is contravariant
  _constructors :: [Id],            -- ^ Constructor names
  _wfMetric :: Maybe Id             -- ^ Name of the measure that serves as well founded termination metric
} deriving (Eq, Ord)

makeLenses ''DatatypeDef

-- | One case in a measure definition: constructor name, arguments, and body  
data MeasureCase = MeasureCase Id [Id] Formula
  deriving (Eq, Ord)

-- | User-defined measure function representation
data MeasureDef = MeasureDef {
  _inSort :: Sort,
  _outSort :: Sort,
  _definitions :: [MeasureCase],
  _postcondition :: Formula
} deriving (Eq, Ord)

makeLenses ''MeasureDef

{- Program terms -}    
    
-- | One case inside a pattern match expression
data Case t = Case {
  constructor :: Id,      -- ^ Constructor name
  argNames :: [Id],       -- ^ Bindings for constructor arguments
  expr :: Program t       -- ^ Result of the match in this case
} deriving (Eq, Ord, Functor)
    
-- | Program skeletons parametrized by information stored symbols, conditionals, and by node types
data BareProgram t =
  PSymbol Id |                                -- ^ Symbol (variable or constant)
  PApp (Program t) (Program t) |              -- ^ Function application
  PFun Id (Program t) |                       -- ^ Lambda abstraction
  PIf (Program t) (Program t) (Program t) |   -- ^ Conditional
  PMatch (Program t) [Case t] |               -- ^ Pattern match on datatypes
  PFix [Id] (Program t) |                     -- ^ Fixpoint
  PLet Id (Program t) (Program t) |           -- ^ Let binding
  PHole |                                     -- ^ Hole (program to fill in)
  PErr                                        -- ^ Error
  deriving (Eq, Ord, Functor)
  
-- | Programs annotated with types  
data Program t = Program {
  content :: BareProgram t,
  typeOf :: t
} deriving (Functor)

instance Eq (Program t) where
  (==) (Program l _) (Program r _) = l == r
  
instance Ord (Program t) where
  (<=) (Program l _) (Program r _) = l <= r
  
-- | Untyped programs  
type UProgram = Program RType
-- | Refinement-typed programs
type RProgram = Program RType

untyped c = Program c AnyT
uHole = untyped PHole
isHole (Program PHole _) = True
isHole _ = False

eraseTypes :: RProgram -> UProgram
eraseTypes = fmap (const AnyT)

symbolName (Program (PSymbol name) _) = name
symbolList (Program (PSymbol name) _) = [name]
symbolList (Program (PApp fun arg) _) = symbolList fun ++ symbolList arg

symbolsOf (Program p _) = case p of 
  PSymbol name -> Set.singleton name
  PApp fun arg -> symbolsOf fun `Set.union` symbolsOf arg
  PFun x body -> symbolsOf body 
  PIf cond thn els -> symbolsOf cond `Set.union` symbolsOf thn `Set.union` symbolsOf els
  PMatch scr cases -> symbolsOf scr `Set.union` Set.unions (map (symbolsOf . expr) cases)
  PFix x body -> symbolsOf body
  PLet x def body -> symbolsOf def `Set.union` symbolsOf body
  _ -> Set.empty

errorProgram = Program PErr (vart dontCare ftrue)
isError (Program PErr _) = True
isError _ = False
    
-- | Substitute a symbol for a subterm in a program    
programSubstituteSymbol :: Id -> RProgram -> RProgram -> RProgram
programSubstituteSymbol name subterm (Program p t) = Program (programSubstituteSymbol' p) t
  where
    pss = programSubstituteSymbol name subterm
    
    programSubstituteSymbol' (PSymbol x) = if x == name then content subterm else p
    programSubstituteSymbol' (PApp fun arg) = PApp (pss fun) (pss arg)
    programSubstituteSymbol' (PFun name pBody) = PFun name (pss pBody)    
    programSubstituteSymbol' (PIf c p1 p2) = PIf (pss c) (pss p1) (pss p2)
    programSubstituteSymbol' (PMatch scr cases) = PMatch (pss scr) (map (\(Case ctr args pBody) -> Case ctr args (pss pBody)) cases)
    programSubstituteSymbol' (PFix args pBody) = PFix args (pss pBody)

-- | Convert an executable formula into a program    
fmlToProgram :: Formula -> RProgram
fmlToProgram (BoolLit b) = Program (PSymbol $ show b) (ScalarT BoolT $ valBool |=| BoolLit b)
fmlToProgram (IntLit i) = Program (PSymbol $ show i) (ScalarT IntT $ valBool |=| IntLit i)
fmlToProgram (Var s x) = Program (PSymbol x) (addRefinement (fromSort s) (varRefinement x s))
fmlToProgram fml@(Unary op e) = let 
    s = sortOf fml 
    p = fmlToProgram e
    fun = Program (PSymbol $ unOpTokens Map.! op) (FunctionT "x" (typeOf p) opRes)
  in Program (PApp fun p) (addRefinement (fromSort s) (Var s valueVarName |=| fml))
  where    
    opRes 
      | op == Not = bool $ valBool |=| fnot (intVar "x")
      | otherwise = int $ valInt |=| Unary op (intVar "x")    
fmlToProgram fml@(Binary op e1 e2) = let 
    s = sortOf fml 
    p1 = fmlToProgram e1
    p2 = fmlToProgram e2
    fun1 = Program (PSymbol $ binOpTokens Map.! op) (FunctionT "x" (typeOf p1) (FunctionT "y" (typeOf p2) opRes))
    fun2 = Program (PApp fun1 p1) (FunctionT "y" (typeOf p2) opRes)
  in Program (PApp fun2 p2) (addRefinement (fromSort s) (Var s valueVarName |=| fml))
  where
    opRes 
      | op == Times || op == Times || op == Times = int $ valInt |=| Binary op (intVar "x") (intVar "y")
      | otherwise                                 = bool $ valBool |=| Binary op (intVar "x") (intVar "y")
      
-- | 'renameAsImpl' @p t@: change argument names in function type @t@ to be the same as in the abstraction @p@
renameAsImpl :: UProgram -> RType -> RType
renameAsImpl p t = renameAsImpl' Map.empty p t
  where
    renameAsImpl' subst (Program (PFun y pRes) _) (FunctionT x tArg tRes) = case tArg of
      ScalarT baseT fml -> FunctionT y (substituteInType subst tArg) (renameAsImpl' (Map.insert x (Var (toSort baseT) y) subst) pRes tRes)    
      _ -> FunctionT y (substituteInType subst tArg) (renameAsImpl' subst pRes tRes)      
    renameAsImpl' subst  _ t = substituteInType subst t      

{- Evaluation environment -}

-- | Typing environment
data Environment = Environment {
  -- | Variable part:
  _symbols :: Map Int (Map Id RSchema),    -- ^ Variables and constants (with their refinement types), indexed by arity
  _ghosts :: Map Id RType,                 -- ^ Ghost variables (to be used in embedding but not in the program)
  _boundTypeVars :: [Id],                  -- ^ Bound type variables
  _boundPredicates :: [PredSig],           -- ^ Argument sorts of bound abstract refinements
  _assumptions :: Set Formula,             -- ^ Unknown assumptions
  _shapeConstraints :: Map Id SType,       -- ^ For polymorphic recursive calls, the shape their types must have
  _usedScrutinees :: [RProgram],           -- ^ Program terms that has already been scrutinized
  _unfoldedVars :: Set Id,                 -- ^ In eager match mode, datatype variables that can be scrutinized
  -- | Constant part:
  _constants :: Set Id,                    -- ^ Subset of symbols that are constants  
  _datatypes :: Map Id DatatypeDef,        -- ^ Datatype definitions
  _globalPredicates :: Map Id [Sort],      -- ^ Signatures (resSort:argSorts) of module-level logic functions (measures, predicates) 
  _measures :: Map Id MeasureDef,          -- ^ Measure definitions
  _typeSynonyms :: Map Id ([Id], RType),   -- ^ Type synonym definitions
  _unresolvedConstants :: Map Id RSchema   -- ^ Unresolved types of components (used for reporting specifications with macros)
}

makeLenses ''Environment

instance Eq Environment where
  (==) e1 e2 = (e1 ^. symbols) == (e2 ^. symbols) && (e1 ^. assumptions) == (e2 ^. assumptions)
  
instance Ord Environment where
  (<=) e1 e2 = (e1 ^. symbols) <= (e2 ^. symbols) && (e1 ^. assumptions) <= (e2 ^. assumptions)  

-- | Empty environment
emptyEnv = Environment {
  _symbols = Map.empty,
  _ghosts = Map.empty,
  _boundTypeVars = [],
  _boundPredicates = [],
  _assumptions = Set.empty,
  _shapeConstraints = Map.empty,
  _usedScrutinees = [],
  _unfoldedVars = Set.empty,
  _constants = Set.empty,
  _globalPredicates = Map.empty,
  _datatypes = Map.empty,
  _measures = Map.empty,
  _typeSynonyms = Map.empty,
  _unresolvedConstants = Map.empty
}

-- | 'symbolsOfArity' @n env@: all symbols of arity @n@ in @env@
symbolsOfArity n env = Map.findWithDefault Map.empty n (env ^. symbols) 

-- | All symbols in an environment
allSymbols :: Environment -> Map Id RSchema
allSymbols env = Map.unions $ Map.elems (env ^. symbols)

-- | 'lookupSymbol' @name env@ : type of symbol @name@ in @env@, including built-in constants
lookupSymbol :: Id -> Int -> Environment -> Maybe RSchema
lookupSymbol name a env
  | a == 0 && name == "True"                          = Just $ Monotype $ ScalarT BoolT valBool
  | a == 0 && name == "False"                         = Just $ Monotype $ ScalarT BoolT (fnot valBool)
  | a == 0 && isJust asInt                            = Just $ Monotype $ ScalarT IntT (valInt |=| IntLit (fromJust asInt))
  | a == 1 && (name `elem` Map.elems unOpTokens)      = let op = head $ Map.keys $ Map.filter (== name) unOpTokens in Just $ unOpType op
  | a == 2 && (name `elem` Map.elems binOpTokens)     = let op = head $ Map.keys $ Map.filter (== name) binOpTokens in Just $ binOpType op
  | otherwise                                         = Map.lookup name (allSymbols env)
  where
    asInt = asInteger name
    
unOpType Neg       = Monotype $ FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))
unOpType Not       = Monotype $ FunctionT "x" boolAll (bool (valBool |=| fnot (boolVar "x")))
binOpType Times    = Monotype $ FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |*| intVar "y")))
binOpType Plus     = Monotype $ FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |+| intVar "y")))
binOpType Minus    = Monotype $ FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |-| intVar "y")))
binOpType Eq       = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |=| vartVar "a" "y"))))
binOpType Neq      = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |/=| vartVar "a" "y"))))
binOpType Lt       = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |<| vartVar "a" "y"))))
binOpType Le       = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |<=| vartVar "a" "y"))))
binOpType Gt       = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |>| vartVar "a" "y"))))
binOpType Ge       = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |>=| vartVar "a" "y"))))
binOpType And      = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" |&| boolVar "y"))))
binOpType Or       = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" ||| boolVar "y"))))
binOpType Implies  = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" |=>| boolVar "y"))))
binOpType Iff      = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" |<=>| boolVar "y"))))

-- | Is @name@ a constant in @env@ including built-in constants)?    
isConstant name env = (name `elem` ["True", "False"]) ||
                      isJust (asInteger name) || 
                      (name `elem` Map.elems unOpTokens) || 
                      (name `elem` Map.elems binOpTokens) || 
                      (name `Set.member` (env ^. constants))    

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

addUnresolvedConstant :: Id -> RSchema -> Environment -> Environment
addUnresolvedConstant name sch = unresolvedConstants %~ Map.insert name sch

removeVariable :: Id -> Environment -> Environment
removeVariable name env = case Map.lookup name (allSymbols env) of
  Nothing -> env
  Just sch -> over symbols (Map.insertWith (flip Map.difference) (arity $ toMonotype sch) (Map.singleton name sch)) . over constants (Set.delete name) $ env
  
unfoldAllVariables env = over unfoldedVars (Set.union (Map.keysSet (symbolsOfArity 0 env) Set.\\ (env ^. constants))) env  
  
addGhost :: Id -> RType -> Environment -> Environment  
addGhost name t = over ghosts (Map.insert name t)

addMeasure :: Id -> MeasureDef -> Environment -> Environment
addMeasure measureName m = over measures (Map.insert measureName m)

addBoundPredicate :: PredSig -> Environment -> Environment
addBoundPredicate sig = over boundPredicates (sig :)

addGlobalPredicate :: Id -> Sort -> [Sort] -> Environment -> Environment
addGlobalPredicate predName resSort argSorts = over globalPredicates (Map.insert predName (resSort : argSorts))

addTypeSynonym :: Id -> [Id] -> RType -> Environment -> Environment
addTypeSynonym name tvs t = over typeSynonyms (Map.insert name (tvs, t))

-- | 'addDatatype' @name env@ : add datatype @name@ to the environment
addDatatype :: Id -> DatatypeDef -> Environment -> Environment
addDatatype name dt = over datatypes (Map.insert name dt)

-- | 'lookupConstructor' @ctor env@ : the name of the datatype for which @ctor@ is regisered as a constructor in @env@, if any
lookupConstructor :: Id -> Environment -> Maybe Id
lookupConstructor ctor env = let m = Map.filter (\dt -> ctor `elem` dt ^. constructors) (env ^. datatypes)
  in if Map.null m
      then Nothing
      else Just $ fst $ Map.findMin m

-- | 'addTypeVar' @a@ : Add bound type variable @a@ to the environment
addTypeVar :: Id -> Environment -> Environment
addTypeVar a = over boundTypeVars (a :)

-- | 'addAssumption' @f env@ : @env@ with extra assumption @f@
addAssumption :: Formula -> Environment -> Environment
addAssumption f = assumptions %~ Set.insert f

-- | 'addScrutinee' @p env@ : @env@ with @p@ marked as having been scrutinized already
addScrutinee :: RProgram -> Environment -> Environment
addScrutinee p = usedScrutinees %~ (p :)

allPredicates env = (Map.fromList $ map (\(PredSig pName argSorts resSort) -> (pName, resSort:argSorts)) (env ^. boundPredicates)) `Map.union` (env ^. globalPredicates)

-- | 'allMeasuresOf' @dtName env@ : all measure of datatype with name @dtName@ in @env@
allMeasuresOf dtName env = Map.filter (\(MeasureDef (DataS sName _) _ _ _) -> dtName == sName) $ env ^. measures

-- | 'allMeasurePostconditions' @baseT env@ : all nontrivial postconditions of measures of @baseT@ in case it is a datatype
allMeasurePostconditions includeQuanitifed baseT@(DatatypeT dtName tArgs _) env = 
    let allMeasures = Map.toList $ allMeasuresOf dtName env 
    in catMaybes $ map extractPost allMeasures ++ if includeQuanitifed then map elemProperties allMeasures else []
  where
    extractPost (mName, MeasureDef _ outSort _ fml) = 
      if fml == ftrue
        then Nothing
        else Just $ substitute (Map.singleton valueVarName (Pred outSort mName [Var (toSort baseT) valueVarName])) fml
        
    elemProperties (mName, MeasureDef (DataS _ vars) (SetS a) _ _) = case elemIndex a vars of
      Nothing -> Nothing
      Just i -> let (ScalarT elemT fml) = tArgs !! i -- @mName@ is a set of datatype "elements": add an axiom that every element of the set has that property 
                in if fml == ftrue || fml == ffalse || not (Set.null $ unknownsOf fml)
                    then Nothing
                    else  let
                            elemSort = toSort elemT
                            scopedVar = Var elemSort "_x"
                            setVal = Pred (SetS elemSort) mName [Var (toSort baseT) valueVarName]
                          in Just $ All scopedVar (fin scopedVar setVal |=>| substitute (Map.singleton valueVarName scopedVar) fml)
    elemProperties (mName, MeasureDef _ _ _ _) = Nothing
    
allMeasurePostconditions _ _ _ = []

typeSubstituteEnv :: TypeSubstitution -> Environment -> Environment
typeSubstituteEnv tass env = over symbols (Map.map (Map.map (schemaSubstitute tass))) env
    
{- Input language declarations -}

-- | Constructor signature: name and type
data ConstructorSig = ConstructorSig Id RType
  deriving (Eq)

data Declaration =
  TypeDecl Id [Id] RType |                                  -- ^ Type name, variables, and definition
  FuncDecl Id RSchema |                                     -- ^ Function name and signature
  DataDecl Id [Id] [(PredSig, Bool)] [ConstructorSig] |     -- ^ Datatype name, type parameters, predicate parameters, and constructor definitions
  MeasureDecl Id Sort Sort Formula [MeasureCase] Bool |     -- ^ Measure name, input sort, output sort, postcondition, definition cases, and whether this is a termination metric
  PredDecl PredSig |                                        -- ^ Module-level predicate
  QualifierDecl [Formula] |                                 -- ^ Qualifiers
  MutualDecl [Id] |                                         -- ^ Mutual recursion group
  InlineDecl Id [Id] Formula |                              -- ^ Inline predicate
  SynthesisGoal Id UProgram                                 -- ^ Name and template for the function to reconstruct
  deriving (Eq)

constructorName (ConstructorSig name _) = name
            
{- Misc -}
          
-- | Typing constraints
data Constraint = Subtype Environment RType RType Bool
  | WellFormed Environment RType
  | WellFormedCond Environment Formula
  | WellFormedMatchCond Environment Formula
  | WellFormedPredicate Environment [Sort] Id
  deriving (Eq, Ord)
  
-- | Synthesis goal
data Goal = Goal {
  gName :: Id,                  -- ^ Function name
  gEnvironment :: Environment,  -- ^ Enclosing environment
  gSpec :: RSchema,             -- ^ Specification
  gImpl :: UProgram,            -- ^ Implementation template
  gDepth :: Int                 -- ^ Maximum level of auxiliary goal nesting allowed inside this goal
} deriving (Eq, Ord)

unresolvedSpec goal = (gEnvironment goal ^. unresolvedConstants) Map.! gName goal
  
