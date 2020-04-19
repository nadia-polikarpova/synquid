{-# LANGUAGE TemplateHaskell, DeriveFunctor #-}

-- | Executable programs
module Synquid.Program where

import Synquid.Logic
import Synquid.Type as Type
import Synquid.Tokens
import Synquid.Util
import Synquid.Error

import Data.Maybe
import Data.Either
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
import Control.Lens as Lens
import Debug.Trace

{- Program terms -}

-- | One case inside a pattern match expression
data Case t = Case {
  constructor :: Id,      -- ^ Constructor name
  argNames :: [Id],       -- ^ Bindings for constructor arguments
  expr :: Program t       -- ^ Result of the match in this case
} deriving (Show, Eq, Ord, Functor)

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
  deriving (Show, Eq, Ord, Functor)

-- | Programs annotated with types
data Program t = Program {
  content :: BareProgram t,
  typeOf :: t
} deriving (Show, Functor)

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
    programSubstituteSymbol' (PLet x pDef pBody) = PLet x (pss pDef) (pss pBody)

-- | Convert an executable formula into a program
fmlToProgram :: Formula -> RProgram
fmlToProgram (BoolLit b) = Program (PSymbol $ show b) (ScalarT BoolT $ valBool |=| BoolLit b)
fmlToProgram (IntLit i) = Program (PSymbol $ show i) (ScalarT IntT $ valInt |=| IntLit i)
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
fmlToProgram fml@(Pred s x fs) = curriedApp fn fs --(addRefinement (fromSort s) (varRefinement x s))
  where
    fn = Program (PSymbol x) (FunctionT x AnyT AnyT {-(fromSort s)-})
    curriedApp :: RProgram -> [Formula] -> RProgram
    curriedApp p [] = p
    curriedApp p (f:fs) = curriedApp (Program (PApp p (fmlToProgram f)) AnyT {-fromSort s -}) fs

-- | Convert an executable formula into an untyped program
fmlToUProgram :: Formula -> RProgram
fmlToUProgram (BoolLit b) = Program (PSymbol $ show b) AnyT
fmlToUProgram (IntLit i) = Program (PSymbol $ show i) AnyT
fmlToUProgram (Var s x) = Program (PSymbol x) AnyT
fmlToUProgram fml@(Unary op e) = let
    p = fmlToUProgram e
    fun = Program (PSymbol $ unOpTokens Map.! op) AnyT
  in Program (PApp fun p) AnyT
fmlToUProgram fml@(Binary op e1 e2) = let
    p1 = fmlToUProgram e1
    p2 = fmlToUProgram e2
    fun1 = Program (PSymbol $ binOpTokens Map.! op) AnyT
    fun2 = Program (PApp fun1 p1) AnyT
  in Program (PApp fun2 p2) AnyT
fmlToUProgram fml@(Pred _ x fs) = curriedApp fn fs
  where
    fn = Program (PSymbol x) AnyT
    curriedApp :: RProgram -> [Formula] -> RProgram
    curriedApp p [] = p
    curriedApp p (f:fs) = curriedApp (Program (PApp p (fmlToUProgram f)) AnyT) fs
fmlToUProgram (Ite gf f1 f2) = Program (PIf gp p1 p2) AnyT
  where
    gp = fmlToUProgram gf
    p1 = fmlToUProgram f1
    p2 = fmlToUProgram f2
fmlToUProgram (Cons _ x fs) = curriedApp fn fs 
  where
    fn = Program (PSymbol x) AnyT
    curriedApp :: RProgram -> [Formula] -> RProgram
    curriedApp p [] = p
    curriedApp p (f:fs) = curriedApp (Program (PApp p (fmlToUProgram f)) AnyT) fs
fmlToUProgram (SetLit _ [])     = Program (PSymbol emptySetCtor) AnyT
fmlToUProgram (SetLit _ [f])     = Program (PApp (Program (PSymbol singletonCtor) AnyT) (fmlToUProgram f)) AnyT
fmlToUProgram (SetLit _ (f:fs)) = Program (PApp ins (curriedApp (fmlToUProgram f) fs)) AnyT
  where
    ins = Program (PSymbol insertSetCtor) AnyT
    emp = Program (PSymbol emptySetCtor) AnyT
    curriedApp :: RProgram -> [Formula] -> RProgram
    curriedApp p [] = Program (PApp p emp) AnyT
    curriedApp p (f:fs) = curriedApp (Program (PApp p (fmlToUProgram f)) AnyT) fs

-- | 'renameAsImpl' @p t@: change argument names in function type @t@ to be the same as in the abstraction @p@
renameAsImpl :: (Id -> Bool) -> UProgram -> RType -> RType
renameAsImpl isBound = renameAsImpl' Map.empty
  where
    renameAsImpl' subst (Program (PFun y pRes) _) (FunctionT x tArg tRes) = case tArg of
      ScalarT baseT fml -> FunctionT y (substituteInType isBound subst tArg) (renameAsImpl' (Map.insert x (Var (toSort baseT) y) subst) pRes tRes)
      _ -> FunctionT y (substituteInType isBound subst tArg) (renameAsImpl' subst pRes tRes)
    renameAsImpl' subst  _ t = substituteInType isBound subst t

{- Top-level definitions -}

-- | User-defined datatype representation
data DatatypeDef = DatatypeDef {
  _typeParams :: [Id],              -- ^ Type parameters
  _predParams :: [PredSig],         -- ^ Signatures of predicate parameters
  _predVariances :: [Bool],         -- ^ For each predicate parameter, whether it is contravariant
  _constructors :: [Id],            -- ^ Constructor names
  _wfMetric :: Maybe Id             -- ^ Name of the measure that serves as well founded termination metric
} deriving (Show, Eq, Ord)

makeLenses ''DatatypeDef

-- | One case in a measure definition: constructor name, arguments, and body
data MeasureCase = MeasureCase Id [Id] Formula
  deriving (Show, Eq, Ord)

type MeasureDefaults = [(Id, Sort)]

-- | User-defined measure function representation
data MeasureDef = MeasureDef {
  _inSort :: Sort,
  _outSort :: Sort,
  _definitions :: [MeasureCase],
  _constantArgs :: MeasureDefaults,
  _postcondition :: Formula
} deriving (Show, Eq, Ord)

makeLenses ''MeasureDef

type ArgMap = Map Id [Set Formula] -- All possible constant arguments of measures with multiple arguments

{- Evaluation environment -}

-- | Typing environment
data Environment = Environment {
  -- | Variable part:
  _symbols :: Map Int (Map Id RSchema),    -- ^ Variables and constants (with their refinement types), indexed by arity
  _boundTypeVars :: [Id],                  -- ^ Bound type variables
  _boundPredicates :: [PredSig],           -- ^ Argument sorts of bound abstract refinements
  _assumptions :: Set Formula,             -- ^ Unknown assumptions
  _shapeConstraints :: Map Id SType,       -- ^ For polymorphic recursive calls, the shape their types must have
  _usedScrutinees :: [RProgram],           -- ^ Program terms that has already been scrutinized
  _unfoldedVars :: Set Id,                 -- ^ In eager match mode, datatype variables that can be scrutinized
  _letBound :: Set Id,                     -- ^ Subset of symbols that are let-bound
  -- | Constant part:
  _constants :: Set Id,                    -- ^ Subset of symbols that are constants
  _datatypes :: Map Id DatatypeDef,        -- ^ Datatype definitions
  _globalPredicates :: Map Id [Sort],      -- ^ Signatures (resSort:argSorts) of module-level logic functions (measures, predicates)
  _measures :: Map Id MeasureDef,          -- ^ Measure definitions
  _typeSynonyms :: Map Id ([Id], RType),   -- ^ Type synonym definitions
  _unresolvedConstants :: Map Id RSchema   -- ^ Unresolved types of components (used for reporting specifications with macros)
} deriving (Show)

makeLenses ''Environment

instance Eq Environment where
  (==) e1 e2 = (e1 ^. symbols) == (e2 ^. symbols) && (e1 ^. assumptions) == (e2 ^. assumptions)

instance Ord Environment where
  (<=) e1 e2 = (e1 ^. symbols) <= (e2 ^. symbols) && (e1 ^. assumptions) <= (e2 ^. assumptions)

-- | Empty environment
emptyEnv = Environment {
  _symbols = Map.empty,
  _boundTypeVars = [],
  _boundPredicates = [],
  _assumptions = Set.empty,
  _shapeConstraints = Map.empty,
  _usedScrutinees = [],
  _unfoldedVars = Set.empty,
  _letBound = Set.empty,
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
lookupSymbol :: Id -> Int -> Bool -> Environment -> Maybe RSchema
lookupSymbol name a hasSet env
  | a == 0 && name == "True"                          = Just $ Monotype $ ScalarT BoolT valBool
  | a == 0 && name == "False"                         = Just $ Monotype $ ScalarT BoolT (fnot valBool)
  | a == 0 && isJust asInt                            = Just $ Monotype $ ScalarT IntT (valInt |=| IntLit (fromJust asInt))
  | a == 1 && (name `elem` Map.elems unOpTokens)      = let op = head $ Map.keys $ Map.filter (== name) unOpTokens in Just $ unOpType op
  | isBinary && hasSet                                = let ops = Map.keys $ Map.filter (== name) binOpTokens
    in Just $ binOpType $ case tail ops of
        [] -> head ops
        _  -> head $ tail ops -- To account for set operator overloading
  | isBinary                                          = let op = head $ Map.keys $ Map.filter (== name) binOpTokens in Just $ binOpType op
  | otherwise                                         = Map.lookup name (allSymbols env)
  where
    isBinary = a == 2 && (name `elem` Map.elems binOpTokens)
    asInt = asInteger name

symbolAsFormula :: Environment -> Id -> RType -> Formula
symbolAsFormula _ name t | arity t > 0
                      = error $ unwords ["symbolAsFormula: not a scalar symbol", name]
symbolAsFormula env name t
  | name == "True"    = BoolLit True
  | name == "False"   = BoolLit False
  | isJust asInt      = IntLit (fromJust asInt)
  | isConstructor     = Cons sort name []
  | otherwise         = Var sort name
  where
    isConstructor = isJust (lookupConstructor name env)
    sort = toSort (baseTypeOf t)
    asInt = asInteger name

unOpType Neg       = Monotype $ FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))
unOpType Not       = Monotype $ FunctionT "x" boolAll (bool (valBool |=| fnot (boolVar "x")))
binOpType Times     = Monotype $ FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |*| intVar "y")))
binOpType Plus      = Monotype $ FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |+| intVar "y")))
binOpType Minus     = Monotype $ FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |-| intVar "y")))
binOpType Eq        = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |=| vartVar "a" "y"))))
binOpType Neq       = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |/=| vartVar "a" "y"))))
binOpType Lt        = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |<| vartVar "a" "y"))))
binOpType Le        = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |<=| vartVar "a" "y"))))
binOpType Gt        = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |>| vartVar "a" "y"))))
binOpType Ge        = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |>=| vartVar "a" "y"))))
binOpType And       = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" |&| boolVar "y"))))
binOpType Or        = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" ||| boolVar "y"))))
binOpType Implies   = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" |=>| boolVar "y"))))
binOpType Iff       = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" |<=>| boolVar "y"))))
binOpType Union     = ForallT "a" $ Monotype $ FunctionT "x" (setAll "a") (FunctionT "y" (setAll "a") (Type.set "a" (valSet "a" |=| setVar "a" "x" /+/ setVar "a" "y")))
binOpType Intersect = ForallT "a" $ Monotype $ FunctionT "x" (setAll "a") (FunctionT "y" (setAll "a") (Type.set "a" (valSet "a" |=| setVar "a" "x" /*/ setVar "a" "y")))
binOpType Diff      = ForallT "a" $ Monotype $ FunctionT "x" (setAll "a") (FunctionT "y" (setAll "a") (Type.set "a" (valSet "a" |=| setVar "a" "x" /-/ setVar "a" "y")))
binOpType Member    = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (setAll "a") (bool (valBool |=| vartVar "a" "x" `fin` setVar "a" "y")))
binOpType Subset    = ForallT "a" $ Monotype $ FunctionT "x" (setAll "a") (FunctionT "y" (setAll "a") (bool (valBool |=| setVar "a" "x" /<=/ setVar "a" "y")))

-- | Is @name@ a constant in @env@ including built-in constants)?
isConstant name env = (name `elem` ["True", "False"]) ||
                      isJust (asInteger name) ||
                      (name `elem` Map.elems unOpTokens) ||
                      (name `elem` Map.elems binOpTokens) ||
                      (name `Set.member` (env ^. constants))

-- | 'isBound' @tv env@: is type variable @tv@ bound in @env@?
isBound :: Environment -> Id -> Bool
isBound env tv = tv `elem` env ^. boundTypeVars

addVariable :: Id -> RType -> Environment -> Environment
addVariable name t = addPolyVariable name (Monotype t)

addPolyVariable :: Id -> RSchema -> Environment -> Environment
addPolyVariable name sch e =  let n = arity (toMonotype sch) in (symbols %~ Map.insertWith Map.union n (Map.singleton name sch)) e
  where
    syms = unwords $ Map.keys $ allSymbols e
    en = Map.keys $ allSymbols e
    n = arity (toMonotype sch)
    en' = Map.keys $ allSymbols ((symbols %~ Map.insertWith Map.union n (Map.singleton name sch)) e)

-- | 'addConstant' @name t env@ : add type binding @name@ :: Monotype @t@ to @env@
addConstant :: Id -> RType -> Environment -> Environment
addConstant name t = addPolyConstant name (Monotype t)

-- | 'addPolyConstant' @name sch env@ : add type binding @name@ :: @sch@ to @env@
addPolyConstant :: Id -> RSchema -> Environment -> Environment
addPolyConstant name sch = addPolyVariable name sch . (constants %~ Set.insert name)

addLetBound :: Id -> RType -> Environment -> Environment
addLetBound name t = addVariable name t . (letBound %~ Set.insert name)

addUnresolvedConstant :: Id -> RSchema -> Environment -> Environment
addUnresolvedConstant name sch = unresolvedConstants %~ Map.insert name sch

removeVariable :: Id -> Environment -> Environment
removeVariable name env = case Map.lookup name (allSymbols env) of
  Nothing -> env
  Just sch -> over symbols (Map.insertWith (flip Map.difference) (arity $ toMonotype sch) (Map.singleton name sch)) . over constants (Set.delete name) $ env

embedContext :: Environment -> RType -> (Environment, RType)
embedContext env (LetT x tDef tBody) =
  let
    (env', tDef') = embedContext (removeVariable x env) tDef
    (env'', tBody') = embedContext env' tBody
  in (addLetBound x tDef' env'', tBody')
-- TODO: function?
embedContext env t = (env, t)

unfoldAllVariables env = over unfoldedVars (Set.union (Map.keysSet (symbolsOfArity 0 env) Set.\\ (env ^. constants))) env

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

-- | 'lookupConstructor' @ctor env@ : the name of the datatype for which @ctor@ is registered as a constructor in @env@, if any
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

allPredicates env = Map.fromList (map (\(PredSig pName argSorts resSort) -> (pName, resSort:argSorts)) (env ^. boundPredicates)) `Map.union` (env ^. globalPredicates)

-- | 'allMeasuresOf' @dtName env@ : all measure of datatype with name @dtName@ in @env@
allMeasuresOf dtName env = Map.filter (\(MeasureDef (DataS sName _) _ _ _ _) -> dtName == sName) $ env ^. measures

-- | 'allMeasurePostconditions' @baseT env@ : all nontrivial postconditions of measures of @baseT@ in case it is a datatype
allMeasurePostconditions includeQuanitifed baseT@(DatatypeT dtName tArgs _) env =
    let
      allMeasures = Map.toList $ allMeasuresOf dtName env
      isAbstract = null $ ((env ^. datatypes) Map.! dtName) ^. constructors
    in catMaybes $ map extractPost allMeasures ++
                   if isAbstract then map contentProperties allMeasures else [] ++
                   if includeQuanitifed then map elemProperties allMeasures else []
  where
    extractPost (mName, MeasureDef _ outSort _ _ fml) =
      if fml == ftrue
        then Nothing
        else Just $ substitute (Map.singleton valueVarName (Pred outSort mName [Var (toSort baseT) valueVarName])) fml

    contentProperties (mName, MeasureDef (DataS _ vars) a _ _ _) = case elemIndex a vars of
      Nothing -> Nothing
      Just i -> let (ScalarT elemT fml) = tArgs !! i -- @mName@ "returns" one of datatype's parameters: transfer the refinement onto the value of the measure
                in let
                    elemSort = toSort elemT
                    measureApp = Pred elemSort mName [Var (toSort baseT) valueVarName]
                   in Just $ substitute (Map.singleton valueVarName measureApp) fml
    contentProperties (mName, MeasureDef {}) = Nothing

    elemProperties (mName, MeasureDef (DataS _ vars) (SetS a) _ _ _) = case elemIndex a vars of
      Nothing -> Nothing
      Just i -> let (ScalarT elemT fml) = tArgs !! i -- @mName@ is a set of datatype "elements": add an axiom that every element of the set has that property
                in if fml == ftrue || fml == ffalse || not (Set.null $ unknownsOf fml)
                    then Nothing
                    else  let
                            elemSort = toSort elemT
                            scopedVar = Var elemSort "_x"
                            setVal = Pred (SetS elemSort) mName [Var (toSort baseT) valueVarName]
                          in Just $ All scopedVar (fin scopedVar setVal |=>| substitute (Map.singleton valueVarName scopedVar) fml)
    elemProperties (mName, MeasureDef {}) = Nothing

allMeasurePostconditions _ _ _ = []

typeSubstituteEnv :: TypeSubstitution -> Environment -> Environment
typeSubstituteEnv tass = over symbols (Map.map (Map.map (schemaSubstitute tass)))

-- | Insert weakest refinement
refineTop :: Environment -> SType -> RType
refineTop env (ScalarT (DatatypeT name tArgs pArgs) _) =
  let variances = env ^. (datatypes . to (Map.! name) . predVariances) in
  ScalarT (DatatypeT name (map (refineTop env) tArgs) (map (BoolLit . not) variances)) ftrue
refineTop _ (ScalarT IntT _) = ScalarT IntT ftrue
refineTop _ (ScalarT BoolT _) = ScalarT BoolT ftrue
refineTop _ (ScalarT (TypeVarT vSubst a) _) = ScalarT (TypeVarT vSubst a) ftrue
refineTop env (FunctionT x tArg tFun) = FunctionT x (refineBot env tArg) (refineTop env tFun)

-- | Insert strongest refinement
refineBot :: Environment -> SType -> RType
refineBot env (ScalarT (DatatypeT name tArgs pArgs) _) =
  let variances = env ^. (datatypes . to (Map.! name) . predVariances) in
  ScalarT (DatatypeT name (map (refineBot env) tArgs) (map BoolLit variances)) ffalse
refineBot _ (ScalarT IntT _) = ScalarT IntT ffalse
refineBot _ (ScalarT BoolT _) = ScalarT BoolT ffalse
refineBot _ (ScalarT (TypeVarT vSubst a) _) = ScalarT (TypeVarT vSubst a) ffalse
refineBot env (FunctionT x tArg tFun) = FunctionT x (refineTop env tArg) (refineBot env tFun)

{- Input language declarations -}

-- | Constructor signature: name and type
data ConstructorSig = ConstructorSig Id RType
  deriving (Show, Eq)

constructorName (ConstructorSig name _) = name

data BareDeclaration =
  TypeDecl Id [Id] RType |                                  -- ^ Type name, variables, and definition
  FuncDecl Id RSchema |                                     -- ^ Function name and signature
  DataDecl Id [Id] [(PredSig, Bool)] [ConstructorSig] |     -- ^ Datatype name, type parameters, predicate parameters, and constructor definitions
  MeasureDecl Id Sort Sort Formula [MeasureCase] MeasureDefaults Bool |     -- ^ Measure name, input sort, output sort, postcondition, definition cases, and whether this is a termination metric
  PredDecl PredSig |                                        -- ^ Module-level predicate
  QualifierDecl [Formula] |                                 -- ^ Qualifiers
  MutualDecl [Id] |                                         -- ^ Mutual recursion group
  InlineDecl Id [Id] Formula |                              -- ^ Inline predicate
  SynthesisGoal Id UProgram                                 -- ^ Name and template for the function to reconstruct
  deriving (Show, Eq)

type Declaration = Pos BareDeclaration

isSynthesisGoal (Pos _ (SynthesisGoal _ _)) = True
isSynthesisGoal _ = False

{- Misc -}

-- | Typing constraints
data Constraint = Subtype Environment RType RType Bool Id
  | WellFormed Environment RType
  | WellFormedCond Environment Formula
  | WellFormedMatchCond Environment Formula
  | WellFormedPredicate Environment [Sort] Id
  deriving (Show, Eq, Ord)

-- | Synthesis goal
data Goal = Goal {
  gName :: Id,                  -- ^ Function name
  gEnvironment :: Environment,  -- ^ Enclosing environment
  gSpec :: RSchema,             -- ^ Specification
  gImpl :: UProgram,            -- ^ Implementation template
  gDepth :: Int,                -- ^ Maximum level of auxiliary goal nesting allowed inside this goal
  gSourcePos :: SourcePos,      -- ^ Source Position,
  gSynthesize :: Bool           -- ^ Synthesis flag (false implies typechecking only)
} deriving (Show, Eq, Ord)


unresolvedType env ident = (env ^. unresolvedConstants) Map.! ident
unresolvedSpec goal = unresolvedType (gEnvironment goal) (gName goal)

-- Remove measure being typechecked from environment
filterEnv :: Environment -> Id -> Environment
filterEnv e m = Lens.set measures (Map.filterWithKey (\k _ -> k == m) (e ^. measures)) e

-- Transform a resolved measure into a program
measureProg :: Id -> MeasureDef -> UProgram
measureProg name (MeasureDef inSort outSort defs [] post) = Program {
  typeOf = t, content = PFun "arg0" Program{ content = PMatch Program{ content = PSymbol "arg0", typeOf = t } (map mCase defs), typeOf = t} }
  where
    t   = AnyT
measureProg name (MeasureDef inSort outSort defs (x:xs) post) = Program {
  typeOf = AnyT, content = PFun (fst x) (measureProg name (MeasureDef inSort outSort defs xs post))
}


-- Transform between case types
mCase :: MeasureCase -> Case RType
mCase (MeasureCase con args body) = Case{constructor = con, argNames = args, expr = fmlToUProgram body}

-- Transform measure or predicate's sort signature into a synthesis/typechecking schema
generateSchema :: Environment -> Id -> [(Maybe Id, Sort)] -> Sort -> Formula -> RSchema
-- generateSchema e name inSorts outSort post = typePolymorphic allTypeParams allPredParams name inSorts outSort post
-- predicate polymorphic only:
generateSchema e name inSorts outSort post = predPolymorphic allPredParams [] name inSorts outSort post
  where
    allPredParams = concat $ fmap ((getPredParams e) . snd) inSorts
    allTypeParams = concat $ fmap ((getTypeParams e) . snd) inSorts

getTypeParams :: Environment -> Sort -> [Id]
getTypeParams e (DataS name _) = case Map.lookup name (e ^. datatypes) of
  Just d -> d ^. typeParams
  Nothing -> []
getTypeParams e _              = []

getPredParams :: Environment -> Sort -> [PredSig]
getPredParams e (DataS name _) = case Map.lookup name (e ^. datatypes) of
  Just d -> d ^. predParams
  Nothing -> []
getPredParams e _              = []

-- Wrap function in appropriate type-polymorphic Schema skeleton
typePolymorphic :: [Id] -> [PredSig] -> Id -> [(Maybe Id, Sort)] -> Sort -> Formula -> SchemaSkeleton Formula
typePolymorphic [] ps name inSorts outSort f = predPolymorphic ps [] name inSorts outSort f
typePolymorphic (x:xs) ps name inSorts outSort f = ForallT x (typePolymorphic xs ps name inSorts outSort f)

-- Wrap function in appropriate predicate-polymorphic SchemaSkeleton
predPolymorphic :: [PredSig] -> [Id] -> Id -> [(Maybe Id, Sort)] -> Sort -> Formula -> SchemaSkeleton Formula
predPolymorphic [] ps name inSorts outSort f = genSkeleton name ps inSorts outSort f
predPolymorphic (x:xs) ps name inSorts outSort f = ForallP x (predPolymorphic xs  ((predSigName x) : ps) name inSorts outSort f)

-- Generate non-polymorphic core of schema
genSkeleton :: Id -> [Id] -> [(Maybe Id, Sort)] -> Sort -> Formula -> SchemaSkeleton Formula
genSkeleton name preds inSorts outSort post = Monotype $ uncurry 0 inSorts 
  where
    uncurry n (x:xs) = FunctionT (fromMaybe ("arg" ++ show n) (fst x)) (ScalarT (toType (snd x)) ftrue) (uncurry (n + 1) xs)
    uncurry _ [] = ScalarT outType post
    toType s = case s of
      (DataS name args) -> DatatypeT name (map fromSort args) pforms
      _ -> (baseTypeOf . fromSort) s 
    outType = (baseTypeOf . fromSort) outSort
    pforms = fmap predform preds
    predform x = Pred AnyS x []

-- Default set implementation -- Needed to typecheck measures involving sets
defaultSetType :: BareDeclaration
defaultSetType = DataDecl name typeVars preds cons
  where
    name = setTypeName
    typeVars = ["a"]
    preds = []
    cons = [empty,single,insert]
    empty = ConstructorSig emptySetCtor (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True))
    single = ConstructorSig singletonCtor (FunctionT "x" (ScalarT (TypeVarT Map.empty "a") (BoolLit True)) (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True)))
    insert = ConstructorSig insertSetCtor (FunctionT "x" (ScalarT (TypeVarT Map.empty "a") (BoolLit True)) (FunctionT "xs" (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True)) (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True))))
