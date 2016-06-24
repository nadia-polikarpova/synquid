{-# LANGUAGE TemplateHaskell, DeriveFunctor #-}

-- | Executable programs
module Synquid.Program where

import Synquid.Logic
import Synquid.Type
import Synquid.Error
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
renameAsImpl :: (Id -> Bool) -> UProgram -> RType -> RType
renameAsImpl isBound p t = renameAsImpl' Map.empty p t
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

{- Evaluation environment -}

-- | Typing environment
data Environment = Environment {
  -- | Variable part:
  _symbols :: Map Int (Map Id RSchema),    -- ^ Variables and constants (with their refinement types), indexed by arity
  _ghosts :: Map Id RType,                 -- ^ Ghost variables (to be used in embedding but not in the program)
  _boundTypeVars :: [Id],                  -- ^ Bound type variables
  _boundPredicates :: [PredSig],           -- ^ Argument sorts of bound abstract refinements
  _assumptions :: Set Formula,             -- ^ Unknown assumptions
  _letBindings :: Map Id UProgram,
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
  _letBindings = Map.empty,
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
isBound :: Environment -> Id -> Bool
isBound env tv = tv `elem` env ^. boundTypeVars

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

allPredicates env = (Map.fromList $ map (\(PredSig pName argSorts resSort) -> (pName, resSort:argSorts)) (env ^. boundPredicates)) `Map.union` (env ^. globalPredicates)

-- | 'allMeasuresOf' @dtName env@ : all measure of datatype with name @dtName@ in @env@
allMeasuresOf dtName env = Map.filter (\(MeasureDef (DataS sName _) _ _ _) -> dtName == sName) $ env ^. measures

-- | 'allMeasurePostconditions' @baseT env@ : all nontrivial postconditions of measures of @baseT@ in case it is a datatype
allMeasurePostconditions includeQuanitifed baseT@(DatatypeT dtName tArgs _) env = 
    let allMeasures = Map.toList $ allMeasuresOf dtName env 
    in catMaybes $ map extractPost allMeasures ++ 
                   map contentProperties allMeasures ++
                   if includeQuanitifed then map elemProperties allMeasures else []
  where
    extractPost (mName, MeasureDef _ outSort _ fml) = 
      if fml == ftrue
        then Nothing
        else Just $ substitute (Map.singleton valueVarName (Pred outSort mName [Var (toSort baseT) valueVarName])) fml
        
    contentProperties (mName, MeasureDef (DataS _ vars) a _ _) = case elemIndex a vars of
      Nothing -> Nothing
      Just i -> let (ScalarT elemT fml) = tArgs !! i -- @mName@ "returns" one of datatype's parameters: transfer the refinement onto the value of the measure 
                in let
                    elemSort = toSort elemT
                    measureApp = Pred elemSort mName [Var (toSort baseT) valueVarName]
                   in Just $ substitute (Map.singleton valueVarName measureApp) fml
    contentProperties (mName, MeasureDef _ _ _ _) = Nothing
        
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
  deriving (Eq)
  
constructorName (ConstructorSig name _) = name  

data BareDeclaration =
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

type Declaration = Pos BareDeclaration
            
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
  gDepth :: Int,                -- ^ Maximum level of auxiliary goal nesting allowed inside this goal
  gSourcePos :: SourcePos       -- ^ Source Position
} deriving (Eq, Ord)

unresolvedSpec goal = (gEnvironment goal ^. unresolvedConstants) Map.! gName goal
  
