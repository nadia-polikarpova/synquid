-- | Top-level synthesizer interface
module Synquid.Synthesizer (synthesize) where

import Synquid.Util
import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.SolverMonad
import Synquid.HornSolver
import Synquid.Z3
import Synquid.Pretty
import Synquid.Resolver
import Synquid.TypeConstraintSolver
import Synquid.Explorer
import Synquid.TypeChecker

import Data.Maybe
import Data.Either
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
import Control.Monad.State
import Control.Lens
import Control.Applicative ((<$>))

import Data.Time.Clock
import Data.Time.Format

import Debug.Trace

type HornSolver = FixPointSolver Z3State


-- | 'synthesize' @templGenParam consGenParams solverParams env typ templ cq tq@ : synthesize a program that has a type @typ@
-- in the typing environment @env@ and follows template @templ@,
-- using conditional qualifiers @cquals@ and type qualifiers @tquals@,
-- with parameters for template generation, constraint generation, and constraint solving @templGenParam@ @consGenParams@ @solverParams@ respectively
synthesize :: ExplorerParams -> HornSolverParams -> Goal -> [Formula] -> [Formula] -> IO (Either ErrorMessage RProgram)
synthesize explorerParams solverParams goal cquals tquals = evalZ3State $ evalFixPointSolver reconstruction solverParams
  where
    -- | Stream of programs that satisfy the specification or type error
    reconstruction :: HornSolver (Either ErrorMessage RProgram)
    reconstruction = let
        typingParams = TypingParams {
                        _condQualsGen = condQuals,
                        _matchQualsGen = matchQuals,
                        _typeQualsGen = typeQuals,
                        _predQualsGen = predQuals,
                        _tcSolverSplitMeasures = _splitMeasures explorerParams,
                        _tcSolverLogLevel = _explorerLogLevel explorerParams
                      }
      in reconstruct explorerParams typingParams goal

    -- | Qualifier generator for conditionals
    condQuals :: Environment -> [Formula] -> QSpace
    condQuals env vars = toSpace Nothing $ concat $
      map (instantiateCondQualifier False env vars) cquals ++ map (extractCondFromType env vars) (components ++ allArgTypes syntGoal)

    -- | Qualifier generator for match scrutinees
    matchQuals :: Environment -> [Formula] -> QSpace
    matchQuals env vars = toSpace (Just 1) $ concatMap (extractMatchQGen env vars) (Map.toList $ (gEnvironment goal) ^. datatypes)

    -- | Qualifier generator for types
    typeQuals :: Environment -> Formula -> [Formula] -> QSpace
    typeQuals env val vars = toSpace Nothing $ concat $
        [ extractQGenFromType False env val vars syntGoal,
          extractQGenFromType True env val vars syntGoal] -- extract from spec: both positive and negative
        ++ map (instantiateTypeQualifier env val vars) tquals -- extract from given qualifiers
        ++ map (extractQGenFromType False env val vars) components -- extract from components: only negative
        -- ++ map (extractQGenFromType True env val vars) components -- extract from components: also positive for now

    -- | Qualifier generator for bound predicates
    predQuals :: Environment -> [Formula] -> [Formula] -> QSpace
    predQuals env params vars = toSpace Nothing $
      concatMap (extractPredQGenFromType True env params vars) (syntGoal : components) ++
      if null params  -- Parameter-less predicate: also include conditional qualifiers
        then concatMap (instantiateCondQualifier False env vars) cquals ++ concatMap (extractCondFromType env vars) (components ++ allArgTypes syntGoal)
        else []

    components = componentsIn $ gEnvironment goal
    componentsIn = map toMonotype . Map.elems . allSymbols
    syntGoal = toMonotype $ gSpec goal

{- Qualifier Generators -}

-- | 'instantiateTypeQualifier ' @qual@: qualifier generator that treats free variables of @qual@ except _v as parameters
instantiateTypeQualifier :: Environment -> Formula -> [Formula] -> Formula -> [Formula]
instantiateTypeQualifier _ _ _ (BoolLit True) = []
instantiateTypeQualifier env actualVal actualVars qual =
  let (formalVals, formalVars) = partition (\v -> varName v == valueVarName) . Set.toList . varsOf $ qual in
  if length formalVals == 1
    then allSubstitutions env qual formalVars actualVars formalVals [actualVal]
    else []

-- | 'instantiateCondQualifier' @qual@: qualifier generator that treats free variables of @qual@ as parameters
instantiateCondQualifier :: Bool -> Environment -> [Formula] -> Formula -> [Formula]
instantiateCondQualifier allowDtEq env vars qual =
    let f = if allowDtEq then const True else not . isDataEq in -- TODO: disallowing datatype equality in conditionals, this is a bit of a hack
    filter f $ allSubstitutions env qual (Set.toList . varsOf $ qual) vars [] []

isDataEq (Binary op e1 _)
  | op == Eq || op == Neq = isData (sortOf e1)
  | otherwise = False
isDataEq _ = False

-- | 'extractMatchQGen' @(dtName, dtDef)@: qualifier generator that generates qualifiers of the form x == ctor, for all scalar constructors ctor of datatype @dtName@
extractMatchQGen :: Environment -> [Formula] -> (Id, DatatypeDef) -> [Formula]
extractMatchQGen env vars (dtName, (DatatypeDef tParams _ _ ctors _)) = concatMap extractForCtor ctors
  where
    -- Extract formulas x == @ctor@ for each x in @vars@
    extractForCtor ctor = case toMonotype $ allSymbols env Map.! ctor of
      ScalarT baseT fml ->
        let fml' = sortSubstituteFml sortInst fml in
        allSubstitutions env fml' [Var (sortSubstitute sortInst $ toSort baseT) valueVarName] vars [] []
      _ -> []
    sortInst = Map.fromList $ zip tParams (map VarS distinctTypeVars)

-- | 'extractQGenFromType' @positive t@: qualifier generator that extracts all conjuncts from refinements of @t@ and treats their free variables as parameters;
-- extracts from positively or negatively occurring refinements depending on @positive@
extractQGenFromType :: Bool -> Environment -> Formula -> [Formula] -> RType -> [Formula]
extractQGenFromType positive env val vars t = extractQGenFromType' positive t
  where
    sortInst =  Map.fromList $ zip (Set.toList $ typeVarsOf t) (map VarS distinctTypeVars)

    extractQGenFromType' :: Bool -> RType -> [Formula]
    extractQGenFromType' False  (ScalarT _ _) = []
    extractQGenFromType' True   (ScalarT baseT fml) =
      let
        -- Datatype: extract from tArgs and pArgs
        extractFromBase (DatatypeT dtName tArgs pArgs) =
          let (DatatypeDef _ pParams _ _ _) = (env ^. datatypes) Map.! dtName
          in concatMap (extractQGenFromType' True) tArgs ++ concat (zipWith extractQGenFromPred pParams pArgs)
        -- Otherwise: no formulas
        extractFromBase _ = []
        fmls = Set.toList $ conjunctsOf (sortSubstituteFml sortInst fml)
      in concatMap (instantiateTypeQualifier env val vars) fmls ++ extractFromBase baseT
    extractQGenFromType' False  (FunctionT _ tArg tRes) = extractQGenFromType' True tArg ++ extractQGenFromType' False tRes
    extractQGenFromType' True   (FunctionT _ tArg tRes) = extractQGenFromType' True tRes

    -- Extract type qualifiers from a predicate argument of a datatype:
    -- if the predicate has parameters, turn it into a type qualifier where the last parameter is replaced with _v
    extractQGenFromPred (PredSig _ argSorts _) fml =
      if null argSorts
        then []
        else let
              lastSort = last argSorts
              lastParam = deBrujns !! (length argSorts - 1)
              fmls = Set.toList $ conjunctsOf $ sortSubstituteFml sortInst $ substitute (Map.singleton lastParam (Var lastSort valueVarName)) fml
             in concatMap (instantiateTypeQualifier env val vars) fmls

-- | Extract conditional qualifiers from the types of Boolean functions
extractCondFromType :: Environment -> [Formula] -> RType -> [Formula]
extractCondFromType env vars t@(FunctionT _ tArg _) = case lastType t of
    ScalarT BoolT (Binary Eq (Var BoolS v) fml) | v == valueVarName ->
      let
        sortInst = Map.fromList $ zip (Set.toList $ typeVarsOf t) (map VarS distinctTypeVars)
        fml' = sortSubstituteFml sortInst fml
      in filter (not . isDataEq) $ allSubstitutions env fml' (Set.toList . varsOf $ fml') vars [] []
    _ -> []
extractCondFromType _ _ _ = []

extractPredQGenFromQual :: Bool -> Environment -> [Formula] -> [Formula] -> Formula -> [Formula]
extractPredQGenFromQual useAllArgs env actualParams actualVars fml =
  if null actualParams
    then []
    else let
        (formalVals, formalVars) = partition (\v -> varName v == valueVarName) . Set.toList . varsOf $ fml
        fmls = Set.toList $ conjunctsOf fml
        extractFromConjunct c =
          filterAllArgs $ allSubstitutions env c formalVars (init actualParams ++ actualVars) formalVals [last actualParams]
      in concatMap extractFromConjunct fmls
  where
    filterAllArgs = if useAllArgs
                      then filter (\q -> Set.fromList actualParams `Set.isSubsetOf` varsOf q)  -- Only take the qualifiers that use all predicate parameters
                      else id

extractPredQGenFromType :: Bool -> Environment -> [Formula] -> [Formula] -> RType -> [Formula]
extractPredQGenFromType useAllArgs env actualParams actualVars t = extractPredQGenFromType' t
  where
    sortInst = Map.fromList $ zip (Set.toList $ typeVarsOf t) (map VarS distinctTypeVars)

    isParam (Var _ name) = take 1 name == dontCare
    isParam _ = False

    filterAllArgs = if useAllArgs
                      then filter (\q -> Set.fromList actualParams `Set.isSubsetOf` varsOf q)  -- Only take the qualifiers that use all predicate parameters
                      else id

    -- Extract predicate qualifiers from a type refinement:
    -- only allow replacing _v with the last parameter of the refinement
    extractFromRefinement fml = if null actualParams
      then []
      else  let
              fml' = sortSubstituteFml sortInst fml
              (formalVals, formalVars) = partition (\v -> varName v == valueVarName) . Set.toList . varsOf $ fml'
              fmls = Set.toList $ conjunctsOf fml'
              extractFromConjunct c =
                filterAllArgs $ allSubstitutions env c formalVars (init actualParams ++ actualVars) formalVals [last actualParams]
            in concatMap extractFromConjunct fmls

    extractPredQGenFromType' :: RType -> [Formula]
    extractPredQGenFromType' (ScalarT (DatatypeT dtName tArgs pArgs) fml) =
      let extractFromPArg pArg =
            let
              pArg' = sortSubstituteFml sortInst pArg
              (formalParams, formalVars) = partition isParam (Set.toList $ varsOf pArg')
              -- atoms = Set.toList $ (atomsOf pArg' `Set.union` conjunctsOf pArg') -- Uncomment this to enable disjunctive qualifiers
              atoms = Set.toList $ atomsOf pArg'
              extractFromAtom atom =
                filterAllArgs $ allSubstitutions env atom formalVars (actualVars ++ actualParams) [] []
            in concatMap extractFromAtom atoms -- Substitute the variables, but leave predicate parameters unchanged (optimization)
      in extractFromRefinement fml ++ concatMap extractFromPArg pArgs ++ concatMap extractPredQGenFromType' tArgs
    extractPredQGenFromType' (ScalarT _ fml) = extractFromRefinement fml
    extractPredQGenFromType' (FunctionT _ tArg tRes) = extractPredQGenFromType' tArg ++ extractPredQGenFromType' tRes

allPredApps :: Environment -> [Formula] -> Int -> [Formula]
allPredApps _ actuals 0 = actuals
allPredApps env actuals n =
  let smallerApps = allPredApps env actuals (n - 1)
  in smallerApps ++ predAppsOneStep smallerApps
  where
    predAppsOneStep actuals = do
      (pName, sorts) <- Map.toList (env ^. globalPredicates)
      let (resSort:argSorts) = instantiateSorts sorts
      let formals = zipWith Var argSorts deBrujns
      let app = Pred resSort pName formals
      allRawSubstitutions env app formals actuals [] []

-- | 'allSubstitutions' @env qual nonsubstActuals formals actuals@:
-- all well-typed substitutions of @actuals@ for @formals@ in a qualifier @qual@
allRawSubstitutions :: Environment -> Formula -> [Formula] -> [Formula] -> [Formula] -> [Formula] -> [Formula]
allRawSubstitutions _ (BoolLit True) _ _ _ _ = []
allRawSubstitutions env qual formals actuals fixedFormals fixedActuals = do
  let tvs = Set.fromList (env ^. boundTypeVars)
  case unifySorts tvs (map sortOf fixedFormals) (map sortOf fixedActuals) of
    Left _ -> []
    Right fixedSortSubst -> do
      let fixedSubst = Map.fromList $ zip (map varName fixedFormals) fixedActuals
      let qual' = substitute fixedSubst qual
      (sortSubst, subst, _) <- foldM (go tvs) (fixedSortSubst, Map.empty, actuals) formals
      return $ substitute subst $ sortSubstituteFml sortSubst qual'
  where
    go tvs (sortSubst, subst, actuals) formal = do
      let formal' = sortSubstituteFml sortSubst formal
      actual <- actuals
      case unifySorts tvs [sortOf formal'] [sortOf actual] of
        Left _ -> mzero
        Right sortSubst' -> return (sortSubst `Map.union` sortSubst', Map.insert (varName formal) actual subst, delete actual actuals)

allSubstitutions :: Environment -> Formula -> [Formula] -> [Formula] -> [Formula] -> [Formula] -> [Formula]
allSubstitutions env qual formals actuals fixedFormals fixedActuals = do
  qual' <- allRawSubstitutions env qual formals actuals fixedFormals fixedActuals
  case resolveRefinement env qual' of
    Left _ -> [] -- Variable sort mismatch
    Right resolved -> return resolved
