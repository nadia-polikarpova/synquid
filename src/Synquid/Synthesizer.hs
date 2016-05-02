-- | Top-level synthesizer interface
module Synquid.Synthesizer (synthesize) where

import Synquid.Util
import Synquid.Logic
import Synquid.SolverMonad
import Synquid.HornSolver
import Synquid.Z3
import Synquid.Program
import Synquid.Pretty
import Synquid.Resolver
import Synquid.TypeConstraintSolver
import Synquid.Explorer
import Synquid.TypeChecker

import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
import Control.Monad.State
import Control.Lens
import Control.Applicative ((<$>))

import Debug.Trace

type HornSolver = FixPointSolver Z3State

-- | 'synthesize' @templGenParam consGenParams solverParams env typ templ cq tq@ : synthesize a program that has a type @typ@
-- in the typing environment @env@ and follows template @templ@,
-- using conditional qualifiers @cquals@ and type qualifiers @tquals@,
-- with parameters for template generation, constraint generation, and constraint solving @templGenParam@ @consGenParams@ @solverParams@ respectively
synthesize :: ExplorerParams -> HornSolverParams -> Goal -> [Formula] -> [Formula] -> IO (Either TypeError RProgram)
synthesize explorerParams solverParams goal cquals tquals = evalZ3State $ evalFixPointSolver reconstruction solverParams
  where
    -- | Stream of programs that satisfy the specification or type error
    reconstruction :: HornSolver (Either TypeError RProgram)
    reconstruction = let
        typingParams = TypingParams { 
                        _condQualsGen = condQuals,
                        _matchQualsGen = matchQuals,
                        _typeQualsGen = typeQuals,
                        _predQualsGen = predQuals,
                        _tcSolverLogLevel = _explorerLogLevel explorerParams
                      }
      in reconstruct explorerParams typingParams goal
      
    -- | Qualifier generator for conditionals
    condQuals :: QualsGen
    condQuals env vars = toSpace $ concat $
      map (\q -> instantiateCondQualifier q env vars) cquals 
      ++ map (\t -> extractCondFromType t env vars) (map toMonotype $ Map.elems $ allSymbols $ gEnvironment goal)

    -- | Qualifier generator for match scrutinees
    matchQuals :: QualsGen
    matchQuals env vars = toSpace $ concatMap (\dt -> extractMatchQGen dt env vars) (Map.toList $ (gEnvironment goal) ^. datatypes)

    -- | Qualifier generator for types
    typeQuals :: QualsGen
    typeQuals env vars = toSpace $ concat $
        [ extractQGenFromType False (toMonotype $ gSpec goal) env vars, 
          extractQGenFromType True (toMonotype $ gSpec goal) env vars ] -- extract from spec: both positive and negative
        ++ map (\q -> instantiateTypeQualifier q env vars) tquals -- extract from given qualifiers
        ++ map (\t -> extractQGenFromType False t env vars) (map toMonotype $ Map.elems $ allSymbols $ gEnvironment goal) -- extract from components: only negative
        
    -- | Qualifier generator for bound predicates
    predQuals :: QualsGen
    predQuals env vars = toSpace $ concatMap
      (\sch -> extractPredQGenFromType (toMonotype sch) env vars) (gSpec goal : (Map.elems $ allSymbols $ gEnvironment goal))

{- Qualifier Generators -}

-- | 'instantiateTypeQualifier ' @qual@: qualifier generator that treats free variables of @qual@ except _v as parameters
instantiateTypeQualifier :: Formula -> Environment -> [Formula] -> [Formula]
instantiateTypeQualifier (BoolLit True) _ _ = []
instantiateTypeQualifier qual env vars =
  let formals = map varName . Set.toList . Set.filter (\v -> varName v /= valueVarName) . varsOf $ qual in
  allSubstitutions env qual formals vars

-- | 'instantiateCondQualifier' @qual@: qualifier generator that treats free variables of @qual@ as parameters
instantiateCondQualifier :: Formula -> Environment -> [Formula] -> [Formula]
instantiateCondQualifier qual env vars = filter (not . isDataEq) $ -- TODO: disallowing datatype equality in conditionals, this is a bit of a hack
    allSubstitutions env qual (map varName . Set.toList . varsOf $ qual) vars
  where
    isDataEq (Binary op e1 _)
      | op == Eq || op == Neq = isData (sortOf e1)
      | otherwise = False
    isDataEq _ = False

-- | 'extractMatchQGen' @(dtName, dtDef)@: qualifier generator that generates qualifiers of the form x == ctor, for all scalar constructors ctor of datatype @dtName@
extractMatchQGen :: (Id, DatatypeDef) -> Environment -> [Formula] -> [Formula]    
extractMatchQGen (dtName, (DatatypeDef tParams _ ctors _)) env vars = concatMap extractForCtor ctors
  where
    -- Extract formulas x == @ctor@ for each x in @vars@
    extractForCtor ctor = case toMonotype $ allSymbols env Map.! ctor of
      ScalarT baseT fml -> 
        let fml' = sortSubstituteFml sortInst fml in
        allSubstitutions env fml' [valueVarName] vars
      _ -> []
    sortInst = Map.fromList $ zip tParams (map VarS distinctTypeVars)

-- | 'extractQGenFromType' @positive t@: qualifier generator that extracts all conjuncts from refinements of @t@ and treats their free variables as parameters;
-- extracts from positively or negatively occurring refinements depending on @positive@
extractQGenFromType :: Bool -> RType -> Environment -> [Formula] -> [Formula]
extractQGenFromType positive t = extractQGenFromType' positive t
  where
    sortInst =  Map.fromList $ zip (Set.toList $ typeVarsOf t) (map VarS distinctTypeVars)
    
    extractQGenFromType' :: Bool -> RType -> Environment -> [Formula] -> [Formula]
    extractQGenFromType' False  (ScalarT _ _) _ _ = []
    extractQGenFromType' True   (ScalarT baseT fml) env vars =
      let
        extractFromBase (DatatypeT _ tArgs pArgs) = concatMap (\t -> extractQGenFromType' True t env vars) tArgs
        extractFromBase _ = []
        fmls = Set.toList $ conjunctsOf (sortSubstituteFml sortInst fml)        
      in concatMap (\q -> instantiateTypeQualifier q env vars) fmls ++ extractFromBase baseT
    extractQGenFromType' False  (FunctionT _ tArg tRes) env vars = extractQGenFromType' True tArg env vars ++ extractQGenFromType' False tRes env vars
    extractQGenFromType' True   (FunctionT _ tArg tRes) env vars = extractQGenFromType' True tRes env vars
    
-- | Extract conditional qualifiers from the types of Boolean functions    
extractCondFromType :: RType -> Environment -> [Formula] -> [Formula]
extractCondFromType t@(FunctionT _ _ _) env vars = case lastType t of
  ScalarT BoolT (Binary Eq (Var BoolS v) fml) | v == valueVarName ->
    let 
      sortInst = Map.fromList $ zip (Set.toList $ typeVarsOf t) (map VarS distinctTypeVars)
      fml' = sortSubstituteFml sortInst fml 
    in allSubstitutions env fml' (map varName . Set.toList . varsOf $ fml) vars
  _ -> []
extractCondFromType _ _ _ = []

extractBoundPreds :: RSchema -> Environment -> [Formula] -> [Formula]
extractBoundPreds = extractBoundPreds' []
  where
    extractBoundPreds' :: [Id] -> RSchema -> Environment -> [Formula] -> [Formula]
    extractBoundPreds' tvs (ForallT a sch) env vars = extractBoundPreds' (a:tvs) sch env vars
    extractBoundPreds' tvs (ForallP sig sch) env vars = let
        sortInst = Map.fromList $ zip tvs (map VarS distinctTypeVars)
        resolvedNominal = allSubstitutions env (sortSubstituteFml sortInst (nominalPredApp sig)) [] [] -- no actual substitution happening, we do this to resolve the formula
      in resolvedNominal ++ extractBoundPreds' tvs sch env vars
    extractBoundPreds' _ _ _ _ = []

extractPredQGenFromType :: RType -> Environment -> [Formula] -> [Formula]
extractPredQGenFromType t env vars = extractPredQGenFromType' t
  where
    sortInst = Map.fromList $ zip (Set.toList $ typeVarsOf t) (map VarS distinctTypeVars)
    
    isParam (Var _ name) = take 1 name == dontCare
    
    (actualParams, actualsVars) = partition isParam vars
    
    extractFromRefinement fml = 
      let fml' = sortSubstituteFml sortInst fml
      in -- filter (\q -> Set.fromList actualParams `Set.isSubsetOf` varsOf q) $ -- Only take the qualifiers that use all predicate parameters (optimization)
          allSubstitutions env fml' (map varName $ Set.toList $ varsOf fml') vars
    
    extractPredQGenFromType' :: RType -> [Formula]
    extractPredQGenFromType' (ScalarT (DatatypeT dtName tArgs pArgs) fml) =
      let extractFromPArg pArg = 
            let
              pArg' = sortSubstituteFml sortInst pArg
              (formalParams, formalVars) = partition isParam (Set.toList $ varsOf pArg') 
            in allSubstitutions env pArg' (map varName formalVars) actualsVars -- Substitute the variables, but leave predicate parameters unchanged (optimization) 
      in extractFromRefinement fml ++ concatMap extractFromPArg pArgs ++ concatMap extractPredQGenFromType' tArgs
    extractPredQGenFromType' (ScalarT _ fml) = extractFromRefinement fml
    extractPredQGenFromType' (FunctionT _ tArg tRes) = extractPredQGenFromType' tArg ++ extractPredQGenFromType' tRes

-- | 'allSubstitutions' @env qual nonsubstActuals formals actuals@: 
-- all well-typed substitutions of @actuals@ for @formals@ in a qualifier @qual@
allSubstitutions :: Environment -> Formula -> [Id] -> [Formula] -> [Formula]
allSubstitutions _ (BoolLit True) _ _ = []
allSubstitutions env qual formals actuals = do
  let pickSubstForVar var = [Map.singleton var v | v <- actuals]
  subst <- Map.unions <$> mapM pickSubstForVar formals
  guard $ Set.size (Set.fromList $ Map.elems subst) == Map.size subst -- Only use substitutions with unique values
  case resolveWithSubstitution env subst qual of
    Left _ -> [] -- Variable sort mismatch
    Right resolved -> return resolved
