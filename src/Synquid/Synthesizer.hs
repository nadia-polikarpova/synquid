-- | Top-level synthesizer interface
module Synquid.Synthesizer (
  synthesize,
  (|++|)
) where

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
                        _tcSolverLogLevel = _explorerLogLevel explorerParams
                      }
      in reconstruct explorerParams typingParams goal
      
    -- | Qualifier generator for conditionals
    condQuals :: QualsGen
    condQuals = toSpace . foldl (|++|) (const []) 
      (map extractCondQGen cquals ++
       map extractCondFromType (map toMonotype $ Map.elems $ allSymbols $ gEnvironment goal))

    matchQuals :: QualsGen
    matchQuals = toSpace . foldl (|++|) (const []) (map extractMatchQGen (Map.toList $ (gEnvironment goal) ^. datatypes))

    -- | Qualifier generator for types
    typeQuals :: QualsGen
    typeQuals = toSpace . foldl1 (|++|)
      ([extractQGenFromType False (toMonotype $ gSpec goal), extractQGenFromType True (toMonotype $ gSpec goal)] -- extract from spec: both positive and negative
        ++ map extractTypeQGen tquals -- extract from given qualifiers
        ++ map (extractQGenFromType False) (map toMonotype $ Map.elems $ allSymbols $ gEnvironment goal)) -- extract from components: only negative

{- Qualifier Generators -}

(|++|) gen gen' = \(env, symbs) -> nub $ gen (env, symbs) ++ gen' (env, symbs)
infixr 5  |++|

-- | 'extractTypeQGen' @qual@: qualifier generator that treats free variables of @qual@ except the value variable as parameters
extractTypeQGen (BoolLit True) _ = []
extractTypeQGen qual (env, (val@(Var s valName) : syms)) =
  let (vals, other) = Set.partition (\v -> varName v == valueVarName) (varsOf qual)
  in if Set.null vals
      then [] -- No _v in a refinement, happens sometimes
      else let (Var s' _) = Set.findMin vals
           in if complies s s'
                then if valName == valueVarName
                       then allSubstitutions env qual s (Set.toList other) syms
                       else map (substitute (Map.singleton valueVarName val)) $ allSubstitutions env qual s (Set.toList other) syms
                else []

-- | 'extractCondQGen' @qual@: qualifier generator that treats free variables of @qual@ as parameters
extractCondQGen qual (env, syms) = filter (not . isDataEq) $ -- TODO: disallowing datatype equality in conditionals, this is a bit of a hack
    allSubstitutions env qual AnyS (Set.toList $ varsOf qual) syms
  where
    isDataEq (Binary op e1 _)
      | op == Eq || op == Neq = isData (sortOf e1)
      | otherwise = False
    isDataEq _ = False

extractMatchQGen (_, (DatatypeDef _ _ [] _)) (_, _) = []
extractMatchQGen (dtName, (DatatypeDef _ _ ctors _)) (env, syms) = 
  let baseCaseCtor = head ctors in
  case toMonotype $ allSymbols env Map.! baseCaseCtor of
    ScalarT baseT fml -> 
      let s = toSort baseT in
      let v = Var s valueVarName in
      allSubstitutions env fml s [v] syms
    _ -> []

-- | 'extractQGenFromType' @positive t@: qualifier generator that extracts all conjuncts from refinements of @t@ and treats their free variables as parameters;
-- extracts from positively or negatively occurring refinements depending on @positive@
extractQGenFromType :: Bool -> RType -> (Environment, [Formula]) -> [Formula]
extractQGenFromType False (ScalarT _ _) _ = []
extractQGenFromType True (ScalarT baseT fml) (env, syms) =
  let
    -- fs = if isJust (sortOf fml) then Set.toList $ conjunctsOf fml else [] -- Excluding ill-types terms
    -- fs = map (sortSubstituteFml subst) $ Set.toList $ conjunctsOf fml
    fs = Set.toList $ conjunctsOf fml -- TODO: this treats polymorphic formulas incorrectly
    replaceWithValueVar pArg = let lastVar = last $ Set.toList $ varsOf pArg
      in substitute (Map.singleton (varName lastVar) (Var (sortOf lastVar) valueVarName)) pArg    
    extractFromBase (DatatypeT _ tArgs pArgs) = 
      let
        ps = Set.toList $ Set.unions (map (conjunctsOf . replaceWithValueVar) . filter (not . null . varsOf) $ pArgs)
        res = concatMap (flip extractTypeQGen (env, syms)) ps
      in concatMap (flip (extractQGenFromType True) (env, syms)) tArgs ++ res
    extractFromBase _ = []
  in concatMap (flip extractTypeQGen (env, syms)) fs ++ extractFromBase baseT
extractQGenFromType False (FunctionT _ tArg tRes) (env, syms) = extractQGenFromType True tArg (env, syms) ++ extractQGenFromType False tRes (env, syms)
extractQGenFromType True (FunctionT _ tArg tRes) (env, syms) = extractQGenFromType True tRes (env, syms)
    
-- | Extract conditional qualifiers from the types of Boolean functions    
extractCondFromType :: RType -> (Environment, [Formula]) -> [Formula]
extractCondFromType t@(FunctionT _ _ _) (env, syms) = case lastType t of
  ScalarT BoolT (Binary Eq (Var BoolS v) fml) | v == valueVarName -> allSubstitutions env fml AnyS (Set.toList $ varsOf fml) syms
  _ -> []
extractCondFromType _ _ = []  

-- | 'allSubstitutions' @qual valueSort vars syms@: all well-typed substitutions of @syms@ for @vars@ in a qualifier @qual@ with value sort @valueSort@
allSubstitutions :: Environment -> Formula -> Sort -> [Formula] -> [Formula] -> [Formula]
allSubstitutions env qual valueSort vars syms = do
  let pickSubstForVar var = [Map.singleton (varName var) v | v <- syms, complies (sortOf v) (sortOf var)]
  subst <- Map.unions <$> mapM pickSubstForVar vars
  guard $ Set.size (Set.fromList $ Map.elems subst) == Map.size subst -- Only use substitutions with unique values (qualifiers are unlikely to have duplicate variables)
  case resolveRefinement env valueSort (substitute subst qual) of
    Left _ -> [] -- Variable sort mismatch
    Right qual' -> return qual'
