-- | Top-level synthesizer interface
module Synquid.Synthesizer (
  synthesize,
  (|++|)
) where

import Synquid.Util
import Synquid.Logic
import Synquid.Solver
import Synquid.SMTSolver
import Synquid.Z3
import Synquid.Program
import Synquid.Pretty
import Synquid.Resolver
import Synquid.Explorer

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

type Z3Memo = StateT Memo Z3State

-- | 'synthesize' @templGenParam consGenParams solverParams env typ templ cq tq@ : synthesize a program that has a type @typ@
-- in the typing environment @env@ and follows template @templ@,
-- using conditional qualifiers @cquals@ and type qualifiers @tquals@,
-- with parameters for template generation, constraint generation, and constraint solving @templGenParam@ @consGenParams@ @solverParams@ respectively
synthesize :: ExplorerParams -> SolverParams -> Goal -> [Formula] -> [Formula] -> IO (Maybe RProgram)
synthesize explorerParams solverParams goal cquals tquals = do
  ps <- evalZ3State $ evalStateT programs Map.empty
  case ps of
    [] -> return Nothing
    p : _ -> return $ Just p

  where
    -- | Stream of programs that satisfy the specification
    programs :: Z3Memo [RProgram]
    programs = let
        -- Initialize missing explorer parameters
        explorerParams' =  set condQualsGen condQuals .
                           set matchQualsGen matchQuals .
                           set typeQualsGen typeQuals
                           $ explorerParams
      in explore explorerParams' (ConstraintSolver init refine prune check clearMemo getMemo putMemo) goal

    init :: Z3Memo Candidate
    init = lift $ initialCandidate

    refine :: [Formula] -> QMap -> ExtractAssumptions -> RProgram -> [Candidate] -> Z3Memo [Candidate]
    refine fmls qmap ea p cands = lift $ refineCandidates (solverParams { candDoc = candidateDoc p }) qmap ea fmls cands

    prune :: QSpace -> Z3Memo QSpace
    prune quals = lift $ pruneQualifiers solverParams quals

    check :: [Formula] -> [Candidate] -> Z3Memo [Candidate]
    check fml c = lift $ checkConsistency fml c

    clearMemo :: Z3Memo ()
    clearMemo = put Map.empty
    
    getMemo :: Z3Memo Memo
    getMemo = get
    
    putMemo :: Memo -> Z3Memo ()
    putMemo = put

    -- | Qualifier generator for conditionals
    condQuals :: QualsGen
    condQuals = toSpace . foldl (|++|) (const []) 
      (map extractCondQGen cquals ++
       map extractCondFromType (map toMonotype $ Map.elems $ allSymbols $ gEnvironment goal))

    matchQuals :: QualsGen
    matchQuals = toSpace . foldl (|++|) (const []) (map extractMatchQGen (Map.toList $ (gEnvironment goal) ^. datatypes))

    -- | Qualifier generator for types
    typeQuals :: QualsGen
    typeQuals = toSpace . foldl (|++|)
      (extractQGenFromType (toMonotype $ gSpec goal)) -- extract from spec
      (map extractTypeQGen tquals ++ -- extract from given qualifiers
      map extractQGenFromType (map toMonotype $ Map.elems $ allSymbols $ gEnvironment goal)) -- extract from components

{- Qualifier Generators -}

(|++|) gen gen' = \(env, symbs) -> nub $ gen (env, symbs) ++ gen' (env, symbs)
infixr 5  |++|

toSpace quals = QSpace quals (length quals)

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
extractCondQGen qual (env, syms) = allSubstitutions env qual UnknownS (Set.toList $ varsOf qual) syms

extractMatchQGen (dtName, (DatatypeDef _ _ ctors _)) (env, syms) = let baseCaseCtor = head ctors
  in case toMonotype $ allSymbols env Map.! baseCaseCtor of
    FunctionT _ _ _ -> [] -- not supported
    ScalarT baseT fml -> let s = toSort baseT in concatMap (\qual -> allSubstitutions env qual s [Var s valueVarName] syms) $ Set.toList (conjunctsOf fml)

-- | 'extractQGenFromType' @t@: qualifier generator that extracts all conjuncts from @t@ and treats their free variables as parameters
extractQGenFromType :: RType -> (Environment, [Formula]) -> [Formula]
extractQGenFromType (ScalarT baseT fml) (env, syms) =
  let
    -- fs = if isJust (sortOf fml) then Set.toList $ conjunctsOf fml else [] -- Excluding ill-types terms
    -- fs = map (sortSubstituteFml subst) $ Set.toList $ conjunctsOf fml
    fs = Set.toList $ conjunctsOf fml -- TODO: this treats polymorphic formulas incorrectly
    replaceWithValueVar pArg = let lastVar = last $ Set.toList $ varsOf pArg
      in substitute (Map.singleton (varName lastVar) (Var (sortOf lastVar) valueVarName)) pArg    
    extractFromBase (DatatypeT _ tArgs pArgs) = 
      let
        ps = Set.toList $ Set.unions (map (conjunctsOf . replaceWithValueVar) pArgs)
        res = concatMap (flip extractTypeQGen (env, syms)) ps
      in concatMap (flip extractQGenFromType (env, syms)) tArgs ++ res
    extractFromBase _ = []
  in concatMap (flip extractTypeQGen (env, syms)) fs ++ extractFromBase baseT
extractQGenFromType (FunctionT _ tArg tRes) (env, syms) = extractQGenFromType tArg (env, syms) ++ extractQGenFromType tRes (env, syms)
    
-- | Extract conditional qualifiers from the types of Boolean functions    
extractCondFromType :: RType -> (Environment, [Formula]) -> [Formula]
extractCondFromType t@(FunctionT _ _ _) (env, syms) = case lastType t of
  ScalarT BoolT (Binary Eq (Var BoolS v) fml) | v == valueVarName -> allSubstitutions env fml UnknownS (Set.toList $ varsOf fml) syms
  _ -> []
extractCondFromType _ _ = []  

-- | 'allSubstitutions' @qual valueSort vars syms@: all well-types substitutions of @syms@ for @vars@ in a qualifier @qual@ with value sort @valueSort@
allSubstitutions :: Environment -> Formula -> Sort -> [Formula] -> [Formula] -> [Formula]
allSubstitutions env qual valueSort vars syms = do
  let pickSubstForVar var = [Map.singleton (varName var) v | v <- syms, complies (sortOf v) (sortOf var)]
  subst <- Map.unions <$> mapM pickSubstForVar vars
  guard $ Set.size (Set.fromList $ Map.elems subst) == Map.size subst -- Only use substitutions with unique values (qualifiers are unlikely to have duplicate variables)
  case resolveRefinement env valueSort (substitute subst qual) of
    Nothing -> [] -- Variable sort mismatch
    Just qual' -> return qual'
