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
import Control.Lens

-- | 'synthesize' @templGenParam consGenParams solverParams env typ templ cq tq@ : synthesize a program that has a type @typ@ 
-- in the typing environment @env@ and follows template @templ@,
-- using conditional qualifiers @cquals@ and type qualifiers @tquals@,
-- with parameters for template generation, constraint generation, and constraint solving @templGenParam@ @consGenParams@ @solverParams@ respectively
synthesize :: ExplorerParams -> SolverParams -> Goal -> [Formula] -> [Formula] -> IO (Maybe RProgram)
synthesize explorerParams solverParams goal cquals tquals = do
  ps <- evalZ3State programs
  case ps of
    [] -> return Nothing
    p : _ -> return $ Just p
    
  where
    -- | Stream of programs that satisfy the specification
    programs :: Z3State [RProgram]
    programs = let
        -- Initialize missing explorer parameters
        explorerParams' =  set condQualsGen condQuals .
                           set matchQualsGen matchQuals .
                           set typeQualsGen typeQuals
                           $ explorerParams
      in explore explorerParams' (ConstraintSolver init refine prune checkConsistency) goal
      
    init :: Z3State Candidate
    init = initialCandidate
      
    refine :: [Formula] -> QMap -> RProgram -> [Candidate] -> Z3State [Candidate]
    refine fmls qmap p cands = refineCandidates (solverParams { candDoc = candidateDoc p }) qmap fmls cands
    
    prune :: QSpace -> Z3State QSpace  
    prune = pruneQualifiers solverParams
    
    -- | Qualifier generator for conditionals
    condQuals = toSpace . foldl (|++|) (const []) (map (extractCondQGen $ gEnvironment goal) cquals)
    
    matchQuals = let env = gEnvironment goal
      in toSpace . foldl (|++|) (const []) (map (extractMatchQGen env) (Map.toList $ env ^. datatypes))
    
    -- | Qualifier generator for types
    typeQuals = toSpace . foldl (|++|) 
      (extractQGenFromType (gEnvironment goal) (toMonotype $ gSpec goal)) -- extract from spec
      (map (extractTypeQGen $ gEnvironment goal) tquals ++ -- extract from given qualifiers
      map (extractQGenFromType (gEnvironment goal) . toMonotype) (Map.elems $ allSymbols $ gEnvironment goal)) -- extract from components
    
{- Qualifier Generators -}

(|++|) gen gen' = \symbs -> nub $ gen symbs ++ gen' symbs
infixr 5  |++|

toSpace quals = QSpace quals (length quals)

-- | 'extractTypeQGen' @qual@: qualifier generator that treats free variables of @qual@ except the value variable as parameters
extractTypeQGen env (BoolLit True) _ = []
extractTypeQGen env qual ((Var s _) : syms) = 
  let (vals, other) = Set.partition (\v -> varName v == valueVarName) (varsOf qual)
  in if Set.null vals 
      then [] -- No _v in a refinement, happens sometimes
      else let (Var s' _) = if Set.null vals then error ("No _v in " ++ show qual) else Set.findMin vals
           in if complies s s'
                then allSubstitutions env qual s (Set.toList other) syms
                else []

-- | 'extractCondQGen' @qual@: qualifier generator that treats free variables of @qual@ as parameters
extractCondQGen env qual syms = allSubstitutions env qual UnknownS (Set.toList $ varsOf qual) syms

extractMatchQGen env (dtName, (Datatype n ctors _)) syms = let baseCaseCtor = head ctors 
  in case toMonotype $ allSymbols env Map.! baseCaseCtor of
    FunctionT _ _ _ -> [] -- not supported
    ScalarT baseT fml -> let s = toSort baseT in concatMap (\qual -> allSubstitutions env qual s [Var s valueVarName] syms) $ Set.toList (conjunctsOf fml)

-- | 'extractQGenFromType' @t@: qualifier generator that extracts all conjuncts from @t@ and treats their free variables as parameters
extractQGenFromType :: Environment -> RType -> [Formula] -> [Formula]
extractQGenFromType env (ScalarT baseT fml) syms = 
  let 
    fs = if isJust (sortOf fml) then Set.toList $ conjunctsOf fml else [] -- Excluding ill-types terms
    extractFromBase (DatatypeT _ tArgs) = concatMap (flip (extractQGenFromType env) syms) tArgs
    extractFromBase _ = []
  in concatMap (flip (extractTypeQGen env) syms) fs ++ extractFromBase baseT
  
extractQGenFromType env (FunctionT _ tArg tRes) syms = extractQGenFromType env tArg syms ++ extractQGenFromType env tRes syms    

-- | 'allSubstitutions' @qual valueSort vars syms@: all well-types substitutions of @syms@ for @vars@ in a qualifier @qual@ with value sort @valueSort@
allSubstitutions :: Environment -> Formula -> Sort -> [Formula] -> [Formula] -> [Formula]
allSubstitutions env qual valueSort vars syms = do
  let pickSubstForVar var = [Map.singleton (varName var) v | v <- syms, complies (fromJust $ sortOf v) (fromJust $ sortOf var)]
  subst <- Map.unions <$> mapM pickSubstForVar vars
  guard $ Set.size (Set.fromList $ Map.elems subst) == Map.size subst -- Only use substitutions with unique values (qualifiers are unlikely to have duplicate variables)      
  case resolveRefinement env valueSort (substitute subst qual) of
    Nothing -> [] -- Variable sort mismatch
    Just qual' -> return qual'
  