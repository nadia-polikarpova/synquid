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
import Control.Monad.Logic
import Control.Monad.Trans.Maybe
import Control.Applicative
import Control.Lens

-- | 'synthesize' @templGenParam consGenParams solverParams env typ templ cq tq@ : synthesize a program that has a type @typ@ 
-- in the typing environment @env@ and follows template @templ@,
-- using conditional qualifiers @cquals@ and type qualifiers @tquals@,
-- with parameters for template generation, constraint generation, and constraint solving @templGenParam@ @consGenParams@ @solverParams@ respectively
synthesize :: ExplorerParams -> SolverParams -> Goal -> [Formula] -> [Formula] -> IO (Maybe RProgram)
synthesize explorerParams solverParams goal cquals tquals = do
  ps <- evalZ3State $ observeManyT 1 $ programs
  case ps of
    [] -> return Nothing
    p : _ -> return $ Just p
    
  where
    -- | Stream of programs that satisfy the specification
    programs :: LogicT Z3State RProgram
    programs = let
        -- Initialize missing explorer parameters
        explorerParams' =  set condQualsGen condQuals .
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
    condQuals = toSpace . foldl (|++|) (const []) (map extractCondQGen cquals)
    
    -- | Qualifier generator for types
    typeQuals = toSpace . foldl (|++|) 
      (extractQGenFromType (toMonotype $ gSpec goal)) -- extract from spec
      (map extractTypeQGen tquals ++ -- extract from given qualifiers
      map (extractQGenFromType . toMonotype) (Map.elems $ allSymbols $ gEnvironment goal)) -- extract from components
    
{- Qualifier Generators -}

(|++|) gen gen' = \symbs -> nub $ gen symbs ++ gen' symbs
infixr 5  |++|

toSpace quals = QSpace quals (length quals)

-- | 'extractTypeQGen' @qual@: qualifier generator that treats free variables of @qual@ except the value variable as parameters
extractTypeQGen (BoolLit True) _ = []
extractTypeQGen qual ((Var s _) : syms) = let 
    (vals, other) = Set.partition (\v -> varName v == valueVarName) (varsOf qual)
    (Var s' _) = if Set.null vals then error ("No _v in " ++ show qual) else Set.findMin vals
  in if complies s s'
      then allSubstitutions qual s (Set.toList other) syms
      else []

-- | 'extractCondQGen' @qual@: qualifier generator that treats free variables of @qual@ as parameters
extractCondQGen qual syms = allSubstitutions qual UnknownS (Set.toList $ varsOf qual) syms

-- | 'extractQGenFromType' @t@: qualifier generator that extracts all conjuncts from @t@ and treats their free variables as parameters
extractQGenFromType :: RType -> [Formula] -> [Formula]
extractQGenFromType (ScalarT baseT fml) syms = 
  let 
    fs = if isJust (sortOf fml) then Set.toList $ conjunctsOf fml else [] -- Excluding ill-types terms
    extractFromBase (DatatypeT _ tArgs) = concatMap (flip extractQGenFromType syms) tArgs
    extractFromBase _ = []
  in concatMap (flip extractTypeQGen syms) fs ++ extractFromBase baseT
  
extractQGenFromType (FunctionT _ tArg tRes) syms = extractQGenFromType tArg syms ++ extractQGenFromType tRes syms    

-- | 'allSubstitutions' @qual valueSort vars syms@: all well-types substitutions of @syms@ for @vars@ in a qualifier @qual@ with value sort @valueSort@
-- allSubstitutions (BoolLit True) _ _ _ = []
allSubstitutions qual valueSort vars syms = do
  -- let syms' = map extractPrimitiveConst syms
  let pickSubstForVar var = [Map.singleton (varName var) v | v <- syms, complies (fromJust $ sortOf v) (fromJust $ sortOf var)]
  subst <- Map.unions <$> mapM pickSubstForVar vars
  guard $ Set.size (Set.fromList $ Map.elems subst) == Map.size subst -- Only use substitutions with unique values (qualifiers are unlikely to have duplicate variables)      
  case resolveRefinement valueSort (substitute subst qual) of
    Nothing -> [] -- Variable sort mismatch
    Just qual' -> return qual'
  