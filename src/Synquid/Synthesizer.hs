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
synthesize :: ExplorerParams Z3State -> SolverParams -> Environment -> RSchema -> [Formula] -> [Formula] -> IO (Maybe RProgram)
synthesize explorerParams solverParams env sch cquals tquals = do
  ps <- evalZ3State $ observeManyT 1 $ programs
  case ps of
    [] -> return Nothing
    p : _ -> return $ Just p
    
  where
    -- | Stream of programs that satisfy the specification
    programs :: LogicT Z3State RProgram
    programs = let
        -- Initialize missing explorer parameters
        explorerParams' =  set solver (ConstraintSolver init refine prune) .
                           set condQualsGen condQuals .
                           set typeQualsGen typeQuals
                           $ explorerParams
      in explore explorerParams' env sch
      
    init :: Z3State Candidate
    init = initialCandidate
      
    refine :: [Formula] -> QMap -> RProgram -> [Candidate] -> Z3State [Candidate]
    -- refine fmls qmap p cands = refineCandidates (solverParams { candDoc = candidateDoc p }) qmap fmls cands
    refine fmls qmap p cands = refineCandidates (solverParams { candDoc = pretty . solution }) qmap fmls cands
    
    prune :: QSpace -> Z3State QSpace  
    prune = pruneQualifiers solverParams
  
    -- | Qualifier generator for conditionals
    condQuals = toSpace . foldl (|++|) (const []) (map extractCondQGen cquals)
    
    -- | Qualifier generator for types
    typeQuals = toSpace . foldl (|++|) 
      (extractQGenFromType (toMonotype sch)) -- extract from spec
      (map extractTypeQGen tquals ++ -- extract from given qualifiers
      map (extractQGenFromType . toMonotype) (Map.elems $ allSymbols env)) -- extract from components
    
{- Qualifier Generators -}

(|++|) gen gen' = \symbs -> nub $ gen symbs ++ gen' symbs
infixr 5  |++|

toSpace quals = QSpace quals (length quals)

-- | 'extractTypeQGen' @qual@: qualifier generator that treats free variables of @qual@ except the value variable as parameters
extractTypeQGen qual (val : syms) = let vars = varsOf qual in
    if Set.member val vars
      then allSubstitutions qual (Set.toList $ Set.delete val (varsOf qual)) syms -- val has correct base type
      else []                                                                     -- val has wrong base type

-- | 'extractCondQGen' @qual@: qualifier generator that treats free variables of @qual@ as parameters
extractCondQGen qual syms = allSubstitutions qual (Set.toList $ varsOf qual) syms

-- | 'extractQGenFromType' @t@: qualifier generator that extracts all conjuncts from @t@ and treats their free variables as parameters
extractQGenFromType :: RType -> [Formula] -> [Formula]
extractQGenFromType (ScalarT _ tArgs fml) syms = let fs = if isJust (baseTypeOf fml) then Set.toList $ conjunctsOf fml else [] -- Excluding ill-types terms
  in concatMap (flip extractTypeQGen syms) fs ++ concatMap (flip extractQGenFromType syms) tArgs
extractQGenFromType (FunctionT _ tArg tRes) syms = extractQGenFromType tArg syms ++ extractQGenFromType tRes syms    

-- | 'allSubstitutions' @qual vars syms@: all well-types substitutions of @syms@ for @vars@ in a qualifier @qual@
allSubstitutions (BoolLit True) _ _ = []
allSubstitutions qual vars syms = do
  let syms' = map extractPrimitiveConst syms
  let pickSubstForVar var = [Map.singleton (varName var) v | v <- syms', baseTypeOf v == baseTypeOf var]
  subst <- Map.unions <$> mapM pickSubstForVar vars
  guard $ Set.size (Set.fromList $ Map.elems subst) == Map.size subst -- Only use substitutions with unique values (qualifiers are unlikely to have duplicate variables)      
  return $ substitute subst qual
  
extractPrimitiveConst v@(Var IntT name) = case reads name of
  [] -> v
  (i, _):_ -> IntLit i
extractPrimitiveConst v = v  
