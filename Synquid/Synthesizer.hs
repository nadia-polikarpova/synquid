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
synthesize :: ExplorerParams Z3State -> SolverParams -> Environment -> RSchema -> [Formula] -> [Formula] -> IO (Maybe SimpleProgram)
synthesize explorerParams solverParams env (Monotype t) cquals tquals = synthesizeMonotype explorerParams solverParams env t cquals tquals
synthesize explorerParams solverParams env (Forall a sch) cquals tquals = synthesize explorerParams solverParams (addTypeVar a env) sch cquals tquals

synthesizeMonotype :: ExplorerParams Z3State -> SolverParams -> Environment -> RType -> [Formula] -> [Formula] -> IO (Maybe SimpleProgram)
synthesizeMonotype explorerParams solverParams env typ cquals tquals = do
  ps <- evalZ3State $ observeManyT 1 $ programs
  case ps of
    [] -> return Nothing
    p : _ -> return $ Just p
    
  where
    -- | Stream of programs that satisfy the specification
    programs :: LogicT Z3State SimpleProgram
    programs = let
        -- Initialize missing explorer parameters
        explorerParams' =  set solver (ConstraintSolver init refine extract) .
                           set condQualsGen condQuals .
                           set typeQualsGen typeQuals
                           $ explorerParams
      in explore explorerParams' env typ
      
    init :: Z3State Candidate
    init = initialCandidate
      
    refine :: [Clause] -> QMap -> LiquidProgram -> [Candidate] -> Z3State [Candidate]
    refine clauses qmap p cands = refineCandidates (solverParams { candDoc = candidateDoc p }) qmap clauses cands
      
    extract :: LiquidProgram -> Candidate -> Z3State SimpleProgram  
    extract p cand = fromJust <$> (runMaybeT $ extractProgram (solution cand) p)
  
    -- | Qualifier generator for conditionals
    condQuals = toSpace . foldl (|++|) (const []) (map extractCondQGen cquals)
    
    -- | Qualifier generator for types
    typeQuals = toSpace . foldl (|++|) (extractQGenFromType typ) (map extractTypeQGen tquals)  
    
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
extractQGenFromType (ScalarT _ fml) syms = let fs = Set.toList $ conjunctsOf fml in concatMap (flip extractTypeQGen syms) fs
extractQGenFromType (FunctionT _ tArg tRes) syms = extractQGenFromType tArg syms ++ extractQGenFromType tRes syms    

-- | 'allSubstitutions' @qual vars syms@: all well-types substitutions of @syms@ for @vars@ in a qualifier @qual@
allSubstitutions (BoolLit True) _ _ = []
allSubstitutions qual vars syms = do
  let pickSubstForVar var = [Map.singleton (varName var) v | v <- syms, varType v == varType var]
  subst <- Map.unions <$> mapM pickSubstForVar vars
  guard $ Set.size (Set.fromList $ Map.elems subst) == Map.size subst -- Only use substitutions with unique values (qualifiers are unlikely to have duplicate variables)      
  return $ substitute subst qual
