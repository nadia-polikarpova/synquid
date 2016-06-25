-- | Interface to SMT solvers
module Synquid.SolverMonad where

import Synquid.Logic
import Synquid.Program
import Data.Map
import Data.Set
import Control.Applicative

class (Monad s, Applicative s) => MonadSMT s where  
  initSolver :: Environment -> s ()                                       -- ^ Initialize solver  
  isSat :: Formula -> s Bool                                              -- ^ 'isSat' @fml@: is @fml@ satisfiable?
  allUnsatCores :: Formula -> Formula -> [Formula] -> s [[Formula]]       -- ^ 'allUnsatCores' @assumption@ @mustHave@ @fmls@: all minimal unsatisfiable subsets of @fmls@ with @mustHave@, which contain @mustHave@, assuming @assumption@
  
class (Monad s, Applicative s) => MonadHorn s where
  initHornSolver :: Environment -> s Candidate                                                -- ^ Initial candidate solution
  preprocessConstraint :: Formula -> s [Formula]                                              -- ^ Convert a Horn clause to the format this solver can handle
  checkCandidates :: Bool -> [Formula] -> ExtractAssumptions ->[Candidate] -> s [Candidate]   -- ^ Check validity or consistency of constraints under current candidates
  refineCandidates :: [Formula] -> QMap -> ExtractAssumptions -> [Candidate] -> s [Candidate] -- ^ Refine current candidates to satisfy new constraints
  pruneQualifiers :: QSpace -> s QSpace                                                       -- ^ Prune redundant qualifiers
  
                                                                          
