-- | Interface to SMT solvers
module Synquid.SolverMonad where

import Synquid.Logic
import Data.Map
import Data.Set
import Control.Applicative

class (Monad s, Applicative s) => MonadSMT s where  
  initSolver :: s ()                                                      -- ^ Initialize solver  
  isValid :: Formula -> s Bool                                            -- ^ 'isValid' @fml@: is @fml@ logically valid?
  allUnsatCores :: Formula -> Formula -> [Formula] -> s [[Formula]]       -- ^ 'allUnsatCores' @assumption@ @mustHave@ @fmls@: all minimal unsatisfiable subsets of @fmls@ with @mustHave@, which contain @mustHave@, assuming @assumption@
  
class (Monad s, Applicative s) => MonadHorn s where
  initHornSolver :: s Candidate                                                      -- ^ Initial candidate solution
  refine :: [Formula] -> QMap -> ExtractAssumptions -> [Candidate] -> s [Candidate]  -- ^ Refine current list of candidates to satisfy new constraints
  pruneQualifiers :: QSpace -> s QSpace                                              -- ^ Prune redundant qualifiers
  checkConsistency :: [Formula] -> [Candidate] -> s [Candidate]                      -- ^ Check consistency of formulas under candidates
  -- csClearMemo :: s (),                                                            -- ^ Clear the memoization store
  -- csGetMemo :: s Memo,                                                            -- ^ Retrieve the memoization store
  -- csPutMemo :: Memo -> s()                                                        -- ^ Store the memoization store
  
                                                                          
