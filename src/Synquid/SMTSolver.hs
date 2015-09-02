-- | Interface to SMT solvers
module Synquid.SMTSolver where

import Synquid.Logic
import Data.Map
import Data.Set
import Control.Applicative

data UnsatCoreResult = UCSat | UCBad [Formula] | UCGood [Formula]

class (Monad s, Applicative s) => SMTSolver s where  
  initSolver :: s ()                                                      -- ^ Initialize solver  
  isValid :: Formula -> s Bool                                            -- ^ 'isValid' @fml@: is @fml@ logically valid?
  unsatCore :: [Formula] -> [Formula] -> [Formula] -> s UnsatCoreResult
  allUnsatCores :: Formula -> Formula -> [Formula] -> s [[Formula]]       -- ^ 'allUnsatCores' @assumption@ @mustHave@ @fmls@: all minimal unsatisfiable subsets of @fmls@ with @mustHave@, which contain @mustHave@, assuming @assumption@
                                                                          
