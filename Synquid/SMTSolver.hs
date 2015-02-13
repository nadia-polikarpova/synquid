-- | Interface to SMT solvers
module Synquid.SMTSolver where

import Synquid.Logic
import Data.Map
import Control.Applicative

class (Monad s, Applicative s) => SMTSolver s where  
  initSolver :: s ()                                                      -- ^ Initialize solver  
  isValid :: Formula -> s Bool                                            -- ^ 'isValid' @fml@: is @fml@ logically valid?
  modelOf :: [Formula] -> [Formula] -> s (Maybe (SMTModel, [Formula]))    -- ^ 'modelOf' @fmls assumptions@: a model of conjunction of @fmls@ under optional @assumptions@, if satisfiable 
                                                                          -- (together with the assumptions that were satisfied)
                                                                          
