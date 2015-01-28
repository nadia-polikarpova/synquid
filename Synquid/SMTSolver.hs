-- | Interface to SMT solvers
module Synquid.SMTSolver where

import Synquid.Logic
import Data.Map
import Control.Applicative

class (Monad s, Applicative s) => SMTSolver s where  
  initSolver :: s ()                          -- ^ Initialize solver  
  isValid :: Formula -> s Bool                -- ^ 'isValid' @fml@: is @fml@ logically valid?
  modelOf :: Formula -> s (Maybe SMTModel)    -- ^ 'modelOf' @fml@: a model of @fml@, is satisfiable