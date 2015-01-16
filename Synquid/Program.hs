-- | Executable programs
module Synquid.Program where

import Synquid.Logic

data Program =
  PVar Id |
  PIf Formula Program Program |
  PHole Formula