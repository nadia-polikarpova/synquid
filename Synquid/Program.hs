-- | Executable programs
module Synquid.Program where

import Synquid.Logic

data Program =
  PIntLit Int |
  PVar Id |
  PApp Program Program |
  PIf Formula Program Program |
  PHole Formula