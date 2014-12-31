import Synquid.Logic
-- import Synquid.Z3
import Synquid.Solver

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

-- main = print $ solveSMTConstraints [
    -- -- (Var "x" |>=| IntLit 0) |&| (Var "x" |<| IntLit 5)
    -- fnot $ (Var "x" |=| IntLit 5) |=>| (Var "x" |>| IntLit 0)
  -- ]
  
  -- Var "x" |>| IntLit 0, Var "x" |<| IntLit 0
  
main = do
  let quals = Map.fromList [
                  ("k", [Var "x" |>=| IntLit 0, Var "x" |<=| IntLit 0]),
                  ("l", [Var "x" |>| IntLit 0, Var "x" |<| IntLit 0, Var "x" |=| IntLit 0])]
  -- let fml = (Var "x" |=| IntLit 1) |=>| (Unknown "k" |&| Unknown "l")
  let fml = Unknown "l" |=>| Unknown "k"
  print $ optimalSolutions fml quals
  