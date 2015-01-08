import Synquid.Logic
-- import Synquid.Z3
import Synquid.Solver

import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

-- main = print $ solveSMTConstraints [
    -- -- (Var "x" |>=| IntLit 0) |&| (Var "x" |<| IntLit 5)
    -- fnot $ (Var "x" |=| IntLit 5) |=>| (Var "x" |>| IntLit 0)
  -- ]
  
  -- Var "x" |>| IntLit 0, Var "x" |<| IntLit 0
  
-- main = do
  -- let quals = Map.fromList [
                  -- ("k", [Var "x" |>=| IntLit 0, Var "x" |<=| IntLit 0]),
                  -- ("l", [Var "x" |>| IntLit 0, Var "x" |<| IntLit 0, Var "x" |=| IntLit 0])]
  -- -- let fml = (Var "x" |=| IntLit 1) |=>| (Unknown "k" |&| Unknown "l")
  -- let fml = Unknown "l" |=>| Unknown "k"
  -- putStr $ intercalate "\n" (map (show . flip substitute fml) $ optimalSolutions quals fml)
  
main = do
  let quals = Map.fromList [("k", [Var "x" |<=| Var "v", Var "y" |<=| Var "v", Var "x" |=| Var "v", Var "y" |=| Var "v", Var "x" |<| Var "v", Var "y" |<| Var "v", IntLit 0 |<=| Var "v", IntLit 0 |=| Var "v"])]
  let fmls = [  ((Var "x" |>| Var "y") |&| (Var "v" |=| Var "x")) |=>| Unknown "k",
                (fnot (Var "x" |>| Var "y") |&| (Var "v" |=| Var "y")) |=>| Unknown "k"]
  print $ leastFixPoint quals fmls
  
  