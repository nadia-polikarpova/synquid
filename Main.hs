import Synquid.Util
import Synquid.Logic
import Synquid.Solver

import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
  
testStrengthen = do
    let quals = Map.fromList [
                ("u", [Var "x" |>| Var "y", Var "x" |>=| Var "y", Var "x" |=| Var "y"]),
                ("v", [Var "x" |<| Var "y", Var "x" |<=| Var "y"]),
                ("w", [Var "x" |<| Var "y", Var "x" |<=| Var "y"])
              ]
    let fml = (Unknown "u" |&| Unknown "v") |=>| (Var "x" |=| Var "y")
    -- let sol = topSolution quals    
    let sol = Map.fromList [
                ("u", Set.fromList [Var "x" |>=| Var "y"]),
                ("v", Set.fromList []),
                ("w", Set.fromList [])
              ]
    print $ strengthen quals fml sol
    
condQuals :: [Id] -> [Formula]  
condQuals vars = do
  lhs <- map Var vars ++ [IntLit 0]
  op <- [Ge, Gt, Eq, Neq]
  rhs <- map Var vars
  guard $ lhs /= rhs
  return $ Binary op lhs rhs

varQual = AnyVar |=| Var "v"    
    
testMaxSynthesize = do
  let vars = ["x", "y"]
  let quals = Map.fromList [
                ("condT", condQuals vars),
                ("condF", condQuals vars),  
                -- ("condT", [Var "x" |>| Var "y", Var "x" |=| Var "y"]),),
                -- ("condF", [Var "x" |<=| Var "y", Var "x" |/=| Var "y"]),
                ("then", [Var "v" |=| Var "x"]),
                ("else", [Var "v" |=| Var "y"])                
                -- ("then", instantiateVars vars varQual),
                -- ("else", instantiateVars vars varQual)
              ]
  let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v")
  let fmls = [  (Unknown "condT" |&| Unknown "then") |=>| maxType,
                (Unknown "condF" |&| Unknown "else") |=>| maxType,
                BoolLit True |=>| (Unknown "condT" ||| Unknown "condF")
                ]                
  -- let fmls = [  (Var "x" |>| Var "y" |&| Unknown "then") |=>| maxType,
                -- (fnot (Var "x" |>| Var "y") |&| Unknown "else") |=>| maxType  ]                                
  print $ greatestFixPoint quals fmls
      
main = testMaxSynthesize  