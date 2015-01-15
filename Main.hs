import Synquid.Util
import Synquid.Logic
import Synquid.Solver
import Synquid.SMTSolver
import Synquid.Z3
import Synquid.Pretty

import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
  
testStrengthen = do
    let quals = Map.fromList [
                ("u", QSpace [Var "x" |>| Var "y", Var "x" |>=| Var "y", Var "x" |=| Var "y"] 0 3),
                ("v", QSpace [Var "x" |<| Var "y", Var "x" |<=| Var "y"] 0 2),
                ("w", QSpace [Var "x" |<| Var "y", Var "x" |<=| Var "y"] 0 2)
              ]
    let fml = (Unknown "u" |&| Unknown "v") |=>| (Var "x" |=| Var "y")
    let sol = Map.fromList [
                ("u", Set.fromList [Var "x" |>=| Var "y"]),
                ("v", Set.fromList []),
                ("w", Set.fromList [])
              ]
    res <- evalZ3State $ initSolver >> strengthen quals fml sol
    print res
    
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
                ("condT", QSpace (condQuals vars) 0 2),
                ("condF", QSpace (condQuals vars) 0 2),  
                -- ("condT", [Var "x" |>| Var "y", Var "x" |=| Var "y"]),),
                -- ("condF", [Var "x" |<=| Var "y", Var "x" |/=| Var "y"]),
                -- ("then", ([Var "v" |=| Var "x"], 1)),
                -- ("else", ([Var "v" |=| Var "y"], 1))                
                ("then", QSpace (instantiateVars vars varQual) 1 1),
                ("else", QSpace (instantiateVars vars varQual) 1 1)
              ]
  let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v")
  let fmls = [  (Unknown "condT" |&| Unknown "then") |=>| maxType,
                (Unknown "condF" |&| Unknown "else") |=>| maxType,
                BoolLit True |=>| (Unknown "condT" ||| Unknown "condF")
                ]                
  -- let fmls = [  (Var "x" |>| Var "y" |&| Unknown "then") |=>| maxType,
                -- (fnot (Var "x" |>| Var "y") |&| Unknown "else") |=>| maxType  ]                                
  res <- evalZ3State $ initSolver >> greatestFixPoint quals fmls
  print $ pretty res 
      
main = testMaxSynthesize  