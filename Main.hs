import Synquid.Util
import Synquid.Logic
import Synquid.Solver
import Synquid.SMTSolver
import Synquid.Z3
import Synquid.Program
import Synquid.Pretty

import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
import Control.Applicative

condQualsRich :: [Id] -> [Formula]  
condQualsRich vars = do
  lhs <- map Var vars ++ [IntLit 0]
  op <- [Ge, Gt, Eq, Neq]
  rhs <- map Var vars
  guard $ lhs /= rhs
  return $ Binary op lhs rhs
  
condQuals :: [Id] -> [Formula]  
condQuals vars = do
  lhs <- map Var vars
  op <- [Ge, Gt]
  rhs <- map Var vars
  guard $ lhs /= rhs
  return $ Binary op lhs rhs
  
typeQuals :: [Id] -> [Formula]  
typeQuals vars = do
  lhs <- map Var vars ++ [Var "v"]
  op <- [Ge, Gt]
  rhs <- map Var vars ++ [Var "v"]
  guard $ lhs /= rhs
  return $ Binary op lhs rhs  

varQual vars = do
  var <- map Var vars
  return $ Var "v" |=| var

extractVar t@(Binary Eq (Var v) (Var x))
  | v == "v"  =  PVar x
extractVar t =  error $ "extractVar got a non-variable type: " ++ show t 
    
testMax2Synthesize = do
  let vars = ["x", "y"]
  let quals = Map.fromList [
                ("condT", QSpace (condQualsRich vars) 0 2),
                ("condF", QSpace (condQualsRich vars) 0 2),  
                ("then", QSpace (varQual vars) 1 1),
                ("else", QSpace (varQual vars) 1 1)
              ]
  let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v")
  let fmls = [  BoolLit True |=>| (Unknown "condT" ||| Unknown "condF"),
                (Unknown "condT" |&| Unknown "then") |=>| maxType,
                (Unknown "condF" |&| Unknown "else") |=>| maxType          
                ]                
  mSol <- evalZ3State $ initSolver >> greatestFixPoint quals fmls
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> let
                  val ident = conjunction $ valuation sol ident
                  res = PIf (val "condT") (extractVar $ val "then") (extractVar $ val "else") 
                in print $ pretty res  
                                
max3 sol = let val ident = conjunction $ valuation sol ident
  in PIf (val "condT1") 
        (PIf (val "condT2") (extractVar $ val "then2") (extractVar $ val "else2")) 
        (PIf (val "condT3") (extractVar $ val "then3") (extractVar $ val "else3"))                
  
testMax3Synthesize1 = do
  let vars = ["x", "y", "z"]
  let quals = Map.fromList [
                ("condT1", QSpace (condQuals vars) 0 1),
                ("condF1", QSpace (condQuals vars) 0 1),  
                ("condT2", QSpace (condQuals vars) 0 1),
                ("condF2", QSpace (condQuals vars) 0 1),  
                ("condT3", QSpace (condQuals vars) 0 1),
                ("condF3", QSpace (condQuals vars) 0 1),  
                ("then2", QSpace (varQual vars) 1 1),
                ("else2", QSpace (varQual vars) 1 1),
                ("then3", QSpace (varQual vars) 1 1),
                ("else3", QSpace (varQual vars) 1 1)
              ]
  let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v") |&| (Var "z" |<=| Var "v")
  let fmls = [  
                BoolLit True |=>| (Unknown "condT1" ||| Unknown "condF1"),
                BoolLit True |=>| (Unknown "condT2" ||| Unknown "condF2"),
                BoolLit True |=>| (Unknown "condT3" ||| Unknown "condF3"),  
                (Unknown "condT1" |&| Unknown "condT2" |&| Unknown "then2") |=>| maxType,
                (Unknown "condT1" |&| Unknown "condF2" |&| Unknown "else2") |=>| maxType,
                (Unknown "condF1" |&| Unknown "condT3" |&| Unknown "then3") |=>| maxType,
                (Unknown "condF1" |&| Unknown "condF3" |&| Unknown "else3") |=>| maxType
                ]                
  mSol <- (evalZ3State $ initSolver >> greatestFixPoint quals fmls)
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> print $ pretty $ max3 sol
  
testMax3Synthesize2 = do
  let vars = ["x", "y", "z"]
  let quals = Map.fromList [
                ("condT1", QSpace (condQuals vars) 0 1),
                ("condF1", QSpace (condQuals vars) 0 1),  
                ("condT2", QSpace (condQuals vars) 0 1),
                ("condF2", QSpace (condQuals vars) 0 1),  
                ("condT3", QSpace (condQuals vars) 0 1),
                ("condF3", QSpace (condQuals vars) 0 1),  
                -- ("then1", QSpace [(Var "x" |<=| Var "v"), (Var "y" |<=| Var "v"), (Var "z" |<=| Var "v")] 0 2),
                -- ("else1", QSpace [(Var "x" |<=| Var "v"), (Var "y" |<=| Var "v"), (Var "z" |<=| Var "v")] 0 2),
                ("then1", QSpace (typeQuals vars) 0 2),
                ("else1", QSpace (typeQuals vars) 0 2),                
                ("then2", QSpace (varQual vars) 1 1),
                ("else2", QSpace (varQual vars) 1 1),
                ("then3", QSpace (varQual vars) 1 1),
                ("else3", QSpace (varQual vars) 1 1)
              ]
  let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v") |&| (Var "z" |<=| Var "v")
  let fmls = [
                BoolLit True |=>| (Unknown "condT1" ||| Unknown "condF1"),
                BoolLit True |=>| (Unknown "condT2" ||| Unknown "condF2"),
                BoolLit True |=>| (Unknown "condT3" ||| Unknown "condF3"),  
                (Unknown "condT1" |&| Unknown "then1") |=>| maxType,
                (Unknown "condF1" |&| Unknown "else1") |=>| maxType,
                (Unknown "condT2" |&| Unknown "then2") |=>| Unknown "then1",
                (Unknown "condF2" |&| Unknown "else2") |=>| Unknown "then1",
                (Unknown "condT3" |&| Unknown "then3") |=>| Unknown "else1",
                (Unknown "condF3" |&| Unknown "else3") |=>| Unknown "else1"
                ]                
  mSol <- (evalZ3State $ initSolver >> greatestFixPoint quals fmls)
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> print $ pretty $ max3 sol  
                      
main = testMax3Synthesize2