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
import Control.Monad.Reader

-- Conditionals

condQualsRich :: [Id] -> [Formula]  
condQualsRich vars = do
  lhs <- map Var vars ++ [IntLit 0]
  op <- [Ge, Gt, Eq, Neq]
  rhs <- map Var vars ++ [IntLit 0]
  guard $ lhs /= rhs
  return $ Binary op lhs rhs
  
condQuals :: [Id] -> [Formula]  
condQuals vars = do
  lhs <- map Var vars
  op <- [Ge, Neq]
  rhs <- map Var vars
  guard $ lhs /= rhs
  return $ Binary op lhs rhs
  
condQualsLinearEq :: Integer -> Id -> Id -> [Formula]  
condQualsLinearEq n x v = map (\i -> Var v |=| (Var x |+| IntLit i)) [0.. (2*n)] 
  -- ++ map (\i -> Var v |=| (fneg (Var x) |+| IntLit i)) [0..n]
  
-- Variables  
  
varQual res vars = do
  var <- map Var vars
  return $ Var res |=| var
  
extractVar res t@(Binary Eq (Var v) (Var x))
  | v == res  =  PVar x
extractVar res t =  error $ "extractVar got a non-variable type: " ++ show t  
  
-- Constants  

constZero res = Var res |=| IntLit 0
constOne res = Var res |=| IntLit 1

constQualInt res = map ($ res) [constZero, constOne]

extractConstInt res q = case elemIndex q (constQualInt res) of
  Just 0 -> PIntLit 0
  Just 1 -> PIntLit 1
  Nothing -> error $ "extractConstInt got a non-existing type: " ++ show q  
  
constId arg res = Var res |=| Var arg
constNeg arg res = Var res |=| fneg (Var arg)
constInc arg res = Var res |=| (Var arg |+| IntLit 1)
constDec arg res = Var res |=| (Var arg |-| IntLit 1)

constQualIntInt arg res = map (\f -> f arg res) [constId, constNeg, constInc, constDec]

extractConstIntInt arg res q = case elemIndex q (constQualIntInt arg res) of
  Just 0 -> PVar "id"
  Just 1 -> PVar "(-)"
  Just 2 -> PVar "inc"
  Just 3 -> PVar "dec"  
  Nothing -> error $ "extractConstIntInt " ++ arg ++ " " ++ res ++ " got a non-existing type: " ++ show q  
  
-- Search parameters  

params1 = SolverParams {
    pruneQuals = False,
    semanticPrune = True,
    agressivePrune = True,
    constraintPickStrategy = PickSmallestSpace,
    maxCegisIterations = -1
  }
  
-- Test cases  
    
testMax2Synthesize = do
  let vars = ["x", "y"]
  let quals = Map.fromList [
                ("condT", QSpace (condQualsRich vars) 2 Map.empty),
                ("condF", QSpace (condQualsRich vars) 2 Map.empty),  
                ("then", QSpace (varQual "v" vars) 1 Map.empty),
                ("else", QSpace (varQual "v" vars) 1 Map.empty)
              ]
  let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v")
  let fmls = [  BoolLit True |=>| (Unknown "condT" ||| Unknown "condF"),
                (Unknown "condT" |&| Unknown "then") |=>| maxType,
                (Unknown "condF" |&| Unknown "else") |=>| maxType          
                ]                
  mSol <- evalZ3State $ initSolver >> solveWithParams params1 quals fmls
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> let
                  val ident = conjunction $ valuation sol ident
                  res = PIf (val "condT") (extractVar "v" $ val "then") (extractVar "v" $ val "else") 
                in print $ pretty res  
                                
max3 sol = let val ident = conjunction $ valuation sol ident
  in PIf (val "condT1") 
        (PIf (val "condT2") (extractVar "v" $ val "then2") (extractVar "v" $ val "else2")) 
        (PIf (val "condT3") (extractVar "v" $ val "then3") (extractVar "v" $ val "else3"))                
  
testMax3Synthesize1 = do
  let vars = ["x", "y", "z"]
  let quals = Map.fromList [
                ("condT1", QSpace (condQuals vars) 2 Map.empty),
                ("condF1", QSpace (condQuals vars) 2 Map.empty),  
                ("condT2", QSpace (condQuals vars) 2 Map.empty),
                ("condF2", QSpace (condQuals vars) 2 Map.empty),  
                ("condT3", QSpace (condQuals vars) 2 Map.empty),
                ("condF3", QSpace (condQuals vars) 2 Map.empty),  
                ("then2", QSpace (varQual "v" vars) 1 Map.empty),
                ("else2", QSpace (varQual "v" vars) 1 Map.empty),
                ("then3", QSpace (varQual "v" vars) 1 Map.empty),
                ("else3", QSpace (varQual "v" vars) 1 Map.empty)
              ]
  let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v") |&| (Var "z" |<=| Var "v")
  let fmls = [  
                (Unknown "condT1" |&| Unknown "condT2" |&| Unknown "then2") |=>| maxType,
                (Unknown "condT1" |&| Unknown "condF2" |&| Unknown "else2") |=>| maxType,
                (Unknown "condF1" |&| Unknown "condT3" |&| Unknown "then3") |=>| maxType,
                (Unknown "condF1" |&| Unknown "condF3" |&| Unknown "else3") |=>| maxType,
                BoolLit True |=>| (Unknown "condT1" ||| Unknown "condF1"),
                BoolLit True |=>| (Unknown "condT2" ||| Unknown "condF2"),
                BoolLit True |=>| (Unknown "condT3" ||| Unknown "condF3")   
                ]
  mSol <- (evalZ3State $ initSolver >> solveWithParams params1 quals fmls)
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> print $ pretty $ max3 sol
  
testMax3Synthesize2 = do
  let vars = ["x", "y", "z"]
  let quals = Map.fromList [
                ("condT1", QSpace (condQuals vars) 2 Map.empty),
                ("condF1", QSpace (condQuals vars) 2 Map.empty),  
                ("condT2", QSpace (condQuals vars) 2 Map.empty),
                ("condF2", QSpace (condQuals vars) 2 Map.empty),  
                ("condT3", QSpace (condQuals vars) 2 Map.empty),
                ("condF3", QSpace (condQuals vars) 2 Map.empty),  
                -- ("then1", QSpace [(Var "x" |<=| Var "v"), (Var "y" |<=| Var "v"), (Var "z" |<=| Var "v")] 0 2),
                -- ("else1", QSpace [(Var "x" |<=| Var "v"), (Var "y" |<=| Var "v"), (Var "z" |<=| Var "v")] 0 2),
                ("then1", QSpace (condQuals $ vars ++ ["v"]) 2 Map.empty),
                ("else1", QSpace (condQuals $ vars ++ ["v"]) 2 Map.empty),                
                ("then2", QSpace (varQual "v" vars) 1 Map.empty),
                ("else2", QSpace (varQual "v" vars) 1 Map.empty),
                ("then3", QSpace (varQual "v" vars) 1 Map.empty),
                ("else3", QSpace (varQual "v" vars) 1 Map.empty)
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
  mSol <- (evalZ3State $ initSolver >> solveWithParams params1 quals fmls)
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> print $ pretty $ max3 sol  
      
pAbs sol = let val ident = conjunction $ valuation sol ident
  in PIf (val "condT") 
        (PApp (extractConstIntInt "y" "v" $ val "fun1") (extractVar "y" $ val "arg1"))                
        (PApp (extractConstIntInt "z" "v" $ val "fun2") (extractVar "z" $ val "arg2"))                
        
testAbsSynthesize1 = do
  let vars = ["x"]
  let quals = Map.fromList [
                ("condT", QSpace (condQualsRich vars) 1 Map.empty),
                ("condF", QSpace (condQualsRich vars) 1 Map.empty),
                ("arg1", QSpace (varQual "y" vars) 1 Map.empty),
                ("fun1", QSpace (constQualIntInt "y" "v") 1 Map.empty),
                ("arg2", QSpace (varQual "z" vars) 1 Map.empty),
                ("fun2", QSpace (constQualIntInt "z" "v") 1 Map.empty)
              ]
  let absType = (Var "v" |>=| IntLit 0) |&| (Var "v" |>=| Var "x")
  let fmls = [  
                BoolLit True |=>| (Unknown "condT" ||| Unknown "condF"),
                (Unknown "condT" |&| Unknown "arg1" |&| Unknown "fun1") |=>| absType,
                (Unknown "condF" |&| Unknown "arg2" |&| Unknown "fun2") |=>| absType
                ]                
  mSol <- (evalZ3State $ initSolver >> solveWithParams params1 quals fmls)
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> print $ pretty $ pAbs sol    
    
testAbsSynthesize2 = do
  let vars = ["x"]
  let quals = Map.fromList [
                ("condT", QSpace (condQualsRich vars) 1 Map.empty),
                ("condF", QSpace (condQualsRich vars) 1 Map.empty),
                ("then", QSpace (condQualsRich $ vars ++ ["v"]) 2 Map.empty),
                ("else", QSpace (condQualsRich $ vars ++ ["v"]) 2 Map.empty),
                ("arg1", QSpace (varQual "y" vars) 1 Map.empty),
                ("fun1", QSpace (constQualIntInt "y" "v") 1 Map.empty),
                ("arg2", QSpace (varQual "z" vars) 1 Map.empty),
                ("fun2", QSpace (constQualIntInt "z" "v") 1 Map.empty)
              ]
  let absType = (Var "v" |>=| IntLit 0) |&| (Var "v" |>=| Var "x")
  let fmls = [  
                BoolLit True |=>| (Unknown "condT" ||| Unknown "condF"),
                (Unknown "condT" |&| Unknown "then") |=>| absType,
                (Unknown "condF" |&| Unknown "else") |=>| absType,
                (Unknown "condT" |&| Unknown "arg1" |&| Unknown "fun1") |=>| Unknown "then",
                (Unknown "condF" |&| Unknown "arg2" |&| Unknown "fun2") |=>| Unknown "else"
                ]                
  mSol <- (evalZ3State $ initSolver >> solveWithParams params1 quals fmls)
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> print $ pretty $ pAbs sol    
    
pInc n sol = let val ident = conjunction $ valuation sol ident
  in if n == 0
      then extractVar "y0" $ val "arg1"
      else PApp (extractConstIntInt ("y" ++ show (n - 1)) ("y" ++ show n) $ val ("fun" ++ show n)) (pInc (n - 1) sol)
        
testIncSynthesize1 n = do
  let vars = ["x"]
  let quals = Map.fromList $ 
                ("arg1", QSpace (varQual "y0" vars) 1 Map.empty) : 
                    map (\i -> ("fun" ++ show i, QSpace (constQualIntInt ("y" ++ show (i - 1)) ("y" ++ show i)) 1 Map.empty)) [1..n]
  let incType = Var ("y" ++ show n) |=| (Var "x" |+| IntLit n)
  let fmls = [foldr (|&|) (Unknown "arg1") (map (\i -> Unknown ("fun" ++ show i)) [1..n])  |=>| incType]                
  mSol <- (evalZ3State $ initSolver >> solveWithParams params1 quals fmls)
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> print $ pretty $ pInc n sol
    
testIncSynthesize2 n = do
  let vars = ["x"]
  let quals = Map.fromList $ 
                [("arg1", QSpace (varQual "y0" vars) 1 Map.empty)] ++
                    map (\i -> ("arg" ++ show i, QSpace (condQualsLinearEq n "x" ("y" ++ show (i - 1))) 1 Map.empty)) [2..n] ++
                    map (\i -> ("fun" ++ show i, QSpace (constQualIntInt ("y" ++ show (i - 1)) ("y" ++ show i)) 1 Map.empty)) [1..n]
  let incType = Var ("y" ++ show n) |=| (Var "x" |+| IntLit n)
  let fmls = map (\i -> (Unknown ("fun" ++ show i) |&| Unknown ("arg" ++ show i)) |=>| Unknown ("arg" ++ show (i + 1))) [1..(n - 1)] ++
                [(Unknown ("fun" ++ show n) |&| Unknown ("arg" ++ show n)) |=>| incType]  
  mSol <- (evalZ3State $ initSolver >> solveWithParams params1 quals fmls)
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> print $ pretty $ pInc n sol
    
ins c xs = Map.fromList [(c, Set.fromList xs)]
    
testIncSynthesize3 n = do
  let vars = ["x"]
  let quals = Map.fromList $ 
                [("arg1", QSpace (varQual "y0" vars) 1 Map.empty)] ++
                    map (\i -> ("arg" ++ show i, QSpace [Var ("y" ++ show (i - 1)) |=| Var "x" |+| Parameter ("i" ++ show i)] 1 (ins ("i" ++ show i) ["x"]))) [2..n] ++ -- , "y" ++ show (i - 1)
                    map (\i -> ("fun" ++ show i, QSpace (constQualIntInt ("y" ++ show (i - 1)) ("y" ++ show i)) 1 Map.empty)) [1..n]
  let incType = Var ("y" ++ show n) |=| (Var "x" |+| IntLit n)
  let fmls = map (\i -> (Unknown ("fun" ++ show i) |&| Unknown ("arg" ++ show i)) |=>| Unknown ("arg" ++ show (i + 1))) [1..(n - 1)] ++
                [(Unknown ("fun" ++ show n) |&| Unknown ("arg" ++ show n)) |=>| incType]  
  mSol <- (evalZ3State $ initSolver >> solveWithParams params1 quals fmls)  
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> print $ pretty $ pInc n sol    
    
testCegis = do 
  mSol <- evalZ3State $ initSolver >> runReaderT (findParams 
    -- (Var "y" |=| Parameter "a" |*| Var "x" |+| Parameter "b"   |=>|   Var "y" |=| IntLit 2 |*| Var "x" |+| IntLit 3) (ins "a" ["x"])) params1
    -- (Var "y" |=| Parameter "a" |*| Var "x" |+| Parameter "b"   |=>|   Var "y" |<| IntLit 2 |*| Var "x" |+| IntLit 3) (ins "a" ["x"])) params1
    -- (Var "y" |=| Var "x" |+| Parameter "b"   |=>|   Var "y" |=| IntLit 2 |*| Var "x" |+| IntLit 3) (ins "b" ["x"])) params1
    -- (Var "y" |>| Parameter "a" |*| Var "x" |+| Parameter "b"   |=>|   Var "y" |<| IntLit 2 |*| Var "x" |+| IntLit 3) (ins "a" ["x"])) params1
    -- (Var "x" |>| Parameter "a"  |=>|  Var "y" |>| IntLit 5) (ins "a" ["x"])) params1
    (Var "y" |=| Var "x" |+| Parameter "i" |=>| Var "v" |=| Var "x" |+| IntLit 5) (ins "i" ["x"])) params1
  case mSol of
    Nothing -> putStr "No solution"
    Just sol -> print $ pretty sol
    
main = testIncSynthesize3 8

