module Main where

import Synquid.Util
import Synquid.Logic
import Synquid.Solver
import Synquid.SMTSolver
import Synquid.Z3
import Synquid.Program
import Synquid.Pretty

import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map, (!))
import Control.Monad

import Test.HUnit

main = runTestTT allTests

allTests = TestList [gfpTests, cegisTests]

defaultParams = SolverParams {
    pruneQuals = False,
    semanticPrune = True,
    agressivePrune = True,
    candidatePickStrategy = UniformStrongCandidate,
    constraintPickStrategy = SmallSpaceConstraint,    
    maxCegisIterations = 10
  }
  
ineqalityQuals :: [Id] -> [Formula]  
ineqalityQuals vars = do
  lhs <- map Var vars
  op <- [Ge, Neq]
  rhs <- map Var vars
  guard $ lhs /= rhs
  return $ Binary op lhs rhs
  
varQual res vars = do
  var <- map Var vars
  return $ Var res |=| var  
  
{- Testing GFP solver -}

gfpTests = TestLabel "GFP" $ TestList [
  TestCase testOptimalValuations1,
  TestCase testOptimalValuations2,
  TestCase testOptimalValuations3,
  TestCase testOptimalValuationsParams1
  ]

testOptimalValuations quals fixedLhs rhs isValidRes = do 
  vals <- evalZ3State $ initSolver >> evalFixPointSolver (optimalValuations quals check) defaultParams
  assertBool (show $ text "optimalValuations: wrong answer" $+$ vsep (map pretty vals) $+$ text "for constraint" <+> pretty (fixedLhs |=>| rhs))  (isValidRes vals)
  where    
    check val = ifM (isValidFml $ fixedLhs |&| conjunction val |=>| rhs) (return $ Just $ Map.empty) (return Nothing)
  
testOptimalValuations1 = testOptimalValuations
  (ineqalityQuals ["x", "y"] ++ varQual "v" ["x", "y"])
  ftrue
  (Var "v" |>=| Var "x"  |&|  Var "v" |>=| Var "y")
  (\sols -> length sols == 5)
  
testOptimalValuations2 = testOptimalValuations
  (ineqalityQuals ["x", "y"] ++ varQual "v" ["x", "y"])
  ftrue
  (Var "x" |=| Var "y")
  (\sols -> length sols == 2)  
  
testOptimalValuations3 = testOptimalValuations
  (ineqalityQuals ["x", "y"] ++ varQual "v" ["x", "y"])
  (Var "x" |>=| Var "y")
  (Var "v" |>=| Var "x"  |&|  Var "v" |>=| Var "y")
  (\sols -> length sols == 4)  

testOptimalValuationsParams quals ins fixedLhs rhs isValidRes = do 
  vals <- evalZ3State $ initSolver >> evalFixPointSolver (optimalValuations quals check) defaultParams
  assertBool (show $ text "optimalValuations: wrong answer" $+$ vsep (map pretty vals) $+$ text "for constraint" <+> pretty (fixedLhs |=>| rhs))  (isValidRes vals)
  where    
    check val = findParams (fixedLhs |&| conjunction val |=>| rhs) ins
    
testOptimalValuationsParams1 = testOptimalValuationsParams
  (ineqalityQuals ["x", "y"] ++ [Parameter "i" |<=| Var "x" |&| Var "x" |<=| Parameter "j"])
  -- [Var "y" |>=| Var "x", Var "x" |=| Parameter "i"] -- ToDo: Bad case for CEGIS
  (mkIns "i" [])
  ftrue
  (Var "y" |>=| IntLit 5)
  (\sols -> length sols == 3)  
  
{- Testing CEGIS -}

cegisTests = TestLabel "CEGIS" $ TestList [
  TestLabel "SatStrong" $ TestCase testFindParamsSatStrong,
  TestLabel "SatWeak" $ TestCase testFindParamsSatWeak,
  TestLabel "UnsatStrong" $ TestCase testFindParamsUnsatStrong,
  TestLabel "UnsatWeak1" $ TestCase testFindParamsUnsatWeak1,
  TestLabel "UnsatWeak2" $ TestCase testFindParamsUnsatWeak2,
  TestLabel "UnsatWeak3" $ TestCase testFindParamsUnsatWeak3
  ]

testFindParams fml ins isValidRes = do 
  mSol <- evalZ3State $ initSolver >> evalFixPointSolver (findParams fml ins) defaultParams
  assertBool (show $ text "findParams: wrong answer" <+> pretty mSol <+> text "for constraint" <+> pretty fml)  (isValidRes mSol)
  
mkIns c xs = Map.fromList [(c, Set.fromList xs)]  
  
testFindParamsSatStrong = let a = 2; b = 3 in testFindParams
    (Var "y" |=| Parameter "a" |*| Var "x" |+| Parameter "b"   |=>|   Var "y" |=| IntLit a |*| Var "x" |+| IntLit b)
    (mkIns "b" ["x"])
    (\mMod -> case mMod of
                Nothing -> False
                Just mod -> mod ! "a" == a  &&  mod ! "b" == b
    )
    
testFindParamsSatWeak = let a = 2; b = 3 in testFindParams
    (Var "y" |=| Parameter "a" |*| Var "x" |+| Parameter "b"   |=>|   Var "y" |<| IntLit a |*| Var "x" |+| IntLit b)
    (mkIns "b" ["x"])
    (\mMod -> case mMod of
                Nothing -> False
                Just mod -> mod ! "a" == a  &&  mod ! "b" < b 
    )
    
testFindParamsUnsatStrong = let a = 2; b = 3 in testFindParams
    (Var "y" |=| Var "x" |+| Parameter "b"   |=>|   Var "y" |=| IntLit a |*| Var "x" |+| IntLit b)
    (mkIns "b" ["x"])
    isNothing
    
testFindParamsUnsatWeak1 = let a = 2; b = 3 in testFindParams
    (Var "y" |>| Parameter "a" |*| Var "x" |+| Parameter "b"   |=>|   Var "y" |<| IntLit a |*| Var "x" |+| IntLit b)
    (mkIns "b" ["x"])
    isNothing
    
testFindParamsUnsatWeak2 = testFindParams
    (Var "x" |>| Parameter "a"  |=>|  Var "y" |>| IntLit 5)
    (mkIns "a" ["x"])
    isNothing
    
testFindParamsUnsatWeak3 = let a = 2; b = 3 in testFindParams
    (Var "y" |=| Var "x" |+| Parameter "i" |=>| Var "v" |=| Var "x" |+| IntLit 5)
    (mkIns "i" ["x", "y"])
    isNothing
    