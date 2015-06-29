module Main where

import Synquid.Logic
import Synquid.Solver
import Synquid.Program
import Synquid.Pretty
import Synquid.ConstraintGenerator
import Synquid.Synthesizer

import Control.Monad
import Control.Monad.Stream
import Control.Monad.Trans.List

-- | Parameters for template exploration
explorerParams = ExplorerParams {
  _eGuessDepth = 3,
  _scrutineeDepth = 0,
  _matchDepth = 1,
  _condDepth = 1,
  _abstractLeafs = True
}

-- | Parameters for constraint solving
solverParams = SolverParams {
  pruneQuals = True,
  -- pruneQuals = False,
  -- optimalValuationsStrategy = UnsatCoreValuations,
  optimalValuationsStrategy = MarcoValuations,    
  -- optimalValuationsStrategy = BFSValuations,    
  semanticPrune = True,
  agressivePrune = True,
  -- semanticPrune = False,
  -- agressivePrune = False,    
  candidatePickStrategy = InitializedWeakCandidate,
  -- candidatePickStrategy = WeakCandidate,
  constraintPickStrategy = SmallSpaceConstraint,
  candDoc = const empty
  }
  
synthesizeAndPrint env typ cquals tquals = do
  print $ nest 2 $ text "Spec" $+$ pretty typ
  print empty
  mProg <- synthesize explorerParams solverParams env typ cquals tquals
  case mProg of
    Nothing -> putStr "No Solution"
    Just prog -> print $ nest 2 $ text "Solution" $+$ programDoc pretty pretty (const empty) prog
  print empty
    
-- | Integer programs    
  
testApp = do
  let env = addSymbol "a" intAll .
            addSymbol "b" intAll .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = int (valInt |>| intVar "b")
  
  synthesizeAndPrint env typ [] []
  
testApp2 = do
  let env = addSymbol "a" nat .
            addSymbol "1" (int (valInt |=| IntLit 1)) .
            -- addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            -- addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            addSymbol "plus" (FunctionT "x" nat (FunctionT "y" nat (int (valInt |=| intVar "x" |+| intVar "y")))) .
            addSymbol "minus" (FunctionT "x" nat (FunctionT "y" nat (int (valInt |=| intVar "x" |-| intVar "y")))) .
            id $ emptyEnv
  let typ = int (valInt |=| intVar "a" |+| IntLit 5)
  
  synthesizeAndPrint env typ [] []
  
testLambda = do
  let env = -- addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = FunctionT "a" nat $ int (valInt |=| intVar "a" |+| IntLit 5)
  
  synthesizeAndPrint env typ [] []
  
testMax2 = do
  let env = emptyEnv
  let typ = FunctionT "x" intAll $ FunctionT "y" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y")
  
  let cq = do
      op <- [Ge, Le, Neq]
      return $ Binary op (intVar "x") (intVar "y")  
      
  synthesizeAndPrint env typ cq []
  
testMax3 = do
  let env = emptyEnv
  let typ = FunctionT "x" intAll $ FunctionT "y" intAll $ FunctionT "z" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y" |&| valInt |>=| intVar "z")
  
  let cq = do
      op <- [Ge, Le, Neq]
      return $ Binary op (intVar "x") (intVar "y")  
      
  synthesizeAndPrint env typ cq []  
   
testAbs = do
  let env =             
            addSymbol "id" (FunctionT "x" intAll (int (valInt |=| intVar "x"))) .
            addSymbol "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .
            id $ emptyEnv
  let typ = FunctionT "x" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| IntLit 0)  
  
  let cq = do
      op <- [Ge, Le, Neq]
      rhs <- [intVar "y", IntLit 0]
      return $ Binary op (intVar "x") rhs  
      
  synthesizeAndPrint env typ cq []

testAddition = do
  let env =
            addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv

  let typ = FunctionT "y" nat $ FunctionT "z" nat $ int (valInt |=| intVar "y" |+| intVar "z")
  
  let cq = do
      lhs <- [intVar "x", IntLit 0]
      op <- [Ge, Le, Neq]
      rhs <- [intVar "y", IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs
      
  synthesizeAndPrint env typ cq []
  
testCompose = do
  let env = emptyEnv
  let typ = FunctionT "f" (FunctionT "x" intAll (int $ valInt |=| intVar "x" |+| IntLit 1)) (FunctionT "y" intAll (int $ valInt |=| intVar "y" |+| IntLit 2))

  synthesizeAndPrint env typ [] []  
  
-- | List programs

testHead = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "1" (int (valInt |=| IntLit 1)) .
            id $ listEnv
  let typ = FunctionT "xs" (list $ Measure IntT "len" valList |>| IntLit 0) (int $ valInt `fin` Measure SetT "elems" (listVar "xs"))
  
  synthesizeAndPrint env typ [] []
  
testReplicate = do
  let env = -- addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            id $ listEnv

  let typ = FunctionT "n" nat (FunctionT "y" intAll (list $ Measure IntT "len" valList |=| intVar "n" |&| Measure SetT "elems" valList /<=/ SetLit [intVar "y"]))
          
  let cq = do
      op <- [Ge, Le, Neq]
      return $ Binary op (intVar "x") (IntLit 0) -- (intVar "y")
      
  synthesizeAndPrint env typ cq []
  
testLength = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            id $ listEnv

  let typ = FunctionT "l" listAll (int $ valInt |=| Measure IntT "len" (listVar "l"))

  synthesizeAndPrint env typ [] [valInt |>=| IntLit 0]
  
testAppend = do
  let env = id $ listEnv

  let typ = FunctionT "xs" listAll (FunctionT "ys" listAll (list $ Measure IntT "len" valList |=| Measure IntT "len" (listVar "xs") |+| Measure IntT "len" (listVar "ys")))

  synthesizeAndPrint env typ [] []
  
testStutter = do
  let env = id $ listEnv

  let typ = FunctionT "xs" listAll (list $ Measure IntT "len" valList |=| IntLit 2 |*| Measure IntT "len" (listVar "xs") |&| Measure SetT "elems" valList |=| Measure SetT "elems" (listVar "xs"))
  
  synthesizeAndPrint env typ [] []
  
testDrop = do
  let env = addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            id $ listEnv

  let typ = FunctionT "xs" listAll (FunctionT "n" (int $ IntLit 0 |<=| valInt |&| valInt |<=| Measure IntT "len" (listVar "xs")) (list $ Measure IntT "len" valList |=| Measure IntT "len" (listVar "xs") |-| intVar "n"))
  -- let typ = FunctionT "n" nat (FunctionT "xs" (list $ Measure IntT "len" valList |<=| intVar "n") (list $ Measure IntT "len" valList |=| Measure IntT "len" (listVar "xs") |-| intVar "n"))
  
  let cq = do
      lhs <- [intVar "x"]
      op <- [Le, Ge, Neq]
      rhs <- [IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs  
    
  synthesizeAndPrint env typ cq []  
    
main = do
  -- Integer programs
  -- putStr "\n=== app ===\n";       testApp
  -- putStr "\n=== app2 ===\n";      testApp2
  -- putStr "\n=== lambda ===\n";    testLambda
  -- putStr "\n=== max2 ===\n";      testMax2  
  -- putStr "\n=== max3 ===\n";      testMax3  
  -- putStr "\n=== abs ===\n";       testAbs  
  -- putStr "\n=== addition ===\n";  testAddition
  -- putStr "\n=== compose ===\n";   testCompose
  -- List programs
  -- putStr "\n=== head ===\n";      testHead
  -- putStr "\n=== replicate ===\n"; testReplicate
  -- putStr "\n=== length ===\n";    testLength
  -- putStr "\n=== append ===\n";    testAppend
  -- putStr "\n=== stutter ===\n";   testStutter
  putStr "\n=== drop ===\n";   testDrop
