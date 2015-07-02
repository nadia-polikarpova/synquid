module Main where

import Synquid.Logic
import Synquid.Solver
import Synquid.Program
import Synquid.Pretty
import Synquid.Explorer
import Synquid.Synthesizer

import Control.Monad
import Control.Monad.Stream
import Control.Monad.Trans.List

-- | Parameters for template exploration
explorerParams = ExplorerParams {
  _eGuessDepth = 3,
  _scrutineeDepth = 0,
  _matchDepth = 1,
  _condDepth = 2,
  _abstractLeafs = True,
  _condQualsGen = undefined,
  _typeQualsGen = undefined,
  _solver = undefined
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
    Just prog -> print $ nest 2 $ text "Solution" $+$ programDoc pretty pretty (const empty) pretty prog
    -- Just prog -> print $ nest 2 $ text "Solution" $+$ programDoc pretty pretty pretty pretty prog
  print empty
    
{- Integer programs -}
  
testApp = do
  let env = addSymbol "a" intAll .
            addSymbol "b" intAll .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = Monotype $ int (valInt |>| intVar "b")
  
  synthesizeAndPrint env typ [] []
  
testApp2 = do
  let env = addSymbol "a" nat .
            addSymbol "1" (int (valInt |=| IntLit 1)) .
            -- addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            -- addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            addSymbol "plus" (FunctionT "x" nat (FunctionT "y" nat (int (valInt |=| intVar "x" |+| intVar "y")))) .
            addSymbol "minus" (FunctionT "x" nat (FunctionT "y" nat (int (valInt |=| intVar "x" |-| intVar "y")))) .
            id $ emptyEnv
  let typ = Monotype $ int (valInt |=| intVar "a" |+| IntLit 5)
  
  synthesizeAndPrint env typ [] []
  
testLambda = do
  let env = addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "a" nat $ int (valInt |=| intVar "a" |+| IntLit 3)
  
  synthesizeAndPrint env typ [] []
  
testMax2 = do
  let env = emptyEnv
  let typ = Monotype $ FunctionT "x" intAll $ FunctionT "y" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y")
  
  let cq = do
      op <- [Ge, Le, Neq]
      return $ Binary op (intVar "x") (intVar "y")  
      
  synthesizeAndPrint env typ cq []
  
testMax3 = do
  let env =
            -- addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "x" intAll $ FunctionT "y" intAll $ FunctionT "z" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y" |&| valInt |>=| intVar "z")
  
  let cq = do
      op <- [Ge, Le, Neq]
      return $ Binary op (intVar "x") (intVar "y")  
      
  synthesizeAndPrint env typ cq []  
   
testAbs = do
  let env =             
            addSymbol "id" (FunctionT "x" intAll (int (valInt |=| intVar "x"))) .
            addSymbol "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "x" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| IntLit 0)  
  
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

  let typ = Monotype $ FunctionT "y" nat $ FunctionT "z" nat $ int (valInt |=| intVar "y" |+| intVar "z")
  
  let cq = do
      lhs <- [intVar "x", IntLit 0]
      op <- [Ge, Le, Neq]
      rhs <- [intVar "y", IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs
      
  synthesizeAndPrint env typ cq []
    
{- Polymorphic programs -}

vart n = ScalarT (TypeVarT n)
vartAll n = vart n ftrue
vartVar n = Var (TypeVarT n)
valVart n = vartVar n valueVarName

testId = do
  let env = emptyEnv
  let typ = Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (vart "a" $ valVart "a" |=| vartVar "a" "x")
  
  synthesizeAndPrint env typ [] []
  
testConst = do
  let env = emptyEnv
  let typ = Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (vart "a" $ valVart "a" |=| vartVar "a" "x"))
  
  synthesizeAndPrint env typ [] []  
  
testCompose = do
  let env = emptyEnv
  let typ = Forall "a" $ Forall "b" $ Forall "c" $ Monotype $ FunctionT "f" (FunctionT "x" (vartAll "a") (vartAll "b")) 
              (FunctionT "g" (FunctionT "y" (vartAll "b") (vartAll "c")) 
              (FunctionT "z" (vartAll "a") (vartAll "c")))

  synthesizeAndPrint env typ [] []    
  
testPolymorphic = do
  let env = -- addPolySymbol "coerce" (Forall "a" $ Forall "b" $ Monotype $ FunctionT "x" (vartAll "a") (vartAll "b")) .            
            addPolySymbol "id" (Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (vart "a" $ valVart "a" |=| vartVar "a" "x")) .
            addSymbol "inc" (FunctionT "x" nat nat) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "x" intAll nat
  
  synthesizeAndPrint env typ [] []
  
  
{- List programs -}

listT = DatatypeT "list"
list = ScalarT listT
listAll = list ftrue
listVar = Var listT
valList = listVar valueVarName

-- | Add list datatype to the environment
addList = addDatatype "list" (Datatype ["Nil", "Cons"] (Just $ Measure IntT "len")) .
          addSymbol "Nil" (list $ Measure IntT "len" valList    |=| IntLit 0 |&|
                                  Measure SetT "elems" valList  |=| SetLit []) .
          addSymbol "Cons" (FunctionT "x" intAll (FunctionT "xs" listAll (list $  Measure IntT "len" valList |=| Measure IntT "len" (listVar "xs") |+| IntLit 1
                                                                                   |&| Measure SetT "elems" valList |=| Measure SetT "elems" (listVar "xs") /+/ SetLit [intVar "x"]
                                                                                   )))

testHead = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "1" (int (valInt |=| IntLit 1)) .
            addList $ emptyEnv
  let typ = Monotype $ FunctionT "xs" (list $ Measure IntT "len" valList |>| IntLit 0) (int $ valInt `fin` Measure SetT "elems" (listVar "xs"))
  
  synthesizeAndPrint env typ [] []
  
testReplicate = do
  let env = -- addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            addList $ emptyEnv

  let typ = Monotype $ FunctionT "n" nat (FunctionT "y" intAll (list $ Measure IntT "len" valList |=| intVar "n" |&| Measure SetT "elems" valList /<=/ SetLit [intVar "y"]))
          
  let cq = do
      op <- [Ge, Le, Neq]
      return $ Binary op (intVar "x") (IntLit 0) -- (intVar "y")
      
  synthesizeAndPrint env typ cq []
  
testLength = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            addList $ emptyEnv

  let typ = Monotype $ FunctionT "l" listAll (int $ valInt |=| Measure IntT "len" (listVar "l"))

  synthesizeAndPrint env typ [] [valInt |>=| IntLit 0]
  
testAppend = do
  let env = addList $ emptyEnv

  let typ = Monotype $ FunctionT "xs" listAll (FunctionT "ys" listAll (list $ Measure IntT "len" valList |=| Measure IntT "len" (listVar "xs") |+| Measure IntT "len" (listVar "ys")))

  synthesizeAndPrint env typ [] []
  
testStutter = do
  let env = addList $ emptyEnv

  let typ = Monotype $ FunctionT "xs" listAll (list $ Measure IntT "len" valList |=| IntLit 2 |*| Measure IntT "len" (listVar "xs") |&| Measure SetT "elems" valList |=| Measure SetT "elems" (listVar "xs"))
  
  synthesizeAndPrint env typ [] []
  
testDrop = do
  let env = addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addList $ emptyEnv

  let typ = Monotype $ FunctionT "xs" listAll (FunctionT "n" (int $ IntLit 0 |<=| valInt |&| valInt |<=| Measure IntT "len" (listVar "xs")) (list $ Measure IntT "len" valList |=| Measure IntT "len" (listVar "xs") |-| intVar "n"))
  -- let typ = Monotype $ FunctionT "n" nat (FunctionT "xs" (list $ Measure IntT "len" valList |<=| intVar "n") (list $ Measure IntT "len" valList |=| Measure IntT "len" (listVar "xs") |-| intVar "n"))
  
  let cq = do
      lhs <- [intVar "x"]
      op <- [Le, Ge, Neq]
      rhs <- [IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs  
    
  synthesizeAndPrint env typ cq []  
  
testDelete = do
  let env = addList $ emptyEnv

  let typ = Monotype $ FunctionT "x" intAll (FunctionT "xs" listAll (list $ Measure SetT "elems" valList |=| Measure SetT "elems" (listVar "xs") /-/ SetLit [intVar "x"]))
      
  synthesizeAndPrint env typ [intVar "x" |=| intVar "y"] []  
  
{- Tree programs -}

treeT = DatatypeT "tree"
tree = ScalarT treeT
treeAll = tree ftrue
treeVar = Var treeT
valTree = treeVar valueVarName

-- | Add tree datatype to the environment
addTree = addDatatype "tree" (Datatype ["Empty", "Node"] (Just $ Measure IntT "size")) .
          addSymbol "Empty" (tree $  
            Measure IntT "size" valTree  |=| IntLit 0
            |&| Measure SetT "telems" valTree  |=| SetLit []
            ) .
          addSymbol "Node" (FunctionT "x" intAll (FunctionT "l" treeAll (FunctionT "r" treeAll (tree $  
            Measure IntT "size" valTree |=| Measure IntT "size" (treeVar "l") |+| Measure IntT "size" (treeVar "r") |+| IntLit 1
            |&| Measure SetT "telems" valTree |=| Measure SetT "telems" (treeVar "l") /+/ Measure SetT "telems" (treeVar "r") /+/ SetLit [intVar "x"]
            ))))            
            
testRoot = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "1" (int (valInt |=| IntLit 1)) .
            addTree $ emptyEnv
  let typ = Monotype $ FunctionT "t" (tree $ Measure IntT "size" valTree |>| IntLit 0) (int $ valInt `fin` Measure SetT "telems" (treeVar "t"))
  
  synthesizeAndPrint env typ [] []
            
              
testTreeGen = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "1" (int (valInt |=| IntLit 0)) .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addTree $ emptyEnv

  let typ = Monotype $ FunctionT "n" nat (tree $ Measure IntT "size" valTree |=| intVar "n")
  
  let cq = do
      op <- [Eq]      
      return $ Binary op (intVar "x") (intVar "y")
  
  synthesizeAndPrint env typ cq []
  
testTreeSize = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "1" (int (valInt |=| IntLit 0)) .
            -- addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            -- addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            addSymbol "plus" (FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |+| intVar "y")))) .
            -- addSymbol "minus" (FunctionT "x" nat (FunctionT "y" nat (int (valInt |=| intVar "x" |-| intVar "y")))) .            
            addTree $ emptyEnv

  let typ = Monotype $ FunctionT "t" treeAll (int $ valInt |=| Measure IntT "size" (treeVar "t"))

  synthesizeAndPrint env typ [] []
            
testFlatten = do
  -- let env = addSymbol "append" (FunctionT "xs" listAll (FunctionT "ys" listAll (list $ Measure SetT "elems" valList |=| Measure SetT "elems" (listVar "xs") /+/ Measure SetT "elems" (listVar "ys")))) .
            -- addList $ addTree $ emptyEnv

  -- let typ = Monotype $ FunctionT "t" treeAll (list $ Measure SetT "elems" valList |=| Measure SetT "telems" (treeVar "t"))
  
  let env = addSymbol "append" (FunctionT "xs" listAll (FunctionT "ys" listAll (list $ Measure IntT "len" valList |=| Measure IntT "len" (listVar "xs") |+| Measure IntT "len" (listVar "ys")))) .
            addList $ addTree $ emptyEnv

  let typ = Monotype $ FunctionT "t" treeAll (list $ Measure IntT "len" valList |=| Measure IntT "size" (treeVar "t"))
    
  synthesizeAndPrint env typ [] []
            
  
    
main = do
  -- Integer programs
  -- putStr "\n=== app ===\n";       testApp
  -- putStr "\n=== app2 ===\n";      testApp2  
  -- putStr "\n=== lambda ===\n";    testLambda
  -- putStr "\n=== max2 ===\n";      testMax2  
  -- putStr "\n=== max3 ===\n";      testMax3
  -- putStr "\n=== abs ===\n";       testAbs  
  -- putStr "\n=== addition ===\n";  testAddition
  -- Polymorphic programs
  -- putStr "\n=== id ===\n";       testId
  -- putStr "\n=== const ===\n";       testConst
  -- putStr "\n=== compose ===\n";   testCompose  
  putStr "\n=== polymorphic ===\n";   testPolymorphic
  -- List programs
  -- putStr "\n=== head ===\n";      testHead
  -- putStr "\n=== replicate ===\n"; testReplicate
  -- putStr "\n=== length ===\n";    testLength
  -- putStr "\n=== append ===\n";    testAppend
  -- putStr "\n=== stutter ===\n";   testStutter
  -- putStr "\n=== drop ===\n";   testDrop
  -- putStr "\n=== delete ===\n";   testDelete
  -- Tree programs
  -- putStr "\n=== root ===\n";      testRoot
  -- putStr "\n=== tree gen ===\n";     testTreeGen
  -- putStr "\n=== tree size ===\n";     testTreeSize
  -- putStr "\n=== flatten ===\n";      testFlatten
