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
  _enableFix = True,
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
  let env = addVariable "a" intAll .
            addVariable "b" intAll .
            addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = Monotype $ int (valInt |>| intVar "b")
  
  synthesizeAndPrint env typ [] []
  
testApp2 = do
  let env = addVariable "a" nat .
            addConstant "1" (int (valInt |=| IntLit 1)) .
            -- addConstant "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            -- addConstant "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            addConstant "plus" (FunctionT "x" nat (FunctionT "y" nat (int (valInt |=| intVar "x" |+| intVar "y")))) .
            addConstant "minus" (FunctionT "x" nat (FunctionT "y" nat (int (valInt |=| intVar "x" |-| intVar "y")))) .
            id $ emptyEnv
  let typ = Monotype $ int (valInt |=| intVar "a" |+| IntLit 5)
  
  synthesizeAndPrint env typ [] []
  
testLambda = do
  let env = addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
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
            -- addConstant "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "x" intAll $ FunctionT "y" intAll $ FunctionT "z" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y" |&| valInt |>=| intVar "z")
  
  let cq = do
      op <- [Ge, Le, Neq]
      return $ Binary op (intVar "x") (intVar "y")  
      
  synthesizeAndPrint env typ cq []  
   
testAbs = do
  let env =             
            addConstant "id" (FunctionT "x" intAll (int (valInt |=| intVar "x"))) .
            addConstant "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "x" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| IntLit 0)  
  
  let cq = do
      op <- [Ge, Le, Neq]
      rhs <- [intVar "y", IntLit 0]
      return $ Binary op (intVar "x") rhs  
      
  synthesizeAndPrint env typ cq []

testAddition = do
  let env =
            addConstant "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
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
  let env = -- addPolyConstant "coerce" (Forall "a" $ Forall "b" $ Monotype $ FunctionT "x" (vartAll "a") (vartAll "b")) .            
            addPolyConstant "id" (Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (vart "a" $ valVart "a" |=| vartVar "a" "x")) .
            addConstant "inc" (FunctionT "x" nat nat) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "x" intAll nat
  
  synthesizeAndPrint env typ [] []
  
  
{- List programs -}

listT = DatatypeT "list"
list = ScalarT listT [vartAll "a"]
listAll = list ftrue
listVar = Var listT
valList = listVar valueVarName

intlist = ScalarT listT [intAll]
natlist = ScalarT listT [nat]

mLen = Measure IntT "len"
mElems = Measure (SetT (TypeVarT "a")) "elems"

-- | Add list datatype to the environment
addList = addDatatype "list" (Datatype 1 ["Nil", "Cons"] (Just $ mLen)) .
          addPolyConstant "Nil" (Forall "a" $ Monotype $ list $ mLen valList |=| IntLit 0
                                                            |&| mElems valList  |=| SetLit (TypeVarT "a") []
                                ) .
          addPolyConstant "Cons" (Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "xs" listAll (list $ mLen valList |=| mLen (listVar "xs") |+| IntLit 1
                                                                                                                     |&| mElems valList |=| mElems (listVar "xs") /+/ SetLit (TypeVarT "a") [vartVar "a" "x"]
                                                                                   )))
                                                                                                                                                                      
testHead = do
  let env = addList $ emptyEnv
  let typ = Forall "a" $ Monotype $ FunctionT "xs" (list $ mLen valList |>| IntLit 0) (vart "a" $ valVart "a" `fin` mElems (listVar "xs"))
  
  synthesizeAndPrint env typ [] []
  
testReplicate = do
  let env = 
            addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            addList $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "n" nat (FunctionT "y" (vartAll "a") (ScalarT listT [vart "a" $ valVart "a" |=| vartVar "a" "y"] $ mLen valList |=| intVar "n"))
          
  let cq = do
      op <- [Ge, Le, Neq]
      return $ Binary op (intVar "x") (IntLit 0) -- (intVar "y")
      
  synthesizeAndPrint env typ cq []
  
testLength = do
  let env = addConstant "0" (int (valInt |=| IntLit 0)) .
            addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            addList $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "l" listAll (int $ valInt |=| mLen (listVar "l"))

  synthesizeAndPrint env typ [] [valInt |>=| IntLit 0]
  
testAppend = do
  let env = addList $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "xs" listAll (FunctionT "ys" listAll (list $ mLen valList |=| mLen (listVar "xs") |+| mLen (listVar "ys")))

  synthesizeAndPrint env typ [] []
  
testStutter = do
  let env = addList $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "xs" listAll (list $ mLen valList |=| IntLit 2 |*| mLen (listVar "xs") |&| mElems valList |=| mElems (listVar "xs"))
  
  synthesizeAndPrint env typ [] []
  
testDrop = do
  let env = addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addList $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "xs" listAll (FunctionT "n" (int $ IntLit 0 |<=| valInt |&| valInt |<=| mLen (listVar "xs")) (list $ mLen valList |=| mLen (listVar "xs") |-| intVar "n"))
  
  let cq = do
      lhs <- [intVar "x"]
      op <- [Le, Ge, Neq]
      rhs <- [IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs  
    
  synthesizeAndPrint env typ cq []  
  
testDelete = do
  let env = addList $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "xs" listAll (list $ mElems valList |=| mElems (listVar "xs") /-/ SetLit (TypeVarT "a") [vartVar "a" "x"]))
      
  synthesizeAndPrint env typ [vartVar "a" "x" |=| vartVar "a" "y"] []  
  
testUseMap = do
  let env = addPolyConstant "map" (Forall "a" $ Forall "b" $ Monotype $ 
                                    FunctionT "f" (FunctionT "x" (vartAll "a") (vartAll "b")) 
                                    (FunctionT "xs" (ScalarT listT [vartAll "a"] ftrue) (ScalarT listT [vartAll "b"] $ mLen valList |=| mLen (listVar "xs")))) .
            addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .                                      
            addConstant "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .
            addConstant "abs" (FunctionT "x" intAll (int (valInt |>=| intVar "x" |&| valInt |>=| IntLit 0))) .
            addList $ emptyEnv

  let typ = Monotype $ FunctionT "xs" (intlist ftrue) (natlist $ mLen valList |=| mLen (listVar "xs"))
  
  synthesizeAndPrint env typ [] []  
  
{- Tree programs -}

-- treeT = DatatypeT "tree"
-- tree = ScalarT treeT []
-- treeAll = tree ftrue
-- treeVar = Var treeT
-- valTree = treeVar valueVarName

-- -- | Add tree datatype to the environment
-- addTree = addDatatype "tree" (Datatype 0 ["Empty", "Node"] (Just $ Measure IntT "size")) .
          -- addConstant "Empty" (tree $  
            -- Measure IntT "size" valTree  |=| IntLit 0
            -- |&| Measure SetT "telems" valTree  |=| SetLit []
            -- ) .
          -- addConstant "Node" (FunctionT "x" intAll (FunctionT "l" treeAll (FunctionT "r" treeAll (tree $  
            -- Measure IntT "size" valTree |=| Measure IntT "size" (treeVar "l") |+| Measure IntT "size" (treeVar "r") |+| IntLit 1
            -- |&| Measure SetT "telems" valTree |=| Measure SetT "telems" (treeVar "l") /+/ Measure SetT "telems" (treeVar "r") /+/ SetLit [intVar "x"]
            -- ))))            
            
-- testRoot = do
  -- let env = addConstant "0" (int (valInt |=| IntLit 0)) .
            -- addConstant "1" (int (valInt |=| IntLit 1)) .
            -- addTree $ emptyEnv
  -- let typ = Monotype $ FunctionT "t" (tree $ Measure IntT "size" valTree |>| IntLit 0) (int $ valInt `fin` Measure SetT "telems" (treeVar "t"))
  
  -- synthesizeAndPrint env typ [] []
            
              
-- testTreeGen = do
  -- let env = addConstant "0" (int (valInt |=| IntLit 0)) .
            -- addConstant "1" (int (valInt |=| IntLit 0)) .
            -- addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            -- addTree $ emptyEnv

  -- let typ = Monotype $ FunctionT "n" nat (tree $ Measure IntT "size" valTree |=| intVar "n")
  
  -- let cq = do
      -- op <- [Eq]      
      -- return $ Binary op (intVar "x") (intVar "y")
  
  -- synthesizeAndPrint env typ cq []
  
-- testTreeSize = do
  -- let env = addConstant "0" (int (valInt |=| IntLit 0)) .
            -- addConstant "1" (int (valInt |=| IntLit 0)) .
            -- -- addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            -- -- addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            -- addConstant "plus" (FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |+| intVar "y")))) .
            -- -- addConstant "minus" (FunctionT "x" nat (FunctionT "y" nat (int (valInt |=| intVar "x" |-| intVar "y")))) .            
            -- addTree $ emptyEnv

  -- let typ = Monotype $ FunctionT "t" treeAll (int $ valInt |=| Measure IntT "size" (treeVar "t"))

  -- synthesizeAndPrint env typ [] []
            
-- testFlatten = do
  -- -- let env = addConstant "append" (FunctionT "xs" listAll (FunctionT "ys" listAll (list $ mElems valList |=| mElems (listVar "xs") /+/ mElems (listVar "ys")))) .
            -- -- addList $ addTree $ emptyEnv

  -- -- let typ = Monotype $ FunctionT "t" treeAll (list $ mElems valList |=| Measure SetT "telems" (treeVar "t"))
  
  -- let env = addConstant "append" (FunctionT "xs" listAll (FunctionT "ys" listAll (list $ mLen valList |=| mLen (listVar "xs") |+| mLen (listVar "ys")))) .
            -- addList $ addTree $ emptyEnv

  -- let typ = Monotype $ FunctionT "t" treeAll (list $ mLen valList |=| Measure IntT "size" (treeVar "t"))
    
  -- synthesizeAndPrint env typ [] []
            
  
    
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
  -- putStr "\n=== polymorphic ===\n";   testPolymorphic
  -- List programs
  -- putStr "\n=== head ===\n";      testHead
  -- putStr "\n=== replicate ===\n"; testReplicate
  -- putStr "\n=== length ===\n";    testLength
  -- putStr "\n=== append ===\n";    testAppend
  -- putStr "\n=== stutter ===\n";   testStutter
  -- putStr "\n=== drop ===\n";   testDrop
  putStr "\n=== delete ===\n";   testDelete
  -- putStr "\n=== use map ===\n";   testUseMap
  -- Tree programs
  -- putStr "\n=== root ===\n";      testRoot
  -- putStr "\n=== tree gen ===\n";     testTreeGen
  -- putStr "\n=== tree size ===\n";     testTreeSize
  -- putStr "\n=== flatten ===\n";      testFlatten
