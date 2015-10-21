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
  _condDepth = 1,
  -- _fixStrategy = AllArguments,
  _fixStrategy = FirstArgument,
  -- _fixStrategy = DisableFixpoint,
  _polyRecursion = True,
  _incrementalSolving = True,
  _condQualsGen = undefined,
  _typeQualsGen = undefined,
  _solver = undefined,
  _context = id
}

-- | Parameters for constraint solving
solverParams = SolverParams {
  pruneQuals = True,
  -- pruneQuals = False,
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
  
synthesizeAndPrint name env typ cquals tquals = do
  let goal = Goal name env typ
  print $ pretty goal
  print empty
  mProg <- synthesize explorerParams solverParams goal cquals tquals
  case mProg of
    Nothing -> putStr "No Solution"
    Just prog -> print $ nest 2 $ text "Solution" $+$ programDoc (const empty) prog -- $+$ parens (text "Size:" <+> pretty (programNodeCount prog))
  print empty
    
{- Integer programs -}
  
testApp = do
  let env = addVariable "a" intAll .
            addVariable "b" intAll .
            addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = Monotype $ int (valInt |>| intVar "b")
  
  synthesizeAndPrint "app" env typ [] []
  
testApp2 = do
  let env = addVariable "a" nat .
            -- addConstant "1" (int (valInt |=| IntLit 1)) .
            addConstant "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            -- addConstant "plus" (FunctionT "x" nat (FunctionT "y" nat (int (valInt |=| intVar "x" |+| intVar "y")))) .
            -- addConstant "minus" (FunctionT "x" nat (FunctionT "y" nat (int (valInt |=| intVar "x" |-| intVar "y")))) .
            id $ emptyEnv
  let typ = Monotype $ int (valInt |=| intVar "a" |+| IntLit 10)
  
  synthesizeAndPrint "app2" env typ [] []
  
testLambda = do
  let env = addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "a" nat $ int (valInt |=| intVar "a" |+| IntLit 3)
  
  synthesizeAndPrint "abs" env typ [] []
  
testMax2 = do
  let env = emptyEnv
  let typ = Monotype $ FunctionT "x" intAll $ FunctionT "y" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y")
  
  let cq = do
        op <- [Ge, Le, Neq]
        return $ Binary op (intVar "x") (intVar "y")  
      
  synthesizeAndPrint "max2" env typ cq []
  
testMax3 = do
  let env =
            -- addConstant "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            -- addConstant "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "x" intAll $ FunctionT "y" intAll $ FunctionT "z" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y" |&| valInt |>=| intVar "z")
  
  let cq = do
        op <- [Ge, Le, Neq]
        return $ Binary op (intVar "x") (intVar "y")  
      
  synthesizeAndPrint "max3" env typ cq []
  
testMax4 = do
  let env =
            -- addConstant "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            -- addConstant "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "w" intAll $ FunctionT "x" intAll $ FunctionT "y" intAll $ FunctionT "z" intAll $ 
                int (valInt |>=| intVar "w" |&| valInt |>=| intVar "x" |&| valInt |>=| intVar "y" |&| valInt |>=| intVar "z")
  
  let cq = do
        op <- [Ge, Le, Neq]
        return $ Binary op (intVar "x") (intVar "y")  
      
  synthesizeAndPrint "max4" env typ cq []    
   
testAbs = do
  let env = addConstant "0" (int (valInt |=| IntLit 0)) .            
            -- addConstant "id" (FunctionT "x" intAll (int (valInt |=| intVar "x"))) .
            addConstant "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "x" intAll $ int ((valInt |=| intVar "x" ||| valInt |=| fneg (intVar "x")) |&| valInt |>=| IntLit 0)  
  
  -- let cq = do
        -- op <- [Ge, Le, Neq]
        -- rhs <- [intVar "y", IntLit 0]
        -- return $ Binary op (intVar "x") rhs  
  let cq = do
        op <- [Ge, Le, Neq]
        return $ Binary op (intVar "x") (intVar "y")
      
  synthesizeAndPrint "abs" env typ cq []

testAddition = do
  let env = addConstant "0" (int (valInt |=| IntLit 0)) .
            addConstant "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv

  let typ = Monotype $ FunctionT "y" nat $ FunctionT "z" nat $ int (valInt |=| intVar "y" |+| intVar "z")
  
  -- let cq = do
        -- lhs <- [intVar "x", IntLit 0]
        -- op <- [Ge, Le, Neq]
        -- rhs <- [intVar "y", IntLit 0]
        -- guard $ lhs /= rhs
        -- return $ Binary op lhs rhs
  let cq = do
        op <- [Ge, Le, Neq]
        return $ Binary op (intVar "x") (intVar "y")        
      
  synthesizeAndPrint "add" env typ cq []
  
-- testEven = do
  -- let env =
            -- addConstant "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            -- -- addConstant "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            -- addConstant "not" (FunctionT "x" boolAll $ bool (valBool |=| fnot $ boolVar "x")) .
            -- id $ emptyEnv

  -- let typ = Monotype $ FunctionT "y" nat $ bool (valBool |=| intVar "y" |\\| IntLit 2)
  
  -- let cq = do
      -- lhs <- [intVar "x", IntLit 0]
      -- op <- [Ge, Le, Neq]
      -- rhs <- [intVar "y", IntLit 0]
      -- guard $ lhs /= rhs
      -- return $ Binary op lhs rhs
      
  -- synthesizeAndPrint env typ cq []
  
    
{- Polymorphic programs -}

testId = do
  let env = emptyEnv
  let typ = Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (vart "a" $ valVart "a" |=| vartVar "a" "x")
  
  synthesizeAndPrint "id" env typ [] []
  
testConst = do
  let env = emptyEnv
  let typ = Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (vart "a" $ valVart "a" |=| vartVar "a" "x"))
  
  synthesizeAndPrint "const" env typ [] []  
  
testCompose = do
  let env = emptyEnv
  let typ = Forall "a" $ Forall "b" $ Forall "c" $ Monotype $ FunctionT "f" (FunctionT "x" (vartAll "a") (vartAll "b")) 
              (FunctionT "g" (FunctionT "y" (vartAll "b") (vartAll "c")) 
              (FunctionT "z" (vartAll "a") (vartAll "c")))

  synthesizeAndPrint "compose" env typ [] []    
  
testPolymorphic = do
  let env = -- addPolyConstant "coerce" (Forall "a" $ Forall "b" $ Monotype $ FunctionT "x" (vartAll "a") (vartAll "b")) .            
            addPolyConstant "id" (Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (vart "a" $ valVart "a" |=| vartVar "a" "x")) .
            addConstant "inc" (FunctionT "x" nat nat) .
            id $ emptyEnv
  let typ = Monotype $ FunctionT "x" intAll nat
  
  synthesizeAndPrint "poly" env typ [] []
  
  
{- List programs -}

listT = DatatypeT "List"
list = ScalarT listT [vartAll "a"]
listAll = list ftrue
listVar = Var (toSort listT)
valList = listVar valueVarName

intlist = ScalarT listT [intAll]
natlist = ScalarT listT [nat]
poslist = ScalarT listT [pos]

mLen = Measure IntS "len"
mElems = Measure (SetS (UninterpretedS "a")) "elems"

-- | Add list datatype to the environment
addList = addDatatype "List" (Datatype 1 ["Nil", "Cons"] (Just $ mLen)) .
          addPolyConstant "Nil" (Forall "a" $ Monotype $ list $ mLen valList |=| IntLit 0
                                                            |&| mElems valList  |=| SetLit (UninterpretedS "a") []
                                ) .
          addPolyConstant "Cons" (Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "xs" listAll (list $ mLen valList |=| mLen (listVar "xs") |+| IntLit 1
                                                                                                                     |&| mLen valList |>| IntLit 0
                                                                                                                     |&| mElems valList |=| mElems (listVar "xs") /+/ SetLit (UninterpretedS "a") [vartVar "a" "x"]
                                                                                   )))
                                                                                                                                                                      
testHead = do
  let env = addList $ emptyEnv
  let typ = Forall "a" $ Monotype $ FunctionT "xs" (list $ mLen valList |>| IntLit 0) (vart "a" $ valVart "a" `fin` mElems (listVar "xs"))
  
  synthesizeAndPrint "head" env typ [] []
  
testNull = do
  let env = addConstant "true" (bool valBool) .
            addConstant "false" (bool (fnot valBool)) .
            addList $ emptyEnv
  let typ = Forall "a" $ Monotype $ FunctionT "xs" (listAll) (bool $ valBool |=| (mLen (listVar "xs") |=| IntLit 0))
  
  synthesizeAndPrint "null" env typ [] []  
  
testReplicate = do
  let env = addConstant "0" (int (valInt |=| IntLit 0)) .
            addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .            
            -- addPolyConstant "genInc" (Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (vart "a" (valVart "a" |>| vartVar "a" "x"))) .
            addList $ emptyEnv

  -- let typ = Forall "a" $ Monotype $ FunctionT "n" nat (FunctionT "y" (vartAll "a") (ScalarT listT [vart "a" $ valVart "a" |>| vartVar "a" "y"] $ mLen valList |=| intVar "n"))
  let typ = Forall "a" $ Monotype $ FunctionT "n" nat (FunctionT "y" (vartAll "a") (ScalarT listT [vartAll "a"] $ mLen valList |=| intVar "n"))
  -- let typ = Forall "a" $ Monotype $ FunctionT "y" (vartAll "a") (ScalarT listT [vartAll "a"] $ mLen valList |=| IntLit 1)
          
  let cq = do
        op <- [Ge, Le, Neq]
        return $ Binary op (intVar "x") (intVar "y")
      
  synthesizeAndPrint "replicate" env typ cq []
  
testLength = do
  let env = addConstant "0" (int (valInt |=| IntLit 0)) .
            addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            addList $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "l" listAll (int $ valInt |=| mLen (listVar "l"))

  synthesizeAndPrint "length" env typ [] [valInt |>=| IntLit 0]
  
testAppend = do
  let env = addList $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "xs" listAll (FunctionT "ys" listAll (list $ mLen valList |=| mLen (listVar "xs") |+| mLen (listVar "ys")))

  synthesizeAndPrint "append" env typ [] []
  
testStutter = do
  let env = addList $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "xs" listAll (list $ mLen valList |=| IntLit 2 |*| mLen (listVar "xs") |&| mElems valList |=| mElems (listVar "xs"))
  
  synthesizeAndPrint "stutter" env typ [] []
  
testTake = do
  let env = addConstant "0" (int (valInt |=| IntLit 0)) .
            addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            addList $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "xs" listAll (FunctionT "n" (int $ IntLit 0 |<=| valInt |&| valInt |<=| mLen (listVar "xs")) (list $ mLen valList |=| intVar "n"))
  
  let cq = do
        op <- [Ge, Le, Neq]
        return $ Binary op (intVar "x") (intVar "y")
    
  synthesizeAndPrint "take" env typ cq []    
  
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
    
  synthesizeAndPrint "drop" env typ cq []  
  
testDelete = do
  let env = addList $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "xs" listAll (list $ mElems valList |=| mElems (listVar "xs") /-/ SetLit (UninterpretedS "a") [vartVar "a" "x"]))
      
  synthesizeAndPrint "delete" env typ [vartVar "a" "x" |=| vartVar "a" "y"] []  
  
testMap = do
  let env = addList $ emptyEnv

  let typ = (Forall "a" $ Forall "b" $ Monotype $ 
                                    FunctionT "f" (FunctionT "x" (vartAll "a") (vartAll "b")) 
                                    (FunctionT "xs" (ScalarT listT [vartAll "a"] ftrue) (ScalarT listT [vartAll "b"] $ mLen valList |=| mLen (listVar "xs"))))
    
  synthesizeAndPrint "map" env typ [] []  
  
testUseMap = do
  let env = addPolyConstant "map" (Forall "a" $ Forall "b" $ Monotype $
                                    FunctionT "f" (FunctionT "x" (vartAll "a") (vartAll "b")) 
                                    (FunctionT "xs" (ScalarT listT [vartAll "a"] ftrue) 
                                    (ScalarT listT [vartAll "b"] $ mLen valList |=| mLen (listVar "xs")))) .
            addConstant "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .            
            addList $ emptyEnv

  let typ = Monotype $ FunctionT "xs" (intlist ftrue) (natlist $ mLen valList |=| mLen (listVar "xs"))
  
  let cq = do
        op <- [Ge, Le, Neq]
        return $ Binary op (intVar "x") (IntLit 0)
    
  synthesizeAndPrint "useMap" env typ cq []
  
testUseFold1 = do
  let env = addPolyConstant "fold1" (Forall "a" $ Monotype $ 
                                    FunctionT "f" (FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (vartAll "a"))) 
                                    (FunctionT "xs" (ScalarT listT [vartAll "a"] $ mLen valList |>| IntLit 0) (vartAll "a"))) .
            addConstant "gcd" (FunctionT "x" pos (FunctionT "y" pos pos)) .
            addList $ emptyEnv

  let typ = Monotype $ FunctionT "xs" (poslist $ mLen valList |>| IntLit 0) nat
    
  synthesizeAndPrint "fold" env typ [] []
  
  
{- Sorted lists -}

incListT = DatatypeT "IncList"
incList = ScalarT incListT [vartAll "a"]
incListVar = Var (toSort incListT)
valIncList = incListVar valueVarName

intInclist = ScalarT incListT [intAll]
natInclist = ScalarT incListT [nat]

mILen = Measure IntS "len"
mIElems = Measure (SetS $ UninterpretedS "a") "elems"

-- | Add list datatype to the environment
addIncList = addDatatype "IncList" (Datatype 1 ["Nil", "Cons"] (Just $ mLen)) .
          addPolyConstant "Nil" (Forall "a" $ Monotype $ incList $ mLen valIncList |=| IntLit 0 |&| 
                                                               mIElems valIncList  |=| SetLit (UninterpretedS "a") []
                                ) .
          addPolyConstant "Cons" (Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") 
                                                         (FunctionT "xs" (ScalarT incListT [vart "a" $ valVart "a" |>=| vartVar "a" "x"] ftrue) 
                                                         (incList $ mLen valIncList |=| mLen (incListVar "xs") |+| IntLit 1 |&| 
                                                                mIElems valIncList |=| mIElems (incListVar "xs") /+/ SetLit (UninterpretedS "a") [vartVar "a" "x"]
                                                          )))

testMakeIncList = do
  let env = addConstant "0" (int (valInt |=| IntLit 0)) .
            -- addConstant "1" (int (valInt |=| IntLit 1)) .
            addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            addIncList $ emptyEnv

  let typ = Monotype $ natInclist $ mIElems valIncList |=| SetLit IntS [IntLit 0, IntLit 1]
          
  synthesizeAndPrint "make" env typ [] []                                                          
  
testIncListInsert = do
  let env = addIncList $ emptyEnv

  -- let typ = Forall "a" $ Monotype $ (FunctionT "xs" (incList ftrue) (FunctionT "x" (vartAll "a") (incList $ mIElems valIncList |=| mIElems (incListVar "xs") /+/ SetLit (UninterpretedS "a") [vartVar "a" "x"])))
  let typ = Forall "a" $ Monotype $ (FunctionT "x" (vartAll "a") (FunctionT "xs" (incList ftrue) (incList $ mIElems valIncList |=| mIElems (incListVar "xs") /+/ SetLit (UninterpretedS "a") [vartVar "a" "x"])))
          
  let cq = do
        op <- [Ge, Le, Neq]
        return $ Binary op (vartVar "a" "x") (vartVar "a" "y")

  synthesizeAndPrint "insert" env typ cq []
  
testIncListMerge = do
  let env = -- addPolyConstant "insert" (Forall "a" $ Monotype $ (FunctionT "x" (vartAll "a") (FunctionT "xs" (incList ftrue) (incList $ mIElems valIncList |=| mIElems (incListVar "xs") /+/ SetLit (TypeVarT "a") [vartVar "a" "x"])))) .
            addIncList $ emptyEnv

  let typ = Forall "a" $ Monotype $ (FunctionT "xs" (incList ftrue) (FunctionT "ys" (incList ftrue) (incList $ mIElems valIncList |=| mIElems (incListVar "xs") /+/ mIElems (incListVar "ys"))))
          
  let cq = do
        op <- [Ge, Le, Neq]
        return $ Binary op (intVar "x") (intVar "y")

  synthesizeAndPrint "merge" env typ cq []                                                          
  
    
{- Tree programs -}

treeT = DatatypeT "tree"
tree = ScalarT treeT [vartAll "a"]
treeAll = tree ftrue
treeVar = Var (toSort treeT)
valTree = treeVar valueVarName

mSize = Measure IntS "size"
mTElems = Measure (SetS (UninterpretedS "a")) "telems"

-- | Add tree datatype to the environment
addTree = addDatatype "tree" (Datatype 1 ["Empty", "Node"] (Just mSize)) .
          addPolyConstant "Empty" (Forall "a" $ Monotype $ tree $  
            mSize valTree  |=| IntLit 0
            -- |&| (mTElems valTree |=| SetLit (TypeVarT "a") [])
            ) .
          addPolyConstant "Node" (Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "l" treeAll (FunctionT "r" treeAll (tree $  
            mSize valTree |=| mSize (treeVar "l") |+| mSize (treeVar "r") |+| IntLit 1
            -- |&| mTElems valTree |=| mTElems (treeVar "l") /+/ mTElems (treeVar "r") /+/ SetLit (TypeVarT "a") [vartVar "a" "x"]
            ))))            
            
testRoot = do
  let env = addTree $ emptyEnv
  let typ = Forall "a" $ Monotype $ FunctionT "t" (tree $ mSize valTree |>| IntLit 0) (vartAll "a") -- $ valVart "a" `fin` mTElems (treeVar "t"))
  
  synthesizeAndPrint "root" env typ [] []
            
              
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
  
testTreeSize = do
  let env = addConstant "0" (int (valInt |=| IntLit 0)) .
            addConstant "1" (int (valInt |=| IntLit 0)) .
            -- addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            -- addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            addConstant "plus" (FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |+| intVar "y")))) .
            -- addConstant "minus" (FunctionT "x" nat (FunctionT "y" nat (int (valInt |=| intVar "x" |-| intVar "y")))) .            
            addTree $ emptyEnv

  let typ = Forall "a" $ Monotype $ FunctionT "t" treeAll (int $ valInt |=| mSize (treeVar "t"))

  synthesizeAndPrint "size" env typ [] []
            
-- testFlatten = do
  -- -- let env = addConstant "append" (FunctionT "xs" listAll (FunctionT "ys" listAll (list $ mElems valList |=| mElems (listVar "xs") /+/ mElems (listVar "ys")))) .
            -- -- addList $ addTree $ emptyEnv

  -- -- let typ = Monotype $ FunctionT "t" treeAll (list $ mElems valList |=| Measure SetS "telems" (treeVar "t"))
  
  -- let env = addConstant "append" (FunctionT "xs" listAll (FunctionT "ys" listAll (list $ mLen valList |=| mLen (listVar "xs") |+| mLen (listVar "ys")))) .
            -- addList $ addTree $ emptyEnv

  -- let typ = Monotype $ FunctionT "t" treeAll (list $ mLen valList |=| Measure IntT "size" (treeVar "t"))
    
  -- synthesizeAndPrint env typ [] []
            
  
    
main = do
  -- -- Integer programs
  -- testApp
  -- testApp2  
  -- -- testLambda
  -- testMax2  
  -- testMax3
  -- testMax4
  -- testAbs  
  -- testAddition
  -- -- testMult
  -- -- Polymorphic programs
  -- -- testId
  -- -- testConst
  -- -- testCompose  
  -- -- testPolymorphic
  -- -- List programs
  -- testHead
  -- testReplicate
  -- testLength
  -- testAppend
  -- testStutter
  -- testTake
  -- testDrop
  -- testDelete
  -- testMap
  testUseMap
  -- testUseFold1
  -- testMakeIncList
  -- testIncListInsert
  -- testIncListMerge
  -- -- Tree programs
  -- testRoot
  -- testTreeGen
  -- testTreeSize
  -- testFlatten
