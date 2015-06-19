module Main where

import Synquid.Logic
import Synquid.Solver
import Synquid.Program
import Synquid.Pretty
import Synquid.ConstraintGenerator
import Synquid.TemplateGenerator
import Synquid.Synthesizer

import Control.Monad

templGenParams = TemplGenParams {
  maxDepth = -1
}

consGenParams = ConsGenParams {
  bottomUp = True,
  abstractLeaves = True,
  abstractFix = True
}

-- | Search parameters
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
  constraintPickStrategy = SmallSpaceConstraint
  }
  
synthesizeAndPrint env typ templ cquals tquals = do
  print $ nest 2 $ text "Spec" $+$ pretty typ
  print $ nest 2 $ text "Template" $+$ pretty templ
  print empty
  mProg <- synthesize templGenParams consGenParams solverParams env typ templ cquals tquals
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
  let templ = hole int_
  
  -- let templ = sym (int_ |->| int_) |$| sym int_  
  -- let tq (_ : syms) = do
      -- op <- [Ge, Le, Neq]
      -- rhs <- syms
      -- return $ Binary op valInt rhs
        
  synthesizeAndPrint env typ templ [] []
  
testApp2 = do
  let env = addSymbol "a" intAll .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = int (valInt |=| intVar "a" |+| IntLit 5)
  let templ = hole int_
  
  -- let templ = sym (int_ |->| int_) |$| sym (int_ |->| int_) |$| sym int_  
  -- let tq (_ : syms) = do
      -- rhs <- syms
      -- [valInt |=| rhs]
      -- -- [valInt |=| rhs, valInt |=| rhs |+| IntLit 1, valInt |=| rhs |-| IntLit 1]
        
  synthesizeAndPrint env typ templ [] []
  
testLambda = do
  let env = addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = FunctionT "a" nat $ int (valInt |=| intVar "a" |+| IntLit 2)
  let templ = int_ |.| hole int_
  
  -- let templ = int_ |.| sym (int_ |->| int_) |$| sym (int_ |->| int_) |$| sym int_
  -- let tq0 _ = [valInt |>=| IntLit 0]
  -- let tq1 (_ : syms) = do
      -- rhs <- syms
      -- [valInt |=| rhs]
      -- -- [valInt |=| rhs, valInt |=| rhs |+| IntLit 1, valInt |=| rhs |-| IntLit 1]
        
  synthesizeAndPrint env typ templ [] []
  
testMax2 = do
  let env = emptyEnv
  let typ = FunctionT "x" intAll $ FunctionT "y" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y")
  let templ = int_ |.| int_ |.| choice (hole int_) (hole int_)
  
  let cq = do
      op <- [Ge, Le, Neq]
      return $ Binary op (intVar "x") (intVar "y")  
      
  -- let tq (_ : syms) = do
      -- op <- [Ge, Le, Neq]
      -- rhs <- syms
      -- return $ Binary op valInt rhs      
  
  synthesizeAndPrint env typ templ cq []
   
testAbs = do
  let env =             
            addSymbol "id" (FunctionT "x" intAll (int (valInt |=| intVar "x"))) .
            addSymbol "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .
            id $ emptyEnv
  let typ = FunctionT "x" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| IntLit 0)  
  let templ = int_ |.| choice (hole int_) (hole int_)
  -- let templ = int_ |.| choice (sym (int_ |->| int_) |$| sym int_) (sym (int_ |->| int_) |$| sym int_)
  
  let cq = do
      op <- [Ge, Le, Neq]
      rhs <- [intVar "y", IntLit 0]
      return $ Binary op (intVar "x") rhs  
      
  -- let tq0 _ = [valInt |<=| IntLit 0, valInt |>=| IntLit 0, valInt |/=| IntLit 0]
  -- let tq1 (_ : syms) = do
      -- rhs <- syms
      -- [valInt |=| rhs, valInt |>=| rhs, valInt |=| fneg rhs]
        
  synthesizeAndPrint env typ templ cq []
  
testPeano = do
  let env =             
            addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            addSymbol "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .
            addSymbol "const0" (FunctionT "x" intAll (int (valInt |=| IntLit 0))) .
            id $ emptyEnv

  let typ = FunctionT "y" nat $ int (valInt |=| intVar "y")
  let templ = fix_ (int_ |.| choice 
                (sym (int_ |->| int_) |$| sym int_)
                (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_))))
  
  let cq = do
      op <- [Ge, Le, Neq]
      rhs <- [intVar "y", IntLit 0]
      return $ Binary op (intVar "x") rhs
      
  -- let tq0 _ = [valInt |>=| IntLit 0]
  -- -- let tq0 _ = [valInt |<=| IntLit 0, valInt |>=| IntLit 0]
  -- let tq1 (_ : syms) = do
      -- rhs <- syms
      -- [valInt |=| rhs]
      -- -- [valInt |=| rhs, valInt |=| rhs |+| IntLit 1, valInt |=| rhs |-| IntLit 1, valInt |=| fneg rhs]
        
  synthesizeAndPrint env typ templ cq []
  
testAddition = do
  let env =
            addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv

  let typ = FunctionT "y" nat $ FunctionT "z" nat $ int (valInt |=| intVar "y" |+| intVar "z")
  -- let templ = fix_ (int_ |.| int_ |.| choice 
                -- (sym int_) 
                -- (sym (int_ |->| int_) |$| ((sym (int_ |->| int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_)) |$| sym int_)))
  -- let templ = int_ |.| (fix_ (int_ |.| choice 
                -- (sym int_) 
                -- (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_)))))
  let templ = fix_ (int_ |.| fix_ (int_ |.| choice (hole int_) (hole int_)))
  
  let cq = do
      lhs <- [intVar "x", IntLit 0]
      op <- [Ge, Le, Neq]
      rhs <- [intVar "y", IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs
      
  -- let tq0 _ = [valInt |<=| IntLit 0, valInt |>=| IntLit 0]
  -- let tq1 (_ : syms) = do
      -- rhs <- syms
      -- []
      -- -- [valInt |=| rhs, valInt |=| rhs |-| IntLit 1, valInt |=| rhs |+| IntLit 1]
  -- let tq2 (_ : syms) = do
      -- rhs1 <- syms
      -- rhs2 <- syms
      -- guard $ rhs1 < rhs2
      -- [valInt |=| rhs1 |+| rhs2]
      -- -- [valInt |=| rhs1 |+| rhs2, valInt |=| rhs1 |+| rhs2 |+| IntLit 1, valInt |=| rhs1 |+| rhs2 |-| IntLit 1]
        
  synthesizeAndPrint env typ templ cq []
  
testCompose = do
  let env = emptyEnv

  let typ = FunctionT "f" (FunctionT "x" intAll (int $ valInt |=| intVar "x" |+| IntLit 1)) (FunctionT "y" intAll (int $ valInt |=| intVar "y" |+| IntLit 2))
  let templ = (int_ |->| int_) |.| int_ |.| hole int_
  -- let templ = (int_ |->| int_) |.| int_ |.| (sym (int_ |->| int_) |$| sym (int_ |->| int_) |$| sym int_)

  synthesizeAndPrint env typ templ [] []  
  
-- | List programs  
  
testHead = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "1" (int (valInt |=| IntLit 1)) .
            id $ listEnv
  let typ = FunctionT "xs" (list $ Measure IntT "len" valList |>| IntLit 0) (int $ valInt `fin` Measure SetT "elems" (listVar "xs"))
  let templ = list_ |.| match (hole list_) (hole int_) (hole int_)
  
  -- let templ = list_ |.| match (sym list_) (sym int_) (sym int_)  
  synthesizeAndPrint env typ templ [] []
  
testReplicate = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            id $ listEnv

  let typ = FunctionT "n" nat (FunctionT "y" intAll (list $ Measure IntT "len" valList |=| intVar "n" |&| Measure SetT "elems" valList /<=/ SetLit [intVar "y"]))
  let templ = fix_ (int_ |.| int_ |.| choice (sym list_) (hole list_))
  
  -- let templ = fix_ (int_ |.| int_ |.| choice
                -- (sym list_)
                -- ((sym (int_ |->| list_ |->| list_) |$| (sym (int_ |->| int_) |$| sym int_)) |$| (sym (int_ |->| int_ |->| list_) |$| (sym (int_ |->| int_) |$| sym int_)) |$| sym int_))  
          
  let cq = do
      op <- [Ge, Le, Neq]
      return $ Binary op (intVar "x") (intVar "y")
      
  synthesizeAndPrint env typ templ cq []
  
testLength = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            id $ listEnv

  let typ = FunctionT "l" listAll (int $ valInt |=| Measure IntT "len" (listVar "l"))
  let templ = fix_ (list_ |.| match (hole list_) (hole int_) (hole int_))
  
  -- let templ = fix_ (list_ |.| match (sym list_)
                -- (sym int_)
                -- (sym (int_ |->| int_) |$| (sym (list_ |->| int_) |$| sym list_)))  

  synthesizeAndPrint env typ templ [] [valInt |>=| IntLit 0]
  
testAppend = do
  let env = id $ listEnv

  let typ = FunctionT "xs" listAll (FunctionT "ys" listAll (list $ Measure IntT "len" valList |=| Measure IntT "len" (listVar "xs") |+| Measure IntT "len" (listVar "ys")))
  let templ = fix_ (list_ |.| list_ |.| match (hole list_) (hole list_) (hole list_))
  
  -- let templ = fix_ (list_ |.| list_ |.| match (sym list_) 
                -- (sym list_) 
                -- ((sym (int_ |->| list_ |->| list_) |$| 
                  -- (sym int_)) |$| 
                  -- ((sym (list_ |->| list_ |->| list_) |$| (sym list_)) |$| (sym list_))))

  synthesizeAndPrint env typ templ [] []
  
testStutter = do
  let env = id $ listEnv

  let typ = FunctionT "xs" listAll (list $ Measure IntT "len" valList |=| IntLit 2 |*| Measure IntT "len" (listVar "xs") |&| Measure SetT "elems" valList |=| Measure SetT "elems" (listVar "xs"))
  let templ = fix_ (list_ |.| match (hole list_) (hole list_) (hole list_))
  
  -- let templ = fix_ (list_ |.| match (sym list_) 
                -- (sym list_) 
                -- ((sym (int_ |->| list_ |->| list_) |$| 
                  -- (sym int_)) |$| 
                  -- (sym (int_ |->| list_ |->| list_) |$| 
                  -- (sym int_)) |$| (sym (list_ |->| list_) |$| sym list_)))

  synthesizeAndPrint env typ templ [] []  
  
main = do  
  -- -- Integer programs
  -- putStr "\n=== app ===\n";       testApp
  -- putStr "\n=== app2 ===\n";      testApp2
  -- putStr "\n=== lambda ===\n";    testLambda
  -- putStr "\n=== max2 ===\n";      testMax2  
  -- putStr "\n=== abs ===\n";       testAbs  
  -- putStr "\n=== peano ===\n";     testPeano  
  -- putStr "\n=== addition ===\n";  testAddition
  -- putStr "\n=== compose ===\n";   testCompose
  -- -- List programs
  -- putStr "\n=== head ===\n";      testHead
  -- putStr "\n=== replicate ===\n"; testReplicate
  -- putStr "\n=== length ===\n";    testLength
  -- putStr "\n=== append ===\n";    testAppend
  putStr "\n=== stutter ===\n";   testStutter
  
-- main = do
  -- let res = take 20 $ toList $ templates templGenParams (Set.fromList [int_, list_, int_ |->| list_, list_ |->| int_, list_ |->| list_]) list_
  -- print $ vsep (map (programDoc (const empty) (const empty) pretty) res)
