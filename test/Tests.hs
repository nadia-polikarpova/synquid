module Main where

import Synquid.Logic
import Synquid.Solver
import Synquid.SMTSolver
import Synquid.Program
import Synquid.Pretty
import Synquid.Explorer
import Synquid.Synthesizer
import Synquid.Parser

import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map, (!))
import Control.Monad

import Test.HUnit

main = runTestTT allTests

allTests = TestList [{-integerTests, listTests, incListTests, -}parserTests]

integerTests = TestLabel "Integer" $ TestList [
    TestCase testApp
  , TestCase testAppMany
  , TestCase testMax2
  , TestCase testMax3
  --, TestCase testMax4
  , TestCase testAbs
  , TestCase testAddition
  ]

listTests = TestLabel "List" $ TestList [
    TestCase testHead
  , TestCase testNull  
  , TestCase testReplicate  
  , TestCase testLength
  , TestCase testAppend
  , TestCase testStutter
  , TestCase testTake
  , TestCase testDrop
  , TestCase testDelete
  , TestCase testMap
  , TestCase testUseMap
  , TestCase testUseFold1
  ]
  
incListTests = TestLabel "IncList" $ TestList [
    TestCase testMakeIncList
  , TestCase testIncListInsert 
  , TestCase testIncListMerge 
  ]  
  
parserTests = TestLabel "Parser" $ TestList [testParseRefinement, testParseFunctionType, testParseTerm, testParseScalarType]

-- | Parameters for AST exploration
defaultExplorerParams = ExplorerParams {
  _eGuessDepth = 3,
  _scrutineeDepth = 0,
  _matchDepth = 1,
  _condDepth = 1,
  _fixStrategy = FirstArgument,
  _polyRecursion = True,
  _incrementalSolving = True,
  _condQualsGen = undefined,
  _typeQualsGen = undefined,
  _solver = undefined,
  _context = id
}

-- | Parameters for constraint solving
defaultSolverParams = SolverParams {
  pruneQuals = True,
  optimalValuationsStrategy = MarcoValuations,    
  semanticPrune = True,
  agressivePrune = True,
  candidatePickStrategy = InitializedWeakCandidate,
  constraintPickStrategy = SmallSpaceConstraint,
  candDoc = const empty
  }

testSynthesizeSuccess explorerParams solverParams env typ cquals tquals = do
  mProg <- synthesize explorerParams solverParams (Goal "test" env typ) cquals tquals
  assertBool "Synthesis failed" $ isJust mProg  
  
{- Testing Synthesis of Integer Programs -}

inequalities = do
  op <- [Ge, Le, Neq]
  return $ Binary op (intVar "x") (intVar "y")
  
inequalities0 = do
  op <- [Ge, Le, Neq]
  return $ Binary op (intVar "x") (IntLit 0)

-- | Single application  
testApp = let 
    env = addVariable "a" intAll .
          addVariable "b" intAll .
          addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
          addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
          id $ emptyEnv
    typ = Monotype $ int (valInt |>| intVar "b")
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ [] []  
  
-- | Multiple applications  
testAppMany = let 
    env = addVariable "a" nat .
          addConstant "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
          addConstant "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
          id $ emptyEnv
    typ = Monotype $ int (valInt |=| intVar "a" |+| IntLit 5)
  in testSynthesizeSuccess (defaultExplorerParams { _eGuessDepth = 5 }) defaultSolverParams env typ [] []  
  
-- | Maximum of 2 integers  
testMax2 = let
  env = emptyEnv
  typ = Monotype $ FunctionT "x" intAll $ FunctionT "y" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y")  
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ inequalities []  
  
-- | Maximum of 3 integers
testMax3 = let
  env = emptyEnv
  typ = Monotype $ FunctionT "x" intAll $ FunctionT "y" intAll $ FunctionT "z" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y" |&| valInt |>=| intVar "z")  
  in testSynthesizeSuccess (defaultExplorerParams {_condDepth = 2}) defaultSolverParams env typ inequalities []      
  
-- | Maximum of 4 integers  
testMax4 = let
  env = emptyEnv
  typ = Monotype $ FunctionT "w" intAll $ FunctionT "x" intAll $ FunctionT "y" intAll $ FunctionT "z" intAll $ 
                int (valInt |>=| intVar "w" |&| valInt |>=| intVar "x" |&| valInt |>=| intVar "y" |&| valInt |>=| intVar "z")  
  in testSynthesizeSuccess (defaultExplorerParams {_condDepth = 3}) defaultSolverParams env typ inequalities []
  
-- | Absolute value
testAbs = let
  env = addConstant "0" (int (valInt |=| IntLit 0)) .
        addConstant "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .
        id $ emptyEnv
  typ = Monotype $ FunctionT "x" intAll $ int ((valInt |=| intVar "x" ||| valInt |=| fneg (intVar "x")) |&| valInt |>=| IntLit 0)
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ inequalities []    

-- | Addition  
testAddition = let
  env = addConstant "0" (int (valInt |=| IntLit 0)) .
        addConstant "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
        addConstant "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
        id $ emptyEnv
  typ = Monotype $ FunctionT "y" nat $ FunctionT "z" nat $ int (valInt |=| intVar "y" |+| intVar "z")  
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ inequalities []
  
{- Testing Synthesis of List Programs -}

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
                                                                                   
polyEq = [vartVar "a" "x" |=| vartVar "a" "y"]
                                                                                                                                                                      
testHead = let
  env = addList $ emptyEnv
  typ = Forall "a" $ Monotype $ FunctionT "xs" (list $ mLen valList |>| IntLit 0) (vart "a" $ valVart "a" `fin` mElems (listVar "xs"))
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ [] []
  
testNull = let
  env = addConstant "true" (bool valBool) .
        addConstant "false" (bool (fnot valBool)) .
        addList $ emptyEnv
  typ = Forall "a" $ Monotype $ FunctionT "xs" (listAll) (bool $ valBool |=| (mLen (listVar "xs") |=| IntLit 0))
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ [] []
  
testReplicate = let
  env = addConstant "0" (int (valInt |=| IntLit 0)) .
        addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
        addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .            
        addList $ emptyEnv
  typ = Forall "a" $ Monotype $ FunctionT "n" nat (FunctionT "y" (vartAll "a") (ScalarT listT [vartAll "a"] $ mLen valList |=| intVar "n"))          
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ inequalities []    
  
testLength = let
  env = addConstant "0" (int (valInt |=| IntLit 0)) .
        addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
        addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
        addList $ emptyEnv
  typ = Forall "a" $ Monotype $ FunctionT "l" listAll (int $ valInt |=| mLen (listVar "l"))
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ [] []    
  
testAppend = let
  env = addList $ emptyEnv
  typ = Forall "a" $ Monotype $ FunctionT "xs" listAll (FunctionT "ys" listAll (list $ mLen valList |=| mLen (listVar "xs") |+| mLen (listVar "ys")))
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ [] []
  
testStutter = let
  env = addList $ emptyEnv
  typ = Forall "a" $ Monotype $ FunctionT "xs" listAll (list $ mLen valList |=| IntLit 2 |*| mLen (listVar "xs") |&| mElems valList |=| mElems (listVar "xs"))
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ [] []
  
testTake = let
  env = addConstant "0" (int (valInt |=| IntLit 0)) .
        addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
        addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
        addList $ emptyEnv
  typ = Forall "a" $ Monotype $ FunctionT "xs" listAll (FunctionT "n" (int $ IntLit 0 |<=| valInt |&| valInt |<=| mLen (listVar "xs")) (list $ mLen valList |=| intVar "n"))  
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ inequalities []  
  
testDrop = let
  env = addConstant "0" (int (valInt |=| IntLit 0)) .
        addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
        addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
        addList $ emptyEnv
  typ = Forall "a" $ Monotype $ FunctionT "xs" listAll (FunctionT "n" (int $ IntLit 0 |<=| valInt |&| valInt |<=| mLen (listVar "xs")) (list $ mLen valList |=| mLen (listVar "xs") |-| intVar "n"))
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ inequalities []  
  
testDelete = let
  env = addList $ emptyEnv
  typ = Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "xs" listAll (list $ mElems valList |=| mElems (listVar "xs") /-/ SetLit (UninterpretedS "a") [vartVar "a" "x"]))
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ polyEq []      
  
testMap = let
  env = addList $ emptyEnv
  typ = (Forall "a" $ Forall "b" $ Monotype $ 
                                    FunctionT "f" (FunctionT "x" (vartAll "a") (vartAll "b")) 
                                    (FunctionT "xs" (ScalarT listT [vartAll "a"] ftrue) (ScalarT listT [vartAll "b"] $ mLen valList |=| mLen (listVar "xs"))))
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ [] []
  
testUseMap = let
  env = addPolyConstant "map" (Forall "a" $ Forall "b" $ Monotype $ 
                                    FunctionT "f" (FunctionT "x" (vartAll "a") (vartAll "b")) 
                                    (FunctionT "xs" (ScalarT listT [vartAll "a"] ftrue) (ScalarT listT [vartAll "b"] $ mLen valList |=| mLen (listVar "xs")))) .
        addConstant "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .            
        addList $ emptyEnv
  typ = Monotype $ FunctionT "xs" (intlist ftrue) (natlist $ mLen valList |=| mLen (listVar "xs"))
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ inequalities0 []  
  
testUseFold1 = let
  env = addPolyConstant "fold1" (Forall "a" $ Monotype $ 
                                    FunctionT "f" (FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (vartAll "a"))) 
                                    (FunctionT "xs" (ScalarT listT [vartAll "a"] $ mLen valList |>| IntLit 0) (vartAll "a"))) .
        addConstant "gcd" (FunctionT "x" pos (FunctionT "y" pos pos)) .
        addList $ emptyEnv
  typ = Monotype $ FunctionT "xs" (poslist $ mLen valList |>| IntLit 0) nat    
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ [] []
  
  
{- Testing Synthesis of Sorted List Programs -}

incListT = DatatypeT "IncList"
incList = ScalarT incListT [vartAll "a"]
incListVar = Var (toSort incListT)
valIncList = incListVar valueVarName

intInclist = ScalarT incListT [intAll]
natInclist = ScalarT incListT [nat]

mILen = Measure IntS "len"
mIElems = Measure (SetS $ UninterpretedS "a") "elems"

polyInequalities = do
        op <- [Ge, Le, Neq]
        return $ Binary op (vartVar "a" "x") (vartVar "a" "y")

-- | Add list datatype to the environment
addIncList = addDatatype "IncList" (Datatype 1 ["Nil", "Cons"] (Just $ mLen)) .
          addPolyConstant "Nil" (Forall "a" $ Monotype $ incList $ mLen valIncList |=| IntLit 0
                                                               |&| mIElems valIncList  |=| SetLit (UninterpretedS "a") []
                                ) .
          addPolyConstant "Cons" (Forall "a" $ Monotype $ FunctionT "x" (vartAll "a") 
                                                         (FunctionT "xs" (ScalarT incListT [vart "a" $ valVart "a" |>=| vartVar "a" "x"] ftrue) 
                                                         (incList $ mLen valIncList |=| mLen (incListVar "xs") |+| IntLit 1
                                                                |&| mIElems valIncList |=| mIElems (incListVar "xs") /+/ SetLit (UninterpretedS "a") [vartVar "a" "x"]
                                                          )))

testMakeIncList = let
  env = addConstant "0" (int (valInt |=| IntLit 0)) .
        addConstant "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
        addConstant "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
        addIncList $ emptyEnv
  typ = Monotype $ natInclist $ mIElems valIncList |=| SetLit IntS [IntLit 0, IntLit 1]
  in testSynthesizeSuccess defaultExplorerParams defaultSolverParams env typ [] []          
  
testIncListInsert = let
  env = addIncList $ emptyEnv
  typ = Forall "a" $ Monotype $ (FunctionT "x" (vartAll "a") (FunctionT "xs" (incList ftrue) (incList $ mIElems valIncList |=| mIElems (incListVar "xs") /+/ SetLit (UninterpretedS "a") [vartVar "a" "x"])))
  in testSynthesizeSuccess (defaultExplorerParams {_eGuessDepth = 2}) defaultSolverParams env typ polyInequalities []          
  
testIncListMerge = let
  env = addPolyConstant "insert" (Forall "a" $ Monotype $ (FunctionT "x" (vartAll "a") (FunctionT "xs" (incList ftrue) (incList $ mIElems valIncList |=| mIElems (incListVar "xs") /+/ SetLit (UninterpretedS "a") [vartVar "a" "x"])))) .
        addIncList $ emptyEnv
  typ = Forall "a" $ Monotype $ (FunctionT "xs" (incList ftrue) (FunctionT "ys" (incList ftrue) (incList $ mIElems valIncList |=| mIElems (incListVar "xs") /+/ mIElems (incListVar "ys"))))
  in testSynthesizeSuccess (defaultExplorerParams {_eGuessDepth = 2}) defaultSolverParams env typ polyInequalities []          
  
-- | Create `Test`s from a parser function and test-cases consisting of an input string and the expected parsed AST.
createParserTestList :: (Show a, Eq a) => Parser a -> [(String, a)] -> Test
createParserTestList parser testCases = TestList $ map createTestCase testCases
  where createTestCase (inputStr, parsedAst) = TestCase $ assertEqual inputStr (Right parsedAst) $ applyParser parser inputStr

testParseScalarType = createParserTestList parseScalarType [
  ("Int", ScalarT IntT [] $ ftrue),
  ("List", ScalarT (DatatypeT "List") [] $ ftrue),
  ("DaT_aType9 (a) ({b | 10 > 1})",
    ScalarT (DatatypeT "DaT_aType9") [ScalarT (TypeVarT "a") [] ftrue, ScalarT (TypeVarT "b") [] $ IntLit 10 |>| IntLit 1] ftrue),
  ("{List | True}", ScalarT (DatatypeT "List") [] $ ftrue)]

testParseFunctionType = createParserTestList parseFunctionType [
  ("(  a : Int -> Int)", FunctionT "a" scalarInt scalarInt),
  ("(___:Int-> (b:{ Bool|  10 > 0}->Int))",
    FunctionT "___" scalarInt (FunctionT "b" (ScalarT BoolT [] $ IntLit 10 |>| IntLit 0) scalarInt)),
  ("(  abc0e93__3_0 : {Int | True} -> (  b:Bool->Int))",
    FunctionT "abc0e93__3_0" (ScalarT IntT [] $ BoolLit True) (FunctionT "b" scalarBool scalarInt))]
  where
    scalarInt = ScalarT IntT [] $ BoolLit True
    scalarBool = ScalarT BoolT [] $ BoolLit True

testParseRefinement = createParserTestList parseFormula testCases
  where
    int = IntLit
    testCases = [
      ("1 + 1", (int 1) |+| (int 1)),
      ("!(-1)", fnot $ fneg $ int 1),
      ("-(!(!1))", fneg $ fnot $ fnot $ int 1),
      ("1 | 10", (int 1) ||| (int 10)),
      ("False & (10)", (ffalse) |&| (int 10)),
      ("(1 + 1) - (4 + 8)", (int 1 |+| int 1) |-| (int 4 |+| int 8)),
      ("(1 + 4 * 3 - 2) * 3 - (2 * 4)", (int 1 |+| (int 4 |*| int 3) |-| int 2) |*| int 3 |-| (int 2 |*| int 4)),
      ("(1 * 9 + 8 - 7 /* 3 <= 3 & 1)", ((((int 1 |*| int 9) |+| int 8 |-| int 7 /*/ int 3) |<=| int 3) |&| int 1)),
      ("8 => 3", (int 8 |=>| int 3)),
      ("True | False => (False & False <=> False)", (ftrue ||| ffalse |=>| ((ffalse |&| ffalse) |<=>| ffalse)))]

testParseTerm = createParserTestList parseTerm [
  ("1", IntLit 1),
  ("123005", IntLit 123005),
  ("True", BoolLit True),
  ("False", BoolLit False),
  ("foobar", Var UnknownS "foobar"),
  ("{    1,   a, 4 ,  True }", SetLit UnknownS [IntLit 1, Var UnknownS "a", IntLit 4, BoolLit True]),
  ("{falseEE}", SetLit UnknownS [Var UnknownS "falseEE"]),
  ("len tail list", Measure UnknownS "len" $ Measure UnknownS "tail" $ Var UnknownS "list"),
  ("foo 1 + 3", Measure UnknownS "foo" $ IntLit 1 |+| IntLit 3)]
