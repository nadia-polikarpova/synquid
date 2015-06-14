module Main where

import Synquid.Util
import Synquid.Logic
import Synquid.Solver
import Synquid.SMTSolver
import Synquid.Z3
import Synquid.Program
import Synquid.Pretty
import Synquid.ConstraintGenerator

import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Bimap as BMap
import Data.Bimap (Bimap)
import Control.Monad
import Control.Lens
import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Control.Monad.Trans.Maybe

nat = int (valInt |>=| IntLit 0)
intAll = int ftrue
listAll = list ftrue
intVar = Var IntT
toSpace quals = QSpace quals (length quals)

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

-- | 'synthesize' @env typ templ cq tq@ : synthesize and print a program that has a type @typ@ 
-- in the typing environment @env@ and follows template @templ@,
-- using conditional qualifiers @cq@ and type qualifiers @tq@
synthesize env typ templ cq tq = do
  let (clauses, qmap, p) = genConstraints consGenParams (toSpace . cq) (toSpace . tq) env typ templ
  
  putStr "Liquid Program\n"
  print $ pretty p
  -- putStr "\nConstraints\n"
  -- print $ vsep $ map pretty clauses
  putStr "\nQmap\n"
  print $ pretty qmap
  putStr "\n"
  
  mProg <- evalZ3State $ do
    initSolver
    mSol <- solveWithParams solverParams qmap clauses (candidateDoc p)
    case mSol of
      Nothing -> return Nothing
      Just sol -> debug 0 (pretty sol) $ runMaybeT $ extract p sol  
  case mProg of
    Nothing -> putStr "No Solution"
    Just prog -> print $ programDoc pretty pretty (const empty) prog
  
testApp = do
  let env = addSymbol "a" intAll .
            addSymbol "b" intAll .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = int (valInt |>| intVar "b")
  let templ = sym (int_ |->| int_) |$| sym int_  
  let tq syms = do
      op <- [Ge, Le, Neq]
      rhs <- syms
      return $ Binary op valInt rhs
        
  synthesize env typ templ (const []) tq
  
testApp2 = do
  let env = addSymbol "a" intAll .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = int (valInt |=| intVar "a")
  let templ = sym (int_ |->| int_) |$| sym (int_ |->| int_) |$| sym int_  
  let tq syms = do
      rhs <- syms
      [valInt |=| rhs]
      -- [valInt |=| rhs, valInt |=| rhs |+| IntLit 1, valInt |=| rhs |-| IntLit 1]
        
  synthesize env typ templ (const []) tq
  
testLambda = do
  let env = addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = FunctionT "a" nat $ int (valInt |=| intVar "a")
  let templ = "a" |.| sym (int_ |->| int_) |$| sym (int_ |->| int_) |$| sym int_
  let tq0 = [valInt |>=| IntLit 0]
  let tq1 syms = do
      rhs <- syms
      [valInt |=| rhs]
      -- [valInt |=| rhs, valInt |=| rhs |+| IntLit 1, valInt |=| rhs |-| IntLit 1]
        
  synthesize env typ templ (const []) (\syms -> tq0 ++ tq1 syms)
  
testMax2 = do
  let env = emptyEnv
  let typ = FunctionT "x" intAll $ FunctionT "y" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y")
  let templ = "x" |.| "y" |.| choice (sym int_) (sym int_)
  
  let cq syms = do
      lhs <- syms
      op <- [Ge, Le, Neq]
      rhs <- syms
      guard $ lhs < rhs
      return $ Binary op lhs rhs  
      
  let tq syms = do
      op <- [Ge, Le, Neq]
      rhs <- syms
      return $ Binary op valInt rhs      
  
  synthesize env typ templ cq tq  
 
testAbs = do
  let env =             
            addSymbol "id" (FunctionT "x" intAll (int (valInt |=| intVar "x"))) .
            addSymbol "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .
            id $ emptyEnv
  let typ = FunctionT "x" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| IntLit 0)
  let templ = "x" |.| choice (sym (int_ |->| int_) |$| sym int_) (sym (int_ |->| int_) |$| sym int_)
  
  let cq syms = do
      lhs <- syms
      op <- [Ge, Le, Neq]
      rhs <- syms ++ [IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs  
  let tq0 = [valInt |<=| IntLit 0, valInt |>=| IntLit 0, valInt |/=| IntLit 0]
  let tq1 syms = do
      rhs <- syms
      [valInt |=| rhs, valInt |>=| rhs, valInt |=| fneg rhs]
        
  synthesize env typ templ cq (\syms -> tq0 ++ tq1 syms)
  
testPeano = do
  let env =             
            addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            addSymbol "neg" (FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))) .
            addSymbol "const0" (FunctionT "x" intAll (int (valInt |=| IntLit 0))) .
            id $ emptyEnv

  let typ = FunctionT "y" nat $ int (valInt |=| intVar "y")
  let templ = fix_ "f" ("y" |.| choice 
                (sym (int_ |->| int_) |$| sym int_)
                (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_))))
  
  let cq syms = do
      lhs <- syms
      op <- [Ge, Le, Neq]
      rhs <- syms ++ [IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs  
  let tq0 = [valInt |>=| IntLit 0]
  -- let tq0 = [valInt |<=| IntLit 0, valInt |>=| IntLit 0]
  let tq1 syms = do
      rhs <- syms
      [valInt |=| rhs]
      -- [valInt |=| rhs, valInt |=| rhs |+| IntLit 1, valInt |=| rhs |-| IntLit 1, valInt |=| fneg rhs]
        
  synthesize env typ templ cq (\syms -> tq0 ++ tq1 syms)
  
testAddition = do
  let env =
            addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv

  let typ = FunctionT "y" nat $ FunctionT "z" nat $ int (valInt |=| intVar "y" |+| intVar "z")
  -- let templ = fix_ "plus" ("y" |.| "z" |.| choice 
                -- (sym int_) 
                -- (sym (int_ |->| int_) |$| ((sym (int_ |->| int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_)) |$| sym int_)))
  let templ = "y" |.| (fix_ "y_plus" ("z" |.| choice 
                (sym int_) 
                (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_)))))
  
  let cq syms = do
      lhs <- syms ++ [IntLit 0]
      op <- [Le, Ge, Neq]
      rhs <- syms ++ [IntLit 0]
      guard $ lhs < rhs
      return $ Binary op lhs rhs  
  let tq0 = [valInt |<=| IntLit 0, valInt |>=| IntLit 0]
  let tq1 syms = do
      rhs <- syms
      []
      -- [valInt |=| rhs, valInt |=| rhs |-| IntLit 1, valInt |=| rhs |+| IntLit 1]
  let tq2 syms = do
      rhs1 <- syms
      rhs2 <- syms
      guard $ rhs1 < rhs2
      [valInt |=| rhs1 |+| rhs2]
      -- [valInt |=| rhs1 |+| rhs2, valInt |=| rhs1 |+| rhs2 |+| IntLit 1, valInt |=| rhs1 |+| rhs2 |-| IntLit 1]
        
  synthesize env typ templ cq (\syms -> tq0 ++ tq1 syms ++ tq2 syms)
  
testReplicate = do
  let env =
            addSymbol "nil" (ScalarT ListT ftrue) .
            addSymbol "cons" (FunctionT "x" intAll (FunctionT "xs" listAll listAll)) .
            id $ emptyEnv

  let typ = FunctionT "y" intAll $ listAll
  let templ = "y" |.| 
                ((sym (int_ |->| list_ |->| list_) |$| sym int_) |$| (sym (int_ |->| list_ |->| list_) |$| sym int_) |$| sym list_)
          
  synthesize env typ templ (const []) (const [])  
  
-- main = testApp
-- main = testApp2
-- main = testLambda
-- main = testMax2
-- main = testAbs  
-- main = testPeano  
-- main = testAddition
main = testReplicate