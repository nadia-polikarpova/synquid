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
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Trans.Maybe

nat = int (valueVar |>=| IntLit 0)
intAll = int ftrue
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
  constraintPickStrategy = SmallSpaceConstraint
  }

-- | 'synthesize' @env typ templ cq tq@ : synthesize and print a program that has a type @typ@ 
-- in the typing environment @env@ and follows template @templ@,
-- using conditional qualifiers @cq@ and type qualifiers @tq@
synthesize env typ templ cq tq = do
  let (clauses, qmap, p) = genConstraints consGenParams (toSpace . cq) (toSpace . tq) env typ templ
  
  -- putStr "Liquid Program\n"
  -- print $ pretty p
  -- putStr "\nConstraints\n"
  -- print $ vsep $ map pretty clauses
  putStr "\nQmap\n"
  print $ pretty qmap
  putStr "\n"
  
  mProg <- evalZ3State $ do
    initSolver
    mSol <- solveWithParams solverParams qmap clauses
    case mSol of
      Nothing -> return Nothing
      Just sol -> debug 0 (pretty sol) $ runMaybeT $ extract p sol  
  case mProg of
    Nothing -> putStr "No Solution"
    Just prog -> print $ pretty prog
  
testApp = do
  let env = addSymbol (Var "a") intAll .
            addSymbol (Var "b") intAll .
            addSymbol (Var "dec") (FunctionT "x" intAll (int (valueVar |=| Var "x" |-| IntLit 1))) .
            addSymbol (Var "inc") (FunctionT "x" intAll (int (valueVar |=| Var "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = int (valueVar |>| Var "b")
  let templ = sym (int_ |->| int_) |$| sym int_  
  let tq syms = do
      op <- [Ge, Le, Neq]
      rhs <- syms
      return $ Binary op valueVar rhs
        
  synthesize env typ templ (const []) tq
  
testApp2 = do
  let env = addSymbol (Var "a") intAll .
            addSymbol (Var "dec") (FunctionT "x" intAll (int (valueVar |=| Var "x" |-| IntLit 1))) .
            addSymbol (Var "inc") (FunctionT "x" intAll (int (valueVar |=| Var "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = int (valueVar |=| Var "a")
  let templ = sym (int_ |->| int_) |$| sym (int_ |->| int_) |$| sym int_  
  let tq syms = do
      rhs <- syms
      [valueVar |=| rhs]
      -- [valueVar |=| rhs, valueVar |=| rhs |+| IntLit 1, valueVar |=| rhs |-| IntLit 1]
        
  synthesize env typ templ (const []) tq
  
testLambda = do
  let env = addSymbol (Var "dec") (FunctionT "x" nat (int (valueVar |=| Var "x" |-| IntLit 1))) .
            addSymbol (Var "inc") (FunctionT "x" nat (int (valueVar |=| Var "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = FunctionT "a" nat $ int (valueVar |=| Var "a")
  let templ = int_ |.| sym (int_ |->| int_) |$| sym (int_ |->| int_) |$| sym int_
  let tq0 = [valueVar |>=| IntLit 0]
  let tq1 syms = do
      rhs <- syms
      [valueVar |=| rhs]
      -- [valueVar |=| rhs, valueVar |=| rhs |+| IntLit 1, valueVar |=| rhs |-| IntLit 1]
        
  synthesize env typ templ (const []) (\syms -> tq0 ++ tq1 syms)
  
testMax2 = do
  let env = emptyEnv
  let typ = FunctionT "x" intAll $ FunctionT "y" intAll $ int (valueVar |>=| Var "x" |&| valueVar |>=| Var "y")
  let templ = int_ |.| int_ |.| choice (sym int_) (sym int_)
  
  let cq syms = do
      lhs <- syms
      op <- [Ge, Le, Neq]
      rhs <- syms
      guard $ lhs < rhs
      return $ Binary op lhs rhs  
      
  let tq syms = do
      op <- [Ge, Le, Neq]
      rhs <- syms
      return $ Binary op valueVar rhs      
  
  synthesize env typ templ cq tq  
 
testAbs = do
  let env =             
            addSymbol (Var "id") (FunctionT "x" intAll (int (valueVar |=| Var "x"))) .
            addSymbol (Var "neg") (FunctionT "x" intAll (int (valueVar |=| fneg (Var "x")))) .
            id $ emptyEnv
  let typ = FunctionT "x" intAll $ int (valueVar |>=| Var "x" |&| valueVar |>=| IntLit 0)
  let templ = int_ |.| choice (sym (int_ |->| int_) |$| sym int_) (sym (int_ |->| int_) |$| sym int_)
  
  let cq syms = do
      lhs <- syms
      op <- [Ge, Le, Neq]
      rhs <- syms ++ [IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs  
  let tq0 = [valueVar |<=| IntLit 0, valueVar |>=| IntLit 0, valueVar |/=| IntLit 0]
  let tq1 syms = do
      rhs <- syms
      [valueVar |=| rhs, valueVar |>=| rhs, valueVar |=| fneg rhs]
        
  synthesize env typ templ cq (\syms -> tq0 ++ tq1 syms)
  
testPeano = do
  let env =             
            addSymbol (Var "dec") (FunctionT "x" nat (int (valueVar |=| Var "x" |-| IntLit 1))) .
            addSymbol (Var "inc") (FunctionT "x" nat (int (valueVar |=| Var "x" |+| IntLit 1))) .
            addSymbol (Var "neg") (FunctionT "x" intAll (int (valueVar |=| fneg (Var "x")))) .
            addSymbol (Var "const0") (FunctionT "x" intAll (int (valueVar |=| IntLit 0))) .
            id $ emptyEnv

  let typ = FunctionT "y" nat $ int (valueVar |=| Var "y")
  let templ = fix_ (int_ |->| int_) (int_ |.| choice 
                (sym (int_ |->| int_) |$| sym int_)
                (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_))))
  
  let cq syms = do
      lhs <- syms
      op <- [Ge, Le, Neq]
      rhs <- syms ++ [IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs  
  let tq0 = [valueVar |>=| IntLit 0]
  -- let tq0 = [valueVar |<=| IntLit 0, valueVar |>=| IntLit 0]
  let tq1 syms = do
      rhs <- syms
      [valueVar |=| rhs]
      -- [valueVar |=| rhs, valueVar |=| rhs |+| IntLit 1, valueVar |=| rhs |-| IntLit 1, valueVar |=| fneg rhs]
        
  synthesize env typ templ cq (\syms -> tq0 ++ tq1 syms)
  
testAddition = do
  let env =
            addSymbol (Var "dec") (FunctionT "x" nat (int (valueVar |=| Var "x" |-| IntLit 1))) .
            addSymbol (Var "inc") (FunctionT "x" nat (int (valueVar |=| Var "x" |+| IntLit 1))) .
            id $ emptyEnv

  let typ = FunctionT "y" nat $ FunctionT "z" nat $ int (valueVar |=| Var "y" |+| Var "z")
  -- let templ = fix_ (int_ |->| int_ |->| int_) (int_ |.| int_ |.| choice 
                -- (sym int_) 
                -- (sym (int_ |->| int_) |$| ((sym (int_ |->| int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_)) |$| sym int_)))
  let templ = int_ |.| (fix_ (int_ |->| int_) (int_ |.| choice 
                (sym int_) 
                (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_)))))
  
  let cq syms = do
      lhs <- syms ++ [IntLit 0]
      op <- [Le, Ge, Neq]
      rhs <- syms ++ [IntLit 0]
      guard $ lhs < rhs
      return $ Binary op lhs rhs  
  let tq0 = [valueVar |<=| IntLit 0, valueVar |>=| IntLit 0]
  let tq1 syms = do
      rhs <- syms
      [valueVar |=| rhs]
      -- [valueVar |=| rhs, valueVar |=| rhs |-| IntLit 1, valueVar |=| rhs |+| IntLit 1]
  let tq2 syms = do
      rhs1 <- syms
      rhs2 <- syms
      guard $ rhs1 /= rhs2
      [valueVar |=| rhs1 |+| rhs2]
      -- [valueVar |=| rhs1 |+| rhs2, valueVar |=| rhs1 |+| rhs2 |+| IntLit 1, valueVar |=| rhs1 |+| rhs2 |-| IntLit 1]
        
  synthesize env typ templ cq (\syms -> tq0 ++ tq1 syms ++ tq2 syms)
  
main = testAddition