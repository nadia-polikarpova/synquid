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

(|++|) gen gen' = \symbs -> gen symbs ++ gen' symbs
infixr 5  |++|

toSpace quals = QSpace quals (length quals)

consGenParams = ConsGenParams {
  bottomUp = True,
  abstractLeaves = True,
  abstractFix = True
}

-- | Search parameters
solverParams = SolverParams {
  -- pruneQuals = True,
  pruneQuals = False,
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
      Just sol -> debug 0 (pretty sol) $ runMaybeT $ extract sol p
  case mProg of
    Nothing -> putStr "No Solution"
    Just prog -> print $ programDoc pretty pretty (const empty) prog
    
-- | Integer programs    
  
testApp = do
  let env = addSymbol "a" intAll .
            addSymbol "b" intAll .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = int (valInt |>| intVar "b")
  let templ = sym (int_ |->| int_) |$| sym int_  
  let tq (_ : syms) = do
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
  let tq (_ : syms) = do
      rhs <- syms
      [valInt |=| rhs]
      -- [valInt |=| rhs, valInt |=| rhs |+| IntLit 1, valInt |=| rhs |-| IntLit 1]
        
  synthesize env typ templ (const []) tq
  
testLambda = do
  let env = addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv
  let typ = FunctionT "a" nat $ int (valInt |=| intVar "a")
  let templ = int_ |.| sym (int_ |->| int_) |$| sym (int_ |->| int_) |$| sym int_
  let tq0 _ = [valInt |>=| IntLit 0]
  let tq1 (_ : syms) = do
      rhs <- syms
      [valInt |=| rhs]
      -- [valInt |=| rhs, valInt |=| rhs |+| IntLit 1, valInt |=| rhs |-| IntLit 1]
        
  synthesize env typ templ (const []) (tq0 |++| tq1)
  
testMax2 = do
  let env = emptyEnv
  let typ = FunctionT "x" intAll $ FunctionT "y" intAll $ int (valInt |>=| intVar "x" |&| valInt |>=| intVar "y")
  let templ = int_ |.| int_ |.| choice (sym int_) (sym int_)
  
  let cq syms = do
      lhs <- syms
      op <- [Ge, Le, Neq]
      rhs <- syms
      guard $ lhs < rhs
      return $ Binary op lhs rhs  
      
  let tq (_ : syms) = do
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
  let templ = int_ |.| choice (sym (int_ |->| int_) |$| sym int_) (sym (int_ |->| int_) |$| sym int_)
  
  let cq syms = do
      lhs <- syms
      op <- [Ge, Le, Neq]
      rhs <- syms ++ [IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs  
  let tq0 _ = [valInt |<=| IntLit 0, valInt |>=| IntLit 0, valInt |/=| IntLit 0]
  let tq1 (_ : syms) = do
      rhs <- syms
      [valInt |=| rhs, valInt |>=| rhs, valInt |=| fneg rhs]
        
  synthesize env typ templ cq (tq0 |++| tq1)
  
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
  
  let cq syms = do
      lhs <- syms
      op <- [Ge, Le, Neq]
      rhs <- syms ++ [IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs  
  let tq0 _ = [valInt |>=| IntLit 0]
  -- let tq0 _ = [valInt |<=| IntLit 0, valInt |>=| IntLit 0]
  let tq1 (_ : syms) = do
      rhs <- syms
      [valInt |=| rhs]
      -- [valInt |=| rhs, valInt |=| rhs |+| IntLit 1, valInt |=| rhs |-| IntLit 1, valInt |=| fneg rhs]
        
  synthesize env typ templ cq (tq0 |++| tq1)
  
testAddition = do
  let env =
            addSymbol "dec" (FunctionT "x" nat (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" nat (int (valInt |=| intVar "x" |+| IntLit 1))) .
            id $ emptyEnv

  let typ = FunctionT "y" nat $ FunctionT "z" nat $ int (valInt |=| intVar "y" |+| intVar "z")
  -- let templ = fix_ (int_ |.| int_ |.| choice 
                -- (sym int_) 
                -- (sym (int_ |->| int_) |$| ((sym (int_ |->| int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_)) |$| sym int_)))
  let templ = int_ |.| (fix_ (int_ |.| choice 
                (sym int_) 
                (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_)))))
  
  let cq syms = do
      lhs <- syms ++ [IntLit 0]
      op <- [Le, Ge, Neq]
      rhs <- syms ++ [IntLit 0]
      guard $ lhs < rhs
      return $ Binary op lhs rhs  
  let tq0 _ = [valInt |<=| IntLit 0, valInt |>=| IntLit 0]
  let tq1 (_ : syms) = do
      rhs <- syms
      []
      -- [valInt |=| rhs, valInt |=| rhs |-| IntLit 1, valInt |=| rhs |+| IntLit 1]
  let tq2 (_ : syms) = do
      rhs1 <- syms
      rhs2 <- syms
      guard $ rhs1 < rhs2
      [valInt |=| rhs1 |+| rhs2]
      -- [valInt |=| rhs1 |+| rhs2, valInt |=| rhs1 |+| rhs2 |+| IntLit 1, valInt |=| rhs1 |+| rhs2 |-| IntLit 1]
        
  synthesize env typ templ cq (tq0 |++| tq1 |++| tq2)
  
-- | List programs  
  
-- addLists =  
            -- addSymbol "head" (FunctionT "xs" (list $ valList |/=| listVar "nil") (int $ valInt `fin` Measure SetT "elems" (listVar "xs"))) .
            -- addSymbol "tail" (FunctionT "xs" (list $ valList |/=| listVar "nil") (list $ Measure IntT "len" valList |=| Measure IntT "len" (listVar "xs") |-| IntLit 1 |&|
                                                                                         -- Measure SetT "elems" valList /<=/ Measure IntT "elems" (listVar "xs")))
  
testReplicate = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            id $ listEnv

  let typ = FunctionT "n" nat (FunctionT "y" intAll (list $ Measure IntT "len" valList |=| intVar "n" |&| Measure SetT "elems" valList /<=/ SetLit [intVar "y" |+| IntLit 1]))
  let templ = fix_ (int_ |.| int_ |.| choice
                (sym list_)
                ((sym (int_ |->| list_ |->| list_) |$| (sym (int_ |->| int_) |$| sym int_)) |$| (sym (int_ |->| int_ |->| list_) |$| (sym (int_ |->| int_) |$| sym int_)) |$| sym int_))
          
  let cq syms = do
      lhs <- syms
      guard $ baseTypeOf lhs == IntT
      op <- [Le, Ge, Neq]
      rhs <- syms
      guard $ baseTypeOf rhs == IntT
      guard $ lhs < rhs
      return $ Binary op lhs rhs            
  let tq (val : syms) = case val of
                          Var ListT _ -> do  
                                            rhs <- syms
                                            guard $ baseTypeOf rhs == IntT
                                            [Measure IntT "len" val |=| rhs, Measure SetT "elems" val /<=/ SetLit [rhs |+| IntLit 1]]
                          Var IntT _ -> do
                                            rhs <- syms
                                            guard $ baseTypeOf rhs == IntT                          
                                            [val |<=| rhs, val |>=| rhs]
          
  synthesize env typ templ cq tq
  
testLength = do
  let env = addSymbol "0" (int (valInt |=| IntLit 0)) .
            addSymbol "dec" (FunctionT "x" intAll (int (valInt |=| intVar "x" |-| IntLit 1))) .
            addSymbol "inc" (FunctionT "x" intAll (int (valInt |=| intVar "x" |+| IntLit 1))) .  
            id $ listEnv

  let typ = FunctionT "l" listAll (int $ IntLit 0 |<=| valInt |&| valInt |=| Measure IntT "len" (listVar "l"))
  let templ = fix_ (list_ |.| match (sym list_)
                (sym int_)
                (sym (int_ |->| int_) |$| (sym (list_ |->| int_) |$| sym list_)))
          
  let tq (val : syms) = case val of
                          Var ListT _ -> []
                          Var IntT _ -> do
                                            rhs <- syms
                                            if baseTypeOf rhs == ListT
                                              then [val |=| Measure IntT "len" rhs]
                                              else [val |<=| rhs, val |>=| rhs]
          
  synthesize env typ templ (const []) tq
  
testConcat = do
  let env = id $ listEnv

  let typ = FunctionT "xs" listAll (FunctionT "ys" listAll (list $ Measure IntT "len" valList |=| Measure IntT "len" (listVar "xs") |+| Measure IntT "len" (listVar "ys")))
  let templ = fix_ (list_ |.| list_ |.| match (sym list_) 
                (sym list_) 
                ((sym (int_ |->| list_ |->| list_) |$| 
                  (sym int_)) |$| 
                  ((sym (list_ |->| list_ |->| list_) |$| (sym list_)) |$| (sym list_))))
                
          
  let tq1 (val : syms) = case val of
                          Var ListT _ -> []
                          Var IntT _ -> do
                                            rhs <- syms
                                            guard $ baseTypeOf rhs == IntT
                                            [val |<=| rhs, val |>=| rhs]
                                              
  let tq2 (val : syms) = case val of
                          Var ListT _ -> do
                              rhs1 <- syms
                              rhs2 <- syms
                              guard $ rhs1 < rhs2
                              guard $ baseTypeOf rhs1 == ListT
                              guard $ baseTypeOf rhs2 == ListT
                              [Measure IntT "len" valList |=| Measure IntT "len" rhs1 |+| Measure IntT "len" rhs2]
                          Var IntT _ -> []

          
  synthesize env typ templ (const []) (tq1 |++| tq2)
  
  
  
-- main = testApp
-- main = testApp2
-- main = testLambda
-- main = testMax2
-- main = testAbs  
-- main = testPeano  
-- main = testAddition
-- main = testReplicate
-- main = testLength
main = testConcat

-- main = do
  -- res <- evalZ3State $ do
    -- initSolver
    -- isValid $ SetLit [IntLit 2, IntLit 1] |=| SetLit [IntLit 1, IntLit 2]
  -- print res
