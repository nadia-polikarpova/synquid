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

-- Search parameters  

defaultParams = SolverParams {
    pruneQuals = True,
    -- pruneQuals = False,
    -- optimalValuationsStrategy = UnsatCoreValuations,
    optimalValuationsStrategy = MarcoValuations,    
    -- optimalValuationsStrategy = BFSValuations,    
    semanticPrune = True,
    -- agressivePrune = True,
    -- semanticPrune = False,
    agressivePrune = False,    
    candidatePickStrategy = InitializedCandidate,
    -- candidatePickStrategy = UniformCandidate,
    constraintPickStrategy = SmallSpaceConstraint
  }
  
nat = int (valueVar |>=| IntLit 0)
intAll = int ftrue

main = do
  let env =             
            -- addSymbol (IntLit 0) (int (valueVar |=| IntLit 0)) .           
            addSymbol (Var "dec") (FunctionT "x" nat (int (valueVar |=| Var "x" |-| IntLit 1))) .
            -- addSymbol (Var "id") (FunctionT "x" intAll (int (valueVar |=| Var "x"))) .
            addSymbol (Var "inc") (FunctionT "x" nat (int (valueVar |=| Var "x" |+| IntLit 1))) .
            -- addSymbol (Var "neg") (FunctionT "x" intAll (int (valueVar |=| fneg (Var "x")))) .
            -- addSymbol (Var "plus") (FunctionT "x" intAll $ FunctionT "y" (int ftrue) $ int (valueVar |=| Var "x" |+| Var "y")) .
            addSymbol (Var "const0") (FunctionT "x" intAll (int (valueVar |=| IntLit 0))) .
            -- addSymbol (Var "a") nat .
            -- addSymbol (Var "b") nat .
            -- addSymbol (Var "f") (FunctionT "x" (int (IntLit 0 |<=| valueVar |&| valueVar |<| Var "y")) (int (valueVar |=| Var "x"))) .
            id $ emptyEnv

  -- Peano
  let typ = FunctionT "y" nat $ int (valueVar |=| Var "y")
  -- let typ = int (valueVar |=| Var "y")
  -- let templ = fix_ (int_ |->| int_) (int_ |.| (sym (int_ |->| int_) |$| sym int_))
  -- let templ = int_ |.| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_))
  -- let templ = fix_ (int_ |->| int_) (int_ |.| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_))))
  let templ = fix_ (int_ |->| int_) (int_ |.| choice 
                (sym (int_ |->| int_) |$| sym int_) 
                (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_))))
              
  -- -- max2:
  -- let typ = FunctionT "x" (int ftrue) $ FunctionT "y" (int ftrue) $ int (valueVar |>=| Var "x" |&| valueVar |>=| Var "y")
  -- let templ = int_ |.| int_ |.| choice (sym int_) (sym int_)

  -- -- abs:
  -- let typ = FunctionT "x" (int ftrue) $ int (valueVar |>=| Var "x" |&| valueVar |>=| IntLit 0)
  -- let templ = int_ |.| choice (sym (int_ |->| int_) |$| sym int_) (sym (int_ |->| int_) |$| sym int_)
  
  -- -- application
  -- let typ = FunctionT "y" nat $ int (valueVar |=| Var "y")
  -- let templ = int_ |.| sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_))
  -- -- let templ = int_ |.| sym (int_ |->| int_) |$| sym int_
  
  -- -- const
  -- let typ = FunctionT "y" nat $ int (valueVar |>| Var "y")
  -- let templ = sym (int_ |->| int_)
  
  let (clauses, qmap, p) = genConstraints (toSpace . cq) (toSpace . \syms -> tq syms ++ [valueVar |<=| IntLit 0, valueVar |>=| IntLit 0]) env typ templ
  
  -- putStr "Liquid Program\n"
  -- print $ pretty p
  -- putStr "\nConstraints\n"
  -- print $ vsep $ map pretty clauses
  putStr "\nQmap\n"
  print $ pretty qmap
  putStr "\n"
  
  mProg <- evalZ3State $ do
    initSolver
    mSol <- solveWithParams defaultParams qmap clauses
    case mSol of
      Nothing -> return Nothing
      Just sol -> runMaybeT $ extract p sol
  case mProg of
    Nothing -> putStr "No Solution"
    Just prog -> print $ pretty prog
  where
    cq syms = do
      lhs <- syms
      op <- [Ge, Le, Neq]
      rhs <- syms ++ [IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs  
    -- tq syms = do
      -- lhs <- valueVar:syms
      -- op <- [Ge, Le, Neq]
      -- rhs <- valueVar:syms
      -- guard $ (lhs == valueVar || rhs == valueVar) && lhs /= rhs
      -- return $ Binary op lhs rhs
    tq syms = do
      rhs <- syms
      [valueVar |=| rhs, valueVar |=| rhs |+| IntLit 1, valueVar |=| rhs |-| IntLit 1] --, valueVar |=| fneg rhs]
    toSpace quals = QSpace quals (length quals)
