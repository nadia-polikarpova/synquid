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

-- -- Conditionals

-- condQualsRich :: [Id] -> [Formula]  
-- condQualsRich vars = do
  -- lhs <- map Var vars ++ [IntLit 0]
  -- op <- [Ge, Neq]
  -- rhs <- map Var vars ++ [IntLit 0]
  -- guard $ lhs /= rhs
  -- return $ Binary op lhs rhs
  
-- condQuals :: [Id] -> [Formula]  
-- condQuals vars = do
  -- lhs <- map Var vars
  -- op <- [Ge, Neq]
  -- rhs <- map Var vars
  -- guard $ lhs /= rhs
  -- return $ Binary op lhs rhs
  
-- condQualsLinearEq :: Integer -> Id -> Id -> [Formula]  
-- condQualsLinearEq n x v = map (\i -> Var v |=| (Var x |+| IntLit i)) [0.. (2*n)] 
  -- -- ++ map (\i -> Var v |=| (fneg (Var x) |+| IntLit i)) [0..n]
  
-- -- Variables  

-- varQual res vars = do
  -- var <- map Var vars
  -- return $ Var res |=| var
    
-- extractVar res (Binary Eq (Var v) (Var x))
  -- | v == res  =  PSymbol x
-- extractVar _ (BoolLit True) = PSymbol "??"
-- extractVar res t =  error $ "extractVar got a non-variable type: " ++ show t  
  
-- -- Constants  

-- constZero res = Var res |=| IntLit 0
-- constOne res = Var res |=| IntLit 1

-- constQualInt res = map ($ res) [constZero, constOne]

-- extractConstInt res q = case elemIndex q (constQualInt res) of
  -- Just 0 -> PSymbol "0"
  -- Just 1 -> PSymbol "1"
  -- Nothing -> error $ "extractConstInt got a non-existing type: " ++ show q  
  
-- constId arg res = Var res |=| Var arg
-- constNeg arg res = Var res |=| fneg (Var arg)
-- constInc arg res = Var res |=| (Var arg |+| IntLit 1)
-- constDec arg res = Var res |=| (Var arg |-| IntLit 1)

-- constQualIntInt arg res = map (\f -> f arg res) [constId, constNeg, constInc, constDec]

-- extractConstIntInt arg res q = case elemIndex q (constQualIntInt arg res) of
  -- Just 0 -> PSymbol "id"
  -- Just 1 -> PSymbol "(-)"
  -- Just 2 -> PSymbol "inc"
  -- Just 3 -> PSymbol "dec"  
  -- Nothing -> error $ "extractConstIntInt " ++ arg ++ " " ++ res ++ " got a non-existing type: " ++ show q  
    
-- pruneQualsParams = defaultParams { pruneQuals = True } -- , candidatePickStrategy = FirstConstraint }
  
-- -- Test cases  
    
-- testMax2Synthesize = do
  -- let vars = ["x", "y"]
  -- let quals = Map.fromList [
                -- -- ("cond", QSpace (condQualsRich vars) 2),
                -- ("cond", QSpace (condQualsRich vars) (length $ condQualsRich vars)),
                -- ("then", QSpace (varQual "v" vars) 1),
                -- ("else", QSpace (varQual "v" vars) 1)
              -- ]
  -- let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v")
  -- let fmls = [  Unknown "cond" |&| Unknown "then" |=>| maxType,
                -- Unknown "else" |=>| maxType ||| Unknown "cond"
                -- ]              
  -- mSol <- evalZ3State $ initSolver >> solveWithParams pruneQualsParams quals fmls
  -- case mSol of
    -- Nothing -> putStr "No solution"
    -- Just sol -> let
                  -- val ident = conjunction $ valuation sol ident
                  -- res = PIf (val "cond") (extractVar "v" $ val "then") (extractVar "v" $ val "else") 
                -- in print $ pretty res  
                                
-- max3 sol = let val ident = conjunction $ valuation sol ident
  -- in PIf (val "cond1") 
        -- (PIf (val "cond2") (extractVar "v" $ val "then2") (extractVar "v" $ val "else2")) 
        -- (PIf (val "cond3") (extractVar "v" $ val "then3") (extractVar "v" $ val "else3"))
        
-- testMax3Synthesize1Old = do
  -- let vars = ["x", "y", "z"]
  -- let quals = Map.fromList [
                -- ("cond1", QSpace (condQuals vars) 2),
                -- ("condF1", QSpace (condQuals vars) 2),
                -- ("cond2", QSpace (condQuals vars) 2),
                -- ("condF2", QSpace (condQuals vars) 2),
                -- ("cond3", QSpace (condQuals vars) 2),
                -- ("condF3", QSpace (condQuals vars) 2),
                -- ("then2", QSpace (varQual "v" vars) 1),
                -- ("else2", QSpace (varQual "v" vars) 1),
                -- ("then3", QSpace (varQual "v" vars) 1),
                -- ("else3", QSpace (varQual "v" vars) 1)
              -- ]
  -- let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v") |&| (Var "z" |<=| Var "v")
  -- let fmls = [  
                -- Unknown "cond1" |&| Unknown "cond2" |&| Unknown "then2" |=>| maxType,
                -- Unknown "cond1" |&| Unknown "condF2" |&| Unknown "else2" |=>| maxType,
                -- Unknown "condF1" |&| Unknown "cond3" |&| Unknown "then3" |=>| maxType,
                -- Unknown "condF1" ||| Unknown "condF3" |&| Unknown "else3" |=>| maxType,
                -- BoolLit True |=>| (Unknown "cond1" ||| Unknown "condF1"),
                -- BoolLit True |=>| (Unknown "cond2" ||| Unknown "condF2"),
                -- BoolLit True |=>| (Unknown "cond3" ||| Unknown "condF3")
                -- ]
  -- mSol <- (evalZ3State $ initSolver >> solveWithParams pruneQualsParams quals fmls)
  -- case mSol of
    -- Nothing -> putStr "No solution"
    -- Just sol -> print $ pretty $ max3 sol        
  
-- testMax3Synthesize1New = do
  -- let vars = ["x", "y", "z"]
  -- let quals = Map.fromList [
                -- -- ("cond1", QSpace (condQuals vars) (length $ condQuals vars)),
                -- -- ("cond2", QSpace (condQuals vars) (length $ condQuals vars)),
                -- -- ("cond3", QSpace (condQuals vars) (length $ condQuals vars)),
                -- ("cond1", QSpace (condQuals vars) 2),
                -- ("cond2", QSpace (condQuals vars) 2),
                -- ("cond3", QSpace (condQuals vars) 2),
                -- ("then2", QSpace (varQual "v" vars) 1),
                -- ("else2", QSpace (varQual "v" vars) 1),
                -- ("then3", QSpace (varQual "v" vars) 1),
                -- ("else3", QSpace (varQual "v" vars) 1)
              -- ]
  -- let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v") |&| (Var "z" |<=| Var "v")
  -- let fmls = [  
                -- Unknown "cond1" |&| Unknown "cond2" |&| Unknown "then2" |=>| maxType,
                -- Unknown "cond1" |&| Unknown "else2" |=>| maxType ||| Unknown "cond2",
                -- Unknown "cond3" |&| Unknown "then3" |=>| maxType ||| Unknown "cond1",
                -- Unknown "else3" |=>| maxType ||| Unknown "cond1" ||| Unknown "cond3"
                -- ]
  -- mSol <- (evalZ3State $ initSolver >> solveWithParams pruneQualsParams quals fmls)
  -- case mSol of
    -- Nothing -> putStr "No solution"
    -- Just sol -> print $ pretty $ max3 sol
    
-- testMax3Synthesize2Old = do
  -- let vars = ["x", "y", "z"]
  -- let quals = Map.fromList [
                -- ("cond1", QSpace (condQuals vars) 2),
                -- ("condF1", QSpace (condQuals vars) 2),
                -- ("cond2", QSpace (condQuals vars) 2),
                -- ("condF2", QSpace (condQuals vars) 2),
                -- ("cond3", QSpace (condQuals vars) 2),
                -- ("condF3", QSpace (condQuals vars) 2),                
                -- ("then1", QSpace (condQuals $ vars ++ ["v"]) 2),
                -- ("else1", QSpace (condQuals $ vars ++ ["v"]) 2),                
                -- ("then2", QSpace (varQual "v" vars) 1),
                -- ("else2", QSpace (varQual "v" vars) 1),
                -- ("then3", QSpace (varQual "v" vars) 1),
                -- ("else3", QSpace (varQual "v" vars) 1)
              -- ]
  -- let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v") |&| (Var "z" |<=| Var "v")
  -- let fmls = [  Unknown "cond1" |&| Unknown "then1" |=>| maxType,
                -- Unknown "condF1" |&| Unknown "else1" |=>| maxType,
                -- Unknown "cond2" |&| Unknown "then2" |=>| Unknown "then1",
                -- Unknown "condF2" |&| Unknown "else2" |=>| Unknown "then1",
                -- Unknown "cond3" |&| Unknown "then3" |=>| Unknown "else1",
                -- Unknown "condF3" |&| Unknown "else3" |=>| Unknown "else1",
                -- BoolLit True |=>| (Unknown "cond1" ||| Unknown "condF1"),
                -- BoolLit True |=>| (Unknown "cond2" ||| Unknown "condF2"),
                -- BoolLit True |=>| (Unknown "cond3" ||| Unknown "condF3")                
                -- ]                
  -- mSol <- (evalZ3State $ initSolver >> solveWithParams pruneQualsParams quals fmls)
  -- case mSol of
    -- Nothing -> putStr "No solution"
    -- Just sol -> print $ pretty $ max3 sol      
  
-- testMax3Synthesize2New = do
  -- let vars = ["x", "y", "z"]
  -- let quals = Map.fromList [
                -- ("cond1", QSpace (condQuals vars) 2),
                -- ("cond2", QSpace (condQuals vars) 2),
                -- ("cond3", QSpace (condQuals vars) 2),
                -- ("then1", QSpace (condQuals $ vars ++ ["v"]) 2),
                -- ("else1", QSpace (condQuals $ vars ++ ["v"]) 2),                
                -- ("then2", QSpace (varQual "v" vars) 1),
                -- ("else2", QSpace (varQual "v" vars) 1),
                -- ("then3", QSpace (varQual "v" vars) 1),
                -- ("else3", QSpace (varQual "v" vars) 1)
              -- ]
  -- let maxType = (Var "x" |<=| Var "v") |&| (Var "y" |<=| Var "v") |&| (Var "z" |<=| Var "v")
  -- let fmls = [  Unknown "cond1" |&| Unknown "then1" |=>| maxType,
                -- Unknown "else1" |=>| maxType ||| Unknown "cond1",
                -- Unknown "cond2" |&| Unknown "then2" |=>| Unknown "then1" ||| fnot (Unknown "cond1"),
                -- Unknown "else2" |=>| Unknown "then1" ||| Unknown "cond2" ||| fnot (Unknown "cond1"),
                -- Unknown "cond3" |&| Unknown "then3" |=>| Unknown "else1" ||| Unknown "cond1",
                -- Unknown "else3" |=>| Unknown "else1" ||| Unknown "cond1" ||| Unknown "cond3"
                -- ]                
  -- mSol <- (evalZ3State $ initSolver >> solveWithParams pruneQualsParams quals fmls)
  -- case mSol of
    -- Nothing -> putStr "No solution"
    -- Just sol -> print $ pretty $ max3 sol  
      
-- pAbs sol = let val ident = conjunction $ valuation sol ident
  -- in PIf (val "cond") 
        -- (PApp (extractConstIntInt "y" "v" $ val "fun1") (extractVar "y" $ val "arg1"))                
        -- (PApp (extractConstIntInt "z" "v" $ val "fun2") (extractVar "z" $ val "arg2"))                
        
-- noAgressiveParams = defaultParams { pruneQuals = True, agressivePrune = False, candidatePickStrategy = UniformCandidate }        
        
-- testAbsSynthesize1 = do
  -- let vars = ["x"]
  -- let quals = Map.fromList [
                -- ("cond", QSpace (condQualsRich vars) 2),
                -- ("arg1", QSpace (varQual "y" vars) 1),
                -- ("fun1", QSpace (constQualIntInt "y" "v") 1),
                -- ("arg2", QSpace (varQual "z" vars) 1),
                -- ("fun2", QSpace (constQualIntInt "z" "v") 1)
              -- ]
  -- let absType = (Var "v" |>=| IntLit 0) |&| (Var "v" |>=| Var "x")
  -- let fmls = [  Unknown "cond" |&| Unknown "arg1" |&| Unknown "fun1" |=>| absType,
                -- Unknown "arg2" |&| Unknown "fun2" |=>| absType ||| Unknown "cond"
              -- ]                
  -- mSol <- (evalZ3State $ initSolver >> solveWithParams noAgressiveParams quals fmls)
  -- case mSol of
    -- Nothing -> putStr "No solution"
    -- Just sol -> print $ pretty $ pAbs sol    
    
-- testAbsSynthesize2 = do
  -- let vars = ["x"]
  -- let quals = Map.fromList [
                -- ("cond", QSpace (condQualsRich vars) 2),
                -- ("then", QSpace (condQualsRich $ vars ++ ["v"]) 2),
                -- ("else", QSpace (condQualsRich $ vars ++ ["v"]) 2),
                -- ("arg1", QSpace (varQual "y" vars) 1),
                -- ("fun1", QSpace (constQualIntInt "y" "v") 1),
                -- ("arg2", QSpace (varQual "z" vars) 1),
                -- ("fun2", QSpace (constQualIntInt "z" "v") 1)
              -- ]
  -- let absType = (Var "v" |>=| IntLit 0) |&| (Var "v" |>=| Var "x")
  -- let fmls = [  Unknown "cond" |&| Unknown "then" |=>| absType,
                -- Unknown "else" |=>| absType ||| Unknown "cond",
                -- Unknown "arg1" |&| Unknown "fun1" |=>| Unknown "then" ||| fnot (Unknown "cond"),
                -- Unknown "arg2" |&| Unknown "fun2" |=>| Unknown "else" ||| Unknown "cond"
                -- ]                
  -- mSol <- (evalZ3State $ initSolver >> solveWithParams noAgressiveParams quals fmls)
  -- case mSol of
    -- Nothing -> putStr "No solution"
    -- Just sol -> print $ pretty $ pAbs sol    

-- pInc :: Integer -> Solution -> SimpleProgram
-- pInc n sol = let val ident = conjunction $ valuation sol ident
  -- in if n == 0
      -- then extractVar "y0" $ val "arg1"
      -- else PApp (extractConstIntInt ("y" ++ show (n - 1)) ("y" ++ show n) $ val ("fun" ++ show n)) (pInc (n - 1) sol)
        
-- testIncSynthesize1 n = do
  -- let vars = ["x"]
  -- let quals = Map.fromList $ 
                -- ("arg1", QSpace (varQual "y0" vars) 1) : 
                    -- map (\i -> ("fun" ++ show i, QSpace (constQualIntInt ("y" ++ show (i - 1)) ("y" ++ show i)) 1)) [1..n]
  -- let incType = Var ("y" ++ show n) |=| (Var "x" |+| IntLit n)
  -- let fmls = [foldr (|&|) (Unknown "arg1") (map (\i -> Unknown ("fun" ++ show i)) [1..n])  |=>| incType]                
  -- mSol <- (evalZ3State $ initSolver >> solveWithParams defaultParams quals fmls)
  -- case mSol of
    -- Nothing -> putStr "No solution"
    -- Just sol -> print $ pretty $ pInc n sol
    
-- testIncSynthesize2 n = do
  -- let vars = ["x"]
  -- let quals = Map.fromList $ 
                -- [("arg1", QSpace (varQual "y0" vars) 1)] ++
                    -- map (\i -> ("arg" ++ show i, QSpace (condQualsLinearEq n "x" ("y" ++ show (i - 1))) 1)) [2..n] ++
                    -- map (\i -> ("fun" ++ show i, QSpace (constQualIntInt ("y" ++ show (i - 1)) ("y" ++ show i)) 1)) [1..n]
  -- let incType = Var ("y" ++ show n) |=| (Var "x" |+| IntLit n)
  -- let fmls = map (\i -> (Unknown ("fun" ++ show i) |&| Unknown ("arg" ++ show i)) |=>| Unknown ("arg" ++ show (i + 1))) [1..(n - 1)] ++
                -- [(Unknown ("fun" ++ show n) |&| Unknown ("arg" ++ show n)) |=>| incType]  
  -- mSol <- (evalZ3State $ initSolver >> solveWithParams defaultParams quals fmls)
  -- case mSol of
    -- Nothing -> putStr "No solution"
    -- Just sol -> print $ pretty $ pInc n sol
    
-- testIncSynthesize3 n = do
  -- let vars = ["x"]
  -- let quals = Map.fromList $ 
                -- [("arg1", QSpace (varQual "y0" vars) 1)] ++
                    -- map (\i -> ("arg" ++ show i, QSpace [Var ("y" ++ show (i - 1)) |=| Var "x" |+| Parameter ("i" ++ show i)] 1)) [2..n] ++ -- , "y" ++ show (i - 1)
                    -- map (\i -> ("fun" ++ show i, QSpace (constQualIntInt ("y" ++ show (i - 1)) ("y" ++ show i)) 1)) [1..n]
  -- let incType = Var ("y" ++ show n) |=| (Var "x" |+| IntLit n)
  -- let fmls = map (\i -> (Unknown ("fun" ++ show i) |&| Unknown ("arg" ++ show i)) |=>| Unknown ("arg" ++ show (i + 1))) [1..(n - 1)] ++
                -- [(Unknown ("fun" ++ show n) |&| Unknown ("arg" ++ show n)) |=>| incType]  
  -- mSol <- (evalZ3State $ initSolver >> solveWithParams defaultParams { maxCegisIterations = -1, candidatePickStrategy = FirstCandidate } quals fmls)
  -- case mSol of
    -- Nothing -> putStr "No solution"
    -- Just sol -> print $ pretty $ pInc n sol    
            
-- main = testMax3Synthesize1New

-- Search parameters  

defaultParams = SolverParams {
    -- pruneQuals = True,
    pruneQuals = False,
    optimalValuationsStrategy = UnsatCoreValuations,
    -- optimalValuationsStrategy = BFSValuations,    
    -- semanticPrune = True,
    -- agressivePrune = True,
    semanticPrune = False,
    agressivePrune = False,    
    candidatePickStrategy = UniformStrongCandidate,
    constraintPickStrategy = SmallSpaceConstraint,
    maxCegisIterations = 20
  }
  
nat = int (valueVar |>=| IntLit 0)
intAll = int ftrue

main = do
  let env =             
            -- addSymbol (IntLit 0) (int (valueVar |=| IntLit 0)) .           
            addSymbol (Var "dec") (FunctionT "x" intAll (int (valueVar |=| Var "x" |-| IntLit 1))) .
            addSymbol (Var "id") (FunctionT "x" intAll (int (valueVar |=| Var "x"))) .
            addSymbol (Var "inc") (FunctionT "x" intAll (int (valueVar |=| Var "x" |+| IntLit 1))) .
            addSymbol (Var "neg") (FunctionT "x" intAll (int (valueVar |=| fneg (Var "x")))) .
            -- addSymbol (Var "plus") (FunctionT "x" intAll $ FunctionT "y" (int ftrue) $ int (valueVar |=| Var "x" |+| Var "y")) .
            -- addSymbol (Var "const0") (FunctionT "x" intAll (int (valueVar |=| IntLit 0))) .
            -- addSymbol (Var "y") nat .
            -- addSymbol (Var "f") (FunctionT "x" (int (IntLit 0 |<=| valueVar |&| valueVar |<| Var "y")) (int (valueVar |=| Var "x"))) .
            id $ emptyEnv

  -- -- Peano
  -- -- let typ = FunctionT "x" intAll $ int (valueVar |=| Var "x")
  -- let typ = int (valueVar |=| Var "y")
  -- -- let templ = fix_ (int_ |->| int_) (int_ |.| (sym (int_ |->| int_) |$| sym int_))
  -- -- let templ = int_ |.| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_))
  -- -- let templ = fix_ (int_ |->| int_) (int_ |.| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_))))
  -- let templ = choice 
                -- (sym (int_ |->| int_) |$| sym int_) 
                -- (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_)))
              
  -- -- max2:
  -- let typ = FunctionT "x" (int ftrue) $ FunctionT "y" (int ftrue) $ int (valueVar |>=| Var "x" |&| valueVar |>=| Var "y")
  -- let templ = int_ |.| int_ |.| choice (sym int_) (sym int_)

  -- abs:
  let typ = FunctionT "x" (int ftrue) $ int (valueVar |>=| Var "x" |&| valueVar |>=| IntLit 0)
  let templ = int_ |.| choice (sym (int_ |->| int_) |$| sym int_) (sym (int_ |->| int_) |$| sym int_)
  
  -- -- application
  -- let typ = FunctionT "y" nat $ int (valueVar |=| IntLit 0)
  -- let templ = int_ |.| sym (int_ |->| int_) |$| (sym (int_ |->| int_) |$| sym int_)
  -- let templ = int_ |.| sym (int_ |->| int_) |$| sym int_
  
  -- -- const
  -- let typ = FunctionT "y" nat $ int (valueVar |>| Var "y")
  -- let templ = sym (int_ |->| int_)
  
  let (p, qmap, fmls) = genConstraints (toSpace . cq) (toSpace . \syms -> tq syms ++ [valueVar |=| IntLit 0]) env typ templ
  
  -- putStr "Liquid Program\n"
  -- print $ pretty p
  -- putStr "\nConstraints\n"
  -- print $ vsep $ map pretty fmls
  -- putStr "\nQmap\n"
  -- print $ pretty qmap
  -- putStr "\n"
  
  mSol <- evalZ3State $ initSolver >> solveWithParams defaultParams qmap fmls (extract p)
  case mSol of
    Nothing -> putStr "No Solution"
    Just sol -> print $ pretty sol
  where
    cq syms = do
      lhs <- syms
      op <- [Ge, Le, Neq]
      rhs <- syms ++ [IntLit 0]
      guard $ lhs /= rhs
      return $ Binary op lhs rhs  
    -- tq syms = do
      -- lhs <- valueVar:syms
      -- op <- [Ge, Neq]
      -- rhs <- valueVar:syms
      -- guard $ (lhs == valueVar || rhs == valueVar) && lhs /= rhs
      -- return $ Binary op lhs rhs
    tq syms = do
      rhs <- syms
      [valueVar |=| rhs, valueVar |=| rhs |+| IntLit 1, valueVar |=| rhs |-| IntLit 1, valueVar |=| fneg rhs]
    toSpace quals = QSpace quals 2 -- (length quals)
