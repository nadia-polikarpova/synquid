module Synquid.ConstraintGenerator where

import Synquid.Logic
import Synquid.Program
import Synquid.Util
import Synquid.Pretty
import Synquid.SMTSolver
import Data.Either
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State
import Control.Applicative
import Control.Lens
import Control.Monad.Trans.Maybe
  
type Generator = State Int

freshId :: String -> Generator String
freshId prefix = ((prefix ++) . show) <$> state (\i -> (i, i + 1))
  
-- | 'freshRefinements' @t@ : a type with the same shape and value variables as @t@ but fresh unknowns as refinements
freshRefinements :: RType -> Generator RType
freshRefinements (ScalarT base _) = do
  k <- freshId "_u"  
  return $ ScalarT base (Unknown valueVarName k)
freshRefinements (FunctionT x tArg tFun) = do
  -- liftM2 (FunctionT x) (freshRefinements tArg) (freshRefinements tFun)
  liftM2 (FunctionT x) (return tArg) (freshRefinements tFun)
  
genConstraints :: QualsGen -> QualsGen -> Environment -> RType -> Template -> (LiquidProgram, QMap, [Formula])
genConstraints cq tq env typ templ = evalState go 0
  where
    go :: Generator (LiquidProgram, QMap, [Formula])
    go = do
      (p, cs) <- constraints env typ templ
      debug 1 (pretty cs) $ return ()
      let cs' = concatMap split cs
      debug 1 (pretty cs') $ return ()
      let (fmls, qspaces) = partitionEithers $ map (toFormula cq tq) cs'
      let qmap = Map.unions qspaces      
      return (p, qmap, fmls)
      
-- | 'extract' @prog sol@ : simple program encoded in @prog@ when all unknowns are instantiated according to @sol@
extract :: SMTSolver s => LiquidProgram -> Solution -> MaybeT s SimpleProgram
extract prog sol = case prog of
  PSymbol (env, t) -> let env' = envApplySolution sol env
    in msum $ map (extractSymbol env' (typeApplySolution sol t)) (Map.toList $ symbolsByShape (shape t) env') 
  PApp pFun pArg -> liftM2 PApp (extract pFun sol) (extract pArg sol)
  PFun x pBody -> liftM (PFun x) (extract pBody sol)
  PIf cond pThen pElse -> liftM2 (PIf $ applySolution sol cond) (extract pThen sol) (extract pElse sol)      
  PFix f pBody -> liftM (PFix f) (extract pBody sol)
  where
    extractSymbol :: SMTSolver s => Environment -> RType -> (Formula, RType) -> MaybeT s SimpleProgram
    extractSymbol env t (symb, symbT) = do
      let constraint = Subtype env (symbolType symb symbT) t
      debug 1 (pretty constraint) $ return ()
      let fmls = lefts $ map (toFormula trivialGen trivialGen) $ split constraint
      debug 1 (vsep $ map pretty fmls) $ return ()
      res <- lift $ isValid (conjunction $ Set.fromList fmls)
      if res
        then debug 1 (text "VALID") $ return (PSymbol symb)
        else debug 1 (text "INVALID") $ mzero    
    symbolType (Var x) (ScalarT b _) = ScalarT b (varRefinement x)
    symbolType _ t = t      
  
constraints :: Environment -> RType -> Template -> Generator (LiquidProgram, [Constraint])
constraints env t (PSymbol _) = do
  t' <- freshRefinements t
  -- let env' = restrict t' env
  return (PSymbol (env, t'), [WellFormed env t', Subtype env t' t])
constraints env t (PApp funTempl argTempl) = do
  x <- freshId "_x"
  tArg <- freshRefinements $ refine $ sTypeOf argTempl
  let tFun = FunctionT x tArg t
  (fun, csFun) <- constraints env tFun funTempl
  (arg, csArg) <- constraints env tArg argTempl     
  return (PApp fun arg, csArg ++ csFun ++ [WellFormed env tArg])
constraints env t (PFun _ bodyTempl) = do
  let (FunctionT x tArg tRes) = t
  let env' = addSymbol (Var x) tArg env
  (pBody, cs) <- constraints env' tRes bodyTempl
  return (PFun x pBody, cs)
constraints env t (PIf _ thenTempl elseTempl) = do
  cond <- Unknown valueVarName <$> freshId "_u"
  (pThen, csThen) <- constraints (addAssumption cond env) t thenTempl
  (pElse, csElse) <- constraints (addNegAssumption cond env) t elseTempl
  return (PIf cond pThen pElse, csThen ++ csElse ++ [WellFormedCond env cond])
constraints env t (PFix _ bodyTemp) = do
  f <- freshId "_f"
  t' <- freshRefinements t
  let env' = addSymbol (Var f) t' env
  (pBody, cs) <- constraints env' t' bodyTemp
  return (PFix f pBody, cs ++ [WellFormed env t', Subtype env t' t])
    
split :: Constraint -> [Constraint]
split (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2)) =
  split (Subtype env tArg2 tArg1) ++ split (Subtype (addSymbol (Var y) tArg2 env) (renameVar x y tRes1) tRes2)
split (WellFormed env (FunctionT x tArg tRes)) = 
  split (WellFormed env tArg) ++ split (WellFormed (addSymbol (Var x) tArg env) tRes)
split c = [c]

type QualsGen = [Formula] -> QSpace

trivialGen = const emptyQSpace

toFormula :: QualsGen -> QualsGen -> Constraint -> Either Formula QMap
toFormula _ _ (Subtype env (ScalarT IntT fml) (ScalarT IntT fml')) =
  let (poss, negs) = embedding env 
  in Left $ conjunction (Set.insert fml poss) |=>| disjunction (Set.insert fml' negs)
toFormula _ tq (WellFormed env (ScalarT IntT (Unknown _ u))) = 
  Right $ Map.singleton u $ tq (Map.keys $ symbolsByShape (ScalarT IntT ()) env)
toFormula cq _ (WellFormedCond env (Unknown _ u)) = 
  Right $ Map.singleton u $ cq (Map.keys $ symbolsByShape (ScalarT IntT ()) env)
toFormula _ _ c = Right $ Map.empty -- error $ show $ text "Not a simple constraint:" $+$ pretty c
