module Synquid.ConstraintGenerator where

import Synquid.Logic
import Synquid.Program
import Synquid.Util
import Synquid.Pretty

import Data.Either
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State
import Control.Applicative
import Control.Lens
  
type Generator = State Int

freshId :: String -> Generator String
freshId prefix = ((prefix ++) . show) <$> state (\i -> (i, i + 1))
  
unknownPrefix = "_u"  
varPrefix = "_x"

-- | 'freshValueVars' @s@ : refinement type with shape @s@, fresh value variables, and trivial refinements
freshValueVars :: SType -> Generator RType
freshValueVars (ScalarT base _) = do
  v <- freshId varPrefix
  return $ ScalarT base (v, ftrue)
freshValueVars (FunctionT t1 t2) = liftM2 FunctionT (freshValueVars t1) (freshValueVars t2)

-- | 'freshRefinements' @t@ : a type with the same shape and value variables as @t@ but fresh unknowns as refinements
freshRefinements :: RType -> Generator RType
freshRefinements (ScalarT base (v, _)) = do
  k <- freshId unknownPrefix
  return $ ScalarT base (v, Unknown k)
freshRefinements (FunctionT tArg tFun) = do
  liftM2 FunctionT (freshRefinements tArg) (freshRefinements tFun)
  
genConstraints :: CondQuals -> TypeQuals -> Environment -> RType -> Template -> (LiquidProgram, QMap, [Formula])
genConstraints cq tq env typ templ = evalState go 0
  where
    go :: Generator (LiquidProgram, QMap, [Formula])
    go = do
      (p, cs) <- constraints env typ templ
      let cs' = concatMap split cs
      let (fmls, qspaces) = partitionEithers $ map (toFormula cq tq) cs'
      let qmap = Map.unions qspaces      
      return (p, qmap, fmls)
  
constraints :: Environment -> RType -> Template -> Generator (LiquidProgram, [Constraint])
constraints env t (PSymbol _) = do
  t' <- freshRefinements t
  let env' = restrict t' env
  return (PSymbol (env', t'), [WellFormedSymbol env' t', Subtype env t' t])
constraints env t (PApp funTempl argTempl) = do
  tArg <- freshValueVars >=> freshRefinements $ sTypeOf argTempl
  let tFun = FunctionT tArg t
  (fun, csFun) <- constraints env tFun funTempl
  (arg, csArg) <- constraints env tArg argTempl     
  return (PApp fun arg, csArg ++ csFun ++ [WellFormed env tArg])
constraints env t (PIf _ thenTempl elseTempl) = do
  cond <- Unknown <$> freshId unknownPrefix
  (pThen, csThen) <- constraints (addAssumption cond env) t thenTempl
  (pElse, csElse) <- constraints (addNegAssumption cond env) t elseTempl
  return (PIf cond pThen pElse, csThen ++ csElse ++ [WellFormedCond env cond])
    
split :: Constraint -> [Constraint]
split (Subtype env (FunctionT tArg1 tFun1) (FunctionT tArg2 tFun2)) =
  split (Subtype env tArg2 tArg1) ++ split (Subtype (addSymbol (valueVar tArg2) tArg2 env) tFun1 tFun2)
split (WellFormed env (FunctionT tArg tFun)) = 
  split (WellFormed env tArg) ++ split (WellFormed (addSymbol (valueVar tArg) tArg env) tFun)
split c = [c]

type CondQuals = [Formula] -> QSpace
type TypeQuals = Id -> [Formula] -> QSpace

toFormula :: CondQuals -> TypeQuals -> Constraint -> Either Formula (Map Id QSpace)
toFormula _ _ (Subtype env (ScalarT IntT (v1, fml1)) (ScalarT IntT (v2, fml2))) =
  let (poss, negs) = embedding env 
  in Left $ conjunction (Set.insert fml1 poss) |=>| disjunction (Set.insert fml2 negs)
toFormula _ tq (WellFormed env (ScalarT IntT (v, Unknown u))) = 
  Right $ Map.singleton u $ tq v (Map.keys $ symbolsByShape (ScalarT IntT ()) env)
toFormula cq _ (WellFormedCond env (Unknown u)) = 
  Right $ Map.singleton u $ cq (Map.keys $ symbolsByShape (ScalarT IntT ()) env)
toFormula _ _ (WellFormedSymbol env t) =
  Right $ Map.map (flip QSpace 1 . nub) $ Map.foldlWithKey (\m s t' -> Map.unionWith (++) m $ matchUnknowns t t' s) Map.empty (env ^. symbols)
  where
    matchUnknowns (ScalarT _ (_, Unknown u)) (ScalarT base (v, _)) (Var x) = Map.singleton u [varRefinement v x]
    matchUnknowns t t' _ = matchUnknowns' t t'
    matchUnknowns' (ScalarT _ (_, Unknown u)) (ScalarT base (_, fml)) = Map.singleton u [fml]
    matchUnknowns' (FunctionT t1 t2) (FunctionT t1' t2') = matchUnknowns' t1 t1' `Map.union` matchUnknowns' t2 t2'
toFormula _ _ c = error $ show $ text "Not a simple constraint:" $+$ pretty c

