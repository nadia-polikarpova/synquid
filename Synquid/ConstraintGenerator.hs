module Synquid.ConstraintGenerator where

import Synquid.Logic
import Synquid.Program
import Synquid.Util
import Synquid.Pretty

import Data.Either
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

toType :: TypeSkeleton -> Generator Type
toType (ScalarS base) = do
  v <- freshId varPrefix
  return $ ScalarT base v ftrue
toType (FunctionS t1 t2) = liftM2 FunctionT (toType t1) (toType t2)

freshRefinements :: Type -> Generator Type
freshRefinements (ScalarT base v _) = do
  k <- freshId unknownPrefix
  return $ ScalarT base v (Unknown k)
freshRefinements (FunctionT tArg tFun) = do
  liftM2 FunctionT (freshRefinements tArg) (freshRefinements tFun)
  
genConstraints :: CondQuals -> TypeQuals -> Environment -> Type -> Template -> (LiquidProgram, QMap, [Formula])
genConstraints = genConstraintsTopDown
-- genConstraints = genConstraintsBottomUp

genConstraintsTopDown cq tq env typ templ = evalState go 0
  where
    go :: Generator (LiquidProgram, QMap, [Formula])
    go = do
      (p, cs) <- constraintsTopDown env typ templ
      let cs' = concatMap split cs
      let (fmls, qspaces) = partitionEithers $ map (toFormula cq tq) cs'
      let qmap = Map.fromList qspaces      
      return (p, qmap, fmls)

genConstraintsBottomUp cq tq env typ templ = evalState go 0
  where
    go :: Generator (LiquidProgram, QMap, [Formula])
    go = do
      (p, t, cs) <- constraintsBottomUp env typ templ
      let cs' = concatMap split $ cs ++ [Subtype env t typ]
      let (fmls, qspaces) = partitionEithers $ map (toFormula cq tq) cs'
      let qmap = Map.fromList qspaces      
      return (p, qmap, fmls)
      
constraintsBottomUp :: Environment -> Type -> Template -> Generator (LiquidProgram, Type, [Constraint])
constraintsBottomUp env s (PSymbol _) = do
  t <- freshRefinements s
  return (PSymbol (restrict t env, t), t, [WellFormedSymbol env t])
constraintsBottomUp env s (PApp funTempl argTempl) = do
  sArg <- toType $ typeSkeletonOf argTempl
  let sFun = FunctionT sArg s
  (fun, tFun, csFun) <- constraintsBottomUp env sFun funTempl
  let (FunctionT tArg tRes) = tFun 
  (arg, tArg', csArg) <- constraintsBottomUp env sArg argTempl     
  return (PApp fun arg, typeConjunction tRes tArg', csArg ++ csFun ++ [Subtype env tArg' tArg])
constraintsBottomUp env s (PIf _ thenTempl elseTempl) = do
  cond <- Unknown <$> freshId unknownPrefix
  t <- freshRefinements s
  (pThen, tThen, csThen) <- constraintsBottomUp (addAssumption cond env) s thenTempl
  (pElse, tElse, csElse) <- constraintsBottomUp (addNegAssumption cond env) s elseTempl
  return (PIf cond pThen pElse, t, csThen ++ csElse ++ [WellFormedCond env cond, WellFormed env t, Subtype (addAssumption cond env) tThen t, Subtype (addNegAssumption cond env) tElse t])
  
constraintsTopDown :: Environment -> Type -> Template -> Generator (LiquidProgram, [Constraint])
constraintsTopDown env t (PSymbol _) = do
  t' <- freshRefinements t
  return (PSymbol (restrict t' env, t'), [WellFormedSymbol env t', Subtype env t' t])
constraintsTopDown env t (PApp funTempl argTempl) = do
  tArg <- toType >=> freshRefinements $ typeSkeletonOf argTempl
  let tFun = FunctionT tArg t
  (fun, csFun) <- constraintsTopDown env tFun funTempl
  (arg, csArg) <- constraintsTopDown env tArg argTempl     
  return (PApp fun arg, csArg ++ csFun ++ [WellFormed env tArg])
constraintsTopDown env t (PIf _ thenTempl elseTempl) = do
  cond <- Unknown <$> freshId unknownPrefix
  (pThen, csThen) <- constraintsTopDown (addAssumption cond env) t thenTempl
  (pElse, csElse) <- constraintsTopDown (addNegAssumption cond env) t elseTempl
  return (PIf cond pThen pElse, csThen ++ csElse ++ [WellFormedCond env cond])
  
  
split :: Constraint -> [Constraint]
split (Subtype env (FunctionT tArg1 tFun1) (FunctionT tArg2 tFun2)) =
  let x = head $ boundVars tArg2 in 
  split (Subtype env tArg2 tArg1) ++ split (Subtype (addSymbol x tArg2 env) tFun1 tFun2)
split (WellFormed env (FunctionT tArg tFun)) = 
  let x = head $ boundVars tArg in 
  split (WellFormed env tArg) ++ split (WellFormed (addSymbol x tArg env) tFun)
-- ToDo: splitting WellFormedSymbol
split c = [c]

type CondQuals = [Id] -> QSpace
type TypeQuals = Id -> [Id] -> QSpace

toFormula :: CondQuals -> TypeQuals -> Constraint -> Either Formula (Id, QSpace)
toFormula _ _ (Subtype env (ScalarT IntT v1 fml1) (ScalarT IntT v2 fml2))
  | v1 == v2 = Left $ conjunction (fml1 `Set.insert` view assumptions env) |=>| disjunction (fml2 `Set.insert` view negAssumptions env)
toFormula _ tq (WellFormed env (ScalarT IntT v (Unknown u))) = 
  Right (u, tq v $ symbolsByShape (ScalarS IntT) env)
toFormula cq _ (WellFormedCond env (Unknown u)) = 
  Right (u, cq $ symbolsByShape (ScalarS IntT) env)  
toFormula _ _ (WellFormedSymbol env (ScalarT IntT v (Unknown u))) = 
  let symq names = QSpace (varQual v names) 1 -- ToDo: distinguish variables and constants
  in Right (u, symq $ symbolsByShape (ScalarS IntT) env)
toFormula _ _ c = error $ show $ text "Not a simple constraint:" $+$ pretty c

varQual res vars = do
  var <- map Var vars
  return $ Var res |=| var  