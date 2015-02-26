module Synquid.ConstraintGenerator where

import Synquid.Logic
import Synquid.Program
import Synquid.Pretty

import Data.Either
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State
import Control.Applicative
import Control.Lens
  
type Generator = StateT Int []

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
  
genConstraints :: CondQuals -> TypeQuals -> Environment -> Type -> Template -> [(SimpleProgram, QMap, [Formula])]
genConstraints cq tq env typ templ = evalStateT go 0
  where
    go :: Generator (SimpleProgram, QMap, [Formula])
    go = do
      s <- toType $ shape typ
      (p, t, cs) <- constraints env typ templ
      let cs' = concatMap split $ cs ++ [Subtype env t typ]
      let (fmls, qspaces) = partitionEithers $ map (toFormula cq tq) cs'
      let qmap = Map.fromList qspaces      
      return (p, qmap, fmls)

constraints :: Environment -> Type -> Template -> Generator (SimpleProgram, Type, [Constraint])
constraints env s (PSymbol _) = do
  name <- lift $ symbolsByShape (shape s) env
  let t = unifyVars (symbolByName name env) s
  return (PSymbol name, t, [])
constraints env s (PApp funTempl argTempl) = do
  sArg <- toType $ typeSkeletonOf argTempl
  let sFun = FunctionT sArg s
  (fun, tFun, csFun) <- constraints env sFun funTempl
  let (FunctionT tArg tRes) = tFun 
  (arg, tArg', csArg) <- constraints env sArg argTempl     
  return (PApp fun arg, typeConjunction tRes tArg', csArg ++ csFun ++ [Subtype env tArg' tArg])
constraints env s (PIf _ thenTempl elseTempl) = do
  cond <- Unknown <$> freshId unknownPrefix
  t <- freshRefinements s
  (pThen, tThen, csThen) <- constraints (addAssumption cond env) s thenTempl
  (pElse, tElse, csElse) <- constraints (addNegAssumption cond env) s elseTempl
  return (PIf cond pThen pElse, t, csThen ++ csElse ++ [WellFormedCond env cond, WellFormed env t, Subtype (addAssumption cond env) tThen t, Subtype (addNegAssumption cond env) tElse t])
  
split :: Constraint -> [Constraint]
split (Subtype env (FunctionT tArg1 tFun1) (FunctionT tArg2 tFun2)) =
  let x = head $ boundVars tArg2 in 
  split (Subtype env tArg2 tArg1) ++ split (Subtype (addSymbol x tArg2 env) tFun1 tFun2)
split (WellFormed env (FunctionT tArg tFun)) = 
  let x = head $ boundVars tArg in 
  split (WellFormed env tArg) ++ split (WellFormed (addSymbol x tArg env) tFun)
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
toFormula _ _ c = error $ show $ text "Not a simple constraint:" $+$ pretty c
  