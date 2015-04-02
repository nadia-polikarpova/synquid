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

-- | 'freshRefinements' @t@ : a type with the same shape and value variables as @t@ but fresh unknowns as refinements
freshRefinements :: RType -> Generator RType
freshRefinements (ScalarT base _) = do
  k <- freshId unknownPrefix
  return $ ScalarT base (Unknown valueVarName k)
freshRefinements (FunctionT x tArg tFun) = do
  liftM2 (FunctionT x) (freshRefinements tArg) (freshRefinements tFun)
  
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
  
constraints :: Environment -> RType -> Template -> Generator (LiquidProgram, [Constraint])
constraints env t (PSymbol _) = do
  t' <- freshRefinements t
  let env' = restrict t' env
  return (PSymbol (env', t'), [WellFormedSymbol env' t', Subtype env t' t])
constraints env t (PApp funTempl argTempl) = do
  x <- freshId varPrefix
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
  cond <- Unknown valueVarName <$> freshId unknownPrefix
  (pThen, csThen) <- constraints (addAssumption cond env) t thenTempl
  (pElse, csElse) <- constraints (addNegAssumption cond env) t elseTempl
  return (PIf cond pThen pElse, csThen ++ csElse ++ [WellFormedCond env cond])
constraints env t (PFix _ bodyTemp) = do
  f <- freshId varPrefix
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

toFormula :: QualsGen -> QualsGen -> Constraint -> Either Formula QMap
toFormula _ _ (Subtype env (ScalarT IntT fml) (ScalarT IntT fml')) =
  let (poss, negs) = embedding env 
  in Left $ conjunction (Set.insert fml poss) |=>| disjunction (Set.insert fml' negs)
toFormula _ tq (WellFormed env (ScalarT IntT (Unknown _ u))) = 
  Right $ Map.singleton u $ tq (Map.keys $ symbolsByShape (ScalarT IntT ()) env)
toFormula cq _ (WellFormedCond env (Unknown _ u)) = 
  Right $ Map.singleton u $ cq (Map.keys $ symbolsByShape (ScalarT IntT ()) env)
toFormula _ _ (WellFormedSymbol env t) =
  -- Right $ Map.map (flip QSpace 1 . nub) $ Map.foldlWithKey (\m s t' -> Map.unionWith (++) m $ matchUnknowns t t' s) emptyQuals (env ^. symbols)
  Right $ Map.map (flip QSpace 100 . nub) $ Map.foldlWithKey (\m s t' -> Map.unionWith (++) m $ matchUnknowns t t' s) emptyQuals (env ^. symbols)
  where
    emptyQuals = constMap (Set.map unknownName $ unknownsOfType t) []
    matchUnknowns (ScalarT _ (Unknown _ u)) (ScalarT base _) (Var x) = Map.singleton u [varRefinement x]
    matchUnknowns t t' _ = matchUnknowns' t t'
    matchUnknowns' (ScalarT _ (Unknown _ u)) (ScalarT base (fml)) = Map.singleton u [fml]
    matchUnknowns' (FunctionT x t1 t2) (FunctionT _ t1' t2') = matchUnknowns' t1 t1' `Map.union` matchUnknowns' t2 t2'
    matchUnknowns' t t' = error $ show $ text "matchUnknowns': cannot match" <+> pretty t <+> text "and" <+> pretty t'
toFormula _ _ c = error $ show $ text "Not a simple constraint:" $+$ pretty c

-- | 'extract' @prog sol@ : simple program encoded in @prog@ when all unknowns are instantiated according to @sol@
extract :: LiquidProgram -> Solution -> SimpleProgram
extract prog sol = case prog of
  PSymbol (env, t) -> PSymbol $ symbolFromType env t
  PApp pFun pArg -> PApp (extract pFun sol) (extract pArg sol)
  PFun x pBody -> PFun x (extract pBody sol)
  PIf cond pThen pElse -> PIf (applySolution sol cond) (extract pThen sol) (extract pElse sol)      
  PFix f pBody -> PFix f (extract pBody sol)
  where
    symbolFromType env t = symbolByType (typeApplySolution sol t) (envApplySolution sol env)
    envApplySolution sol = over symbols (Map.map (typeApplySolution sol))
    
-- | 'symbolByType' @t env@ : symbol of type @t@ in @env@
symbolByType :: RType -> Environment -> Formula
symbolByType t env = case t of
  (ScalarT _ fml) -> case varFromRefinement fml of
    Just sym -> sym
    Nothing -> envLookup
  _ -> envLookup
  where
    envLookup = case Map.toList $ Map.filter (== t) $ symbolsByShape (shape t) env of
                  (sym, _):_ -> sym
                  _ -> error $ show (text "symbolByType: can't find type" <+> pretty t <+> text "in" $+$ pretty env)   
