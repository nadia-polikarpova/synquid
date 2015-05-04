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
  return $ ScalarT base (Unknown Map.empty k)
freshRefinements (FunctionT x tArg tFun) = do
  liftM3 FunctionT (freshId "_x") (freshRefinements tArg) (freshRefinements tFun)
  
genConstraints :: QualsGen -> QualsGen -> Environment -> RType -> Template -> (LiquidProgram, QMap, [Clause])
genConstraints cq tq env typ templ = evalState go 0
  where
    go :: Generator (LiquidProgram, QMap, [Clause])
    go = do
      (p, cs) <- constraints env typ templ
      -- debug 1 (text "Typing Constraints" $+$ (vsep $ map pretty cs)) $ return ()
      let cs' = concatMap split cs
      -- debug 1 (vsep $ map pretty cs') $ return ()
      let (clauses, qspaces) = partitionEithers $ map (toFormula cq tq) cs'
      let qmap = Map.unions qspaces      
      debug 1 (text "Typing Constraints" $+$ (vsep $ map pretty cs)) $ return (p, qmap, clauses)

constraints :: Environment -> RType -> Template -> Generator (LiquidProgram, [Constraint])
constraints env t (PSymbol _) = do
  t' <- freshRefinements t
  let symbols = symbolsByShape (shape t') env
  let leafFml = Map.mapWithKey (fmlForSymbol t') symbols
  let disjuncts = map (:[]) $ Map.elems $ Map.mapWithKey (constraintForSymbol t') symbols
  case t of
    ScalarT _ _ -> return (PSymbol leafFml, [WellFormedScalar env t', Subtype env t' t])
    FunctionT _ _ _ -> return (PSymbol leafFml, [WellFormedSymbol disjuncts, WellFormed (clearSymbols $ clearAssumptions env) t', Subtype env t' t])
  where    
    constraintForSymbol t symb symbT = Subtype (clearSymbols $ clearAssumptions env) (symbolType symb symbT) t
    fmlForSymbol t symb symbT = let         
        fmls = map fromHorn $ lefts $ map (toFormula trivialGen trivialGen) $ split (constraintForSymbol t symb symbT)
      in conjunction $ Set.fromList fmls
    symbolType (Var x) (ScalarT b _) = ScalarT b (varRefinement x)
    symbolType _ t = t      
constraints env t (PApp funTempl argTempl) = do
  x <- freshId "_x"
  tArg <- freshRefinements $ refine $ sTypeOf argTempl
  let tFun = FunctionT x tArg t
  (fun, csFun) <- constraints env tFun funTempl
  (arg, csArg) <- constraints env tArg argTempl     
  return (PApp fun arg, csArg ++ csFun ++ [WellFormed (clearRanks env) tArg])
constraints env t (PFun _ bodyTempl) = do
  let (FunctionT x tArg tRes) = t
  let env' = addSymbol (Var x) tArg env
  (pBody, cs) <- constraints env' tRes bodyTempl
  return (PFun x pBody, cs)
constraints env t (PIf _ thenTempl elseTempl) = do
  cond <- Unknown Map.empty <$> freshId "_u"
  (pThen, csThen) <- constraints (addAssumption cond env) t thenTempl
  (pElse, csElse) <- constraints (addNegAssumption cond env) t elseTempl
  return (PIf cond pThen pElse, csThen ++ csElse ++ [WellFormedCond env cond])
constraints env t (PFix _ bodyTemp) = do
  f <- freshId "_f"  
  -- t' <- freshRefinements t
  -- let env' = addSymbol (Var f) t' env
  -- (pBody, cs) <- constraints env' t' bodyTemp
  -- return (PFix f pBody, cs ++ [WellFormed env t', Subtype env t' t])    
  
  t'@(FunctionT x tArg tRes) <- freshRefinements t
  m <- freshId "_m"
  y <- freshId "_x"  
  let (ScalarT IntT fml) = tArg
  let tArg' = ScalarT IntT (fml |&| (valueVar |>=| IntLit 0) |&| (valueVar |<| Var m))
  let tArg'' = ScalarT IntT (fml |&| (valueVar |=| Var m))
  let env' = addSymbol (Var f) (FunctionT y tArg' (renameVar x y tRes)) . addRank (Var m) $ env
  (pBody, cs) <- constraints env' (FunctionT x tArg'' tRes) bodyTemp
  return (PFix f pBody, cs ++ [WellFormed (clearRanks env) t', Subtype env t' t])    
    
split :: Constraint -> [Constraint]
split (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2)) =
  split (Subtype env tArg2 tArg1) ++ split (Subtype (addSymbol (Var y) tArg2 env) (renameVar x y tRes1) tRes2)
split (WellFormed env (FunctionT x tArg tRes)) = 
  split (WellFormed env tArg) ++ split (WellFormed (addSymbol (Var x) tArg (set ranks [] env)) tRes)
split (WellFormedSymbol disjuncts) = 
  [WellFormedSymbol $ map (concatMap split) disjuncts]
split c = [c]

type QualsGen = [Formula] -> QSpace

trivialGen = const emptyQSpace

toFormula :: QualsGen -> QualsGen -> Constraint -> Either Clause QMap
toFormula _ _ (Subtype env (ScalarT IntT fml) (ScalarT IntT fml')) =
  let (poss, negs) = embedding env 
  in Left $ Horn $ conjunction (Set.insert fml poss) |=>| disjunction (Set.insert fml' negs)
toFormula _ tq (WellFormed env (ScalarT IntT (Unknown _ u))) = 
  Right $ Map.singleton u $ tq ((Map.keys $ symbolsByShape (ScalarT IntT ()) env) ++ env^.ranks)
toFormula cq _ (WellFormedCond env (Unknown _ u)) = 
  Right $ Map.singleton u $ cq (Map.keys $ symbolsByShape (ScalarT IntT ()) env)
toFormula _ _ (WellFormedScalar env (ScalarT IntT (Unknown _ u))) = 
  let quals = map (valueVar |=|) (Map.keys $ symbolsByShape (ScalarT IntT ()) env)
  in Right $ Map.singleton u $ QSpace quals (length quals)
toFormula _ _ (WellFormedSymbol disjuncts) =
  Left $ Disjunctive $ map (map fromHorn . lefts . map (toFormula trivialGen trivialGen)) disjuncts 
toFormula _ _ c = error $ show $ text "Not a simple constraint:" $+$ pretty c

-- | 'extract' @prog sol@ : simple program encoded in @prog@ when all unknowns are instantiated according to @sol@
extract :: SMTSolver s => LiquidProgram -> Solution -> MaybeT s SimpleProgram
extract prog sol = case prog of
  PSymbol leafConstraint -> msum $ map extractSymbol (Map.toList $ leafConstraint)     
  PApp pFun pArg -> liftM2 PApp (extract pFun sol) (extract pArg sol)
  PFun x pBody -> liftM (PFun x) (extract pBody sol)
  PIf cond pThen pElse -> liftM2 (PIf $ applySolution sol cond) (extract pThen sol) (extract pElse sol)      
  PFix f pBody -> liftM (PFix f) (extract pBody sol)
  where
    extractSymbol :: SMTSolver s => (Formula, Formula) -> MaybeT s SimpleProgram
    extractSymbol (symb, fml) = do   
      let fml' = applySolution sol fml
      res <- debug 1 (text "Check symbol" <+> pretty symb <+> parens (pretty fml) <+> pretty fml') $ lift $ isValid fml'
      if res then debug 1 (text "OK") $ return (PSymbol symb) else debug 1 (text "MEH") $ mzero    
