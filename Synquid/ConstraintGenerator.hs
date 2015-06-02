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
import Control.Monad.Reader
import Control.Applicative
import Control.Lens
import Control.Monad.Trans.Maybe

{- Interface -}

-- | State space generator (returns a state space for a list of symbols in scope)
type QualsGen = [Formula] -> QSpace

-- | Empty state space generator
trivialGen = const emptyQSpace

-- | Parameters of constraint generation
data ConsGenParams = ConsGenParams {
  bottomUp :: Bool,                                       -- ^ Should types be propagated bottom-up as opposed to top-down?
  abstractLeaves :: Bool,
  abstractFix :: Bool  
}

-- | 'genConstraints' @params cq tq env typ templ@ : given parameters @params@, search space generators for conditionals and types @cq@ and @tq@,
-- top-level type environment @env@, refinement type @typ@, and template @templ@,
-- generate a set of constraints, a search space map for the unknowns inside those constraints, and a liquid program,
-- such that a valid solution for the constraints would turn the liquid program into a simple program of type @typ@.
genConstraints :: ConsGenParams -> QualsGen -> QualsGen -> Environment -> RType -> Template -> ([Clause], QMap, LiquidProgram)
genConstraints params cq tq env typ templ = if bottomUp params
                                              then runReader (evalStateT goBottomUp (0, [])) params
                                              else runReader (evalStateT goTopDown (0, [])) params
  where
    goTopDown :: Generator ([Clause], QMap, LiquidProgram)
    goTopDown = do
      p <- constraintsTopDown env typ templ
      cs <- gets snd
      let cs' = concatMap split cs
      let (clauses, qmap) = toFormulas cq tq cs'
      debug 1 (text "Typing Constraints" $+$ (vsep $ map pretty cs)) $ return (clauses, qmap, p)
      
    goBottomUp :: Generator ([Clause], QMap, LiquidProgram)
    goBottomUp = do
      (p, t) <- constraintsBottomUp env templ
      addConstraint $ Subtype env t typ
      cs <- gets snd
      let cs' = concatMap split cs
      let (clauses, qmap) = toFormulas cq tq cs'
      debug 1 (text "Typing Constraints" $+$ (vsep $ map pretty cs)) $ return (clauses, qmap, p)

{- Implementation -}
  
type Generator = StateT (Int, [Constraint]) (Reader ConsGenParams)

freshId :: String -> Generator String
freshId prefix = ((prefix ++) . show) <$> state (\(i, cs) -> (i, (i + 1, cs)))
  
-- | 'freshRefinements' @t@ : a type with the same shape and value variables as @t@ but fresh unknowns as refinements
freshRefinements :: RType -> Generator RType
freshRefinements (ScalarT base _) = do
  k <- freshId "_u"  
  return $ ScalarT base (Unknown Map.empty k)
freshRefinements (FunctionT x tArg tFun) = do
  liftM3 FunctionT (freshId "_x") (freshRefinements tArg) (freshRefinements tFun)
  
addConstraint c = modify (\(i, cs) -> (i, c:cs))  
  
-- | 'constraintsTopDown' @env t templ@ : a liquid program and typing constraints 
-- for a program of type @t@ following @templ@ in the typing environment @env@
constraintsTopDown :: Environment -> RType -> Template -> Generator LiquidProgram
constraintsTopDown env t (PSymbol s) = do
  abstract <- asks abstractLeaves
  t' <- if abstract then freshRefinements t else return t
  let symbols = symbolsByShape s env
  let leafFml = Map.mapWithKey (fmlForSymbol abstract t') symbols
  let disjuncts = map (:[]) $ Map.elems $ Map.mapWithKey (constraintForSymbol abstract t') symbols  
  if abstract  
    then do
      addConstraint $ WellFormedLeaf t' (Map.elems $ Map.mapWithKey symbolType symbols)
      when (isFunctionType s) $ addConstraint $ WellFormedSymbol disjuncts
      addConstraint $ Subtype env t' t
    else addConstraint $ WellFormedSymbol disjuncts  
  return $ PSymbol leafFml
  where    
    constraintForSymbol abstract t symb symbT = if abstract
                                                  then Subtype emptyEnv (symbolType symb symbT) t
                                                  else Subtype env (symbolType symb symbT) t
    fmlForSymbol abstract t symb symbT = let         
        fmls = map fromHorn $ fst $ toFormulas trivialGen trivialGen $ split (constraintForSymbol abstract t symb symbT)
      in conjunction $ Set.fromList fmls
    symbolType (Var x) (ScalarT b _) = ScalarT b (varRefinement x)
    symbolType _ t = t      
constraintsTopDown env t (PApp funTempl argTempl) = do
  x <- freshId "_x"
  tArg <- freshRefinements $ refine $ sTypeOf argTempl
  let tFun = FunctionT x tArg t
  fun <- constraintsTopDown env tFun funTempl
  arg <- constraintsTopDown env tArg argTempl     
  addConstraint $ WellFormed (clearRanks env) tArg
  return $ PApp fun arg
constraintsTopDown env t (PFun _ bodyTempl) = do
  let (FunctionT x tArg tRes) = t
  let env' = addSymbol (Var x) tArg env
  pBody <- constraintsTopDown env' tRes bodyTempl
  return $ PFun x pBody
constraintsTopDown env t (PIf _ thenTempl elseTempl) = do
  cond <- Unknown Map.empty <$> freshId "_u"
  pThen <- constraintsTopDown (addAssumption cond env) t thenTempl
  pElse <- constraintsTopDown (addNegAssumption cond env) t elseTempl
  addConstraint $ WellFormedCond env cond
  return $ PIf cond pThen pElse
constraintsTopDown env t (PFix _ bodyTemp) = do
  abstract <- asks abstractFix
  t' <- if abstract then freshRefinements t else return t
  f <- freshId "_f"
  let (FunctionT x tArg tRes) = t'
  m <- freshId "_m"
  y <- freshId "_x"  
  let (ScalarT IntT fml) = tArg
  let tArg' = ScalarT IntT (fml |&| (valueVar |>=| IntLit 0) |&| (valueVar |<| Var m))
  let tArg'' = ScalarT IntT (fml |&| (valueVar |=| Var m))
  let env' = addSymbol (Var f) (FunctionT y tArg' (renameVar x y tRes)) . addRank (Var m) $ env
  pBody <- constraintsTopDown env' (FunctionT x tArg'' tRes) bodyTemp
  when abstract $ (addConstraint $ WellFormed (clearRanks env) t') >> (addConstraint $ Subtype env t' t)
  return $ PFix f pBody
  
-- | 'constraintsBottomUp' @env templ@ : a liquid program, its type, and typing constraints 
-- for a program following @templ@ in the typing environment @env@  
constraintsBottomUp :: Environment -> Template -> Generator (LiquidProgram, RType)
constraintsBottomUp env (PSymbol s) = do
  t <- freshRefinements $ refine s
  let symbols = symbolsByShape s env
  let leafFml = Map.mapWithKey (fmlForSymbol t) symbols
  let disjuncts = map (:[]) $ Map.elems $ Map.mapWithKey (constraintForSymbol t) symbols
  
  addConstraint $ WellFormedLeaf t (Map.elems $ Map.mapWithKey symbolType symbols)
  when (isFunctionType s) $ addConstraint $ WellFormedSymbol disjuncts
  return (PSymbol leafFml, t)
  where    
    constraintForSymbol t symb symbT = Subtype emptyEnv (symbolType symb symbT) t
    fmlForSymbol t symb symbT = let         
        fmls = map fromHorn $ fst $ toFormulas trivialGen trivialGen $ split (constraintForSymbol t symb symbT)
      in conjunction $ Set.fromList fmls
    symbolType (Var x) (ScalarT b _) = ScalarT b (varRefinement x)
    symbolType _ t = t
constraintsBottomUp env (PApp funTempl argTempl) = do
  (fun, FunctionT x tArg tRes) <- constraintsBottomUp env funTempl
  (arg, tArg') <- constraintsBottomUp env argTempl
  addConstraint $ Subtype env tArg' tArg
  return (PApp fun arg, typeConjunction (renameVar valueVarName x tArg') tRes)
constraintsBottomUp env templ@(PFun _ bodyTempl) = do
  t@(FunctionT x tArg tRes) <- freshRefinements $ refine $ sTypeOf templ
  let env' = addSymbol (Var x) tArg env
  (pBody, tRes') <- constraintsBottomUp env' bodyTempl
  addConstraint $ WellFormed env t
  addConstraint $ Subtype env' tRes' tRes
  return (PFun x pBody, t)
constraintsBottomUp env (PIf _ thenTempl elseTempl) = do
  t <- freshRefinements $ refine $ sTypeOf thenTempl
  cond <- Unknown Map.empty <$> freshId "_u"
  let envThen = addAssumption cond env
  let envElse = addNegAssumption cond env
  (pThen, tThen) <- constraintsBottomUp envThen thenTempl
  (pElse, tElse) <- constraintsBottomUp envElse elseTempl
  addConstraint $ WellFormed (clearRanks env) t
  addConstraint $ WellFormedCond env cond
  addConstraint $ Subtype envThen tThen t
  addConstraint $ Subtype envElse tElse t  
  return (PIf cond pThen pElse, t)
constraintsBottomUp env (PFix s bodyTemp) = do
  t@(FunctionT x tArg tRes) <- freshRefinements $ refine s
  f <- freshId "_f"
  m <- freshId "_m"
  y <- freshId "_x"  
  let (ScalarT IntT fml) = tArg
  let tArg' = ScalarT IntT (fml |&| (valueVar |>=| IntLit 0) |&| (valueVar |<| Var m))
  let tArg'' = ScalarT IntT (fml |&| (valueVar |=| Var m))
  let env' = addSymbol (Var f) (FunctionT y tArg' (renameVar x y tRes)) . addRank (Var m) $ env
  (pBody, t') <- constraintsBottomUp env' bodyTemp
  addConstraint $ WellFormed env t
  addConstraint $ Subtype env t' (FunctionT x tArg'' tRes)
  return (PFix f pBody, t)  
      
-- | 'split' @c@ : split typing constraint @c@ that may contain function types into simple constraints (over only scalar types)
split :: Constraint -> [Constraint]
split (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2)) =
  split (Subtype env tArg2 tArg1) ++ split (Subtype (addSymbol (Var y) tArg2 env) (renameVar x y tRes1) tRes2)
split (WellFormed env (FunctionT x tArg tRes)) = 
  split (WellFormed env tArg) ++ split (WellFormed (addSymbol (Var x) tArg (clearRanks env)) tRes)
split (WellFormedLeaf (FunctionT x tArg tRes) ts) =
  split (WellFormedLeaf tArg (map argType ts)) ++ split (WellFormedLeaf tRes (map (\(FunctionT y tArg' tRes') -> renameVar y x tRes') ts))
split (WellFormedSymbol disjuncts)
  | length disjuncts == 1   = concatMap split (head disjuncts)
  | otherwise               = [WellFormedSymbol $ map (concatMap split) disjuncts]
split c = [c]

toFormulas :: QualsGen -> QualsGen -> [Constraint] -> ([Clause], QMap)
toFormulas cq tq cs = let (leafCs, nodeCs) = partition isWFLeaf cs
  in execState (mapM_ (toFormula cq tq) nodeCs >> mapM_ (toFormula cq tq) leafCs) ([], Map.empty)

-- | 'toFormula' @cq tq c@ : translate simple typing constraint @c@ into either a logical constraint or an element of the search space,
-- given search space generators @cq@ and @tq@
toFormula :: QualsGen -> QualsGen -> Constraint -> State ([Clause], QMap) ()
toFormula _ _ (Subtype env (ScalarT IntT fml) (ScalarT IntT fml')) =
  let (poss, negs) = embedding env 
  in _1 %= ((Horn $ conjunction (Set.insert fml poss) |=>| disjunction (Set.insert fml' negs)) :)
toFormula _ tq (WellFormed env (ScalarT IntT (Unknown _ u))) = 
  _2 %= Map.insert u (tq ((Map.keys $ symbolsByShape (ScalarT IntT ()) env) ++ env^.ranks))
toFormula cq _ (WellFormedCond env (Unknown _ u)) = 
  _2 %= Map.insert u (cq (Map.keys $ symbolsByShape (ScalarT IntT ()) env))
toFormula _ _ (WellFormedSymbol disjuncts) =
  _1 %= ((Disjunctive $ map (map fromHorn . fst . toFormulas trivialGen trivialGen) disjuncts) :)
toFormula _ _ (WellFormedLeaf (ScalarT IntT (Unknown _ u)) ts) = do
  quals <- (Set.toList . Set.unions) <$> mapM qualsFromType ts
  _2 %= Map.insert u (QSpace quals (length quals))
  where
    qualsFromType (ScalarT IntT fml) = Set.unions <$> mapM spaceFromQual (Set.toList $ conjunctsOf fml)
    spaceFromQual q@(Unknown _ _) = do
      qmap <- gets snd
      return $ Set.fromList $ lookupQualsSubst qmap q
    spaceFromQual (BoolLit True) = return $ Set.empty
    spaceFromQual q = return $ Set.singleton q  
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
