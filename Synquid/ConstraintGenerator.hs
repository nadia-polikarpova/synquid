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
emptyGen = const emptyQSpace

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
genConstraints params cq tq env t templ = if bottomUp params
                                              then runReader (evalStateT goBottomUp (0, [])) params
                                              else runReader (evalStateT goTopDown (0, [])) params
  where
    goTopDown :: Generator ([Clause], QMap, LiquidProgram)
    goTopDown = do
      p <- addVariableNames templ >>= constraintsTopDown env t
      cs <- gets snd
      let cs' = concatMap split cs
      let (clauses, qmap) = toFormulas cq tq cs'
      debug 1 (text "Typing Constraints" $+$ (vsep $ map pretty cs)) $ return (clauses, qmap, p)
      
    goBottomUp :: Generator ([Clause], QMap, LiquidProgram)
    goBottomUp = do
      p <- addVariableNames templ >>= constraintsBottomUp env
      addConstraint $ Subtype env (typ p) t
      cs <- gets snd
      let cs' = concatMap split cs
      let (clauses, qmap) = toFormulas cq tq cs'
      debug 1 (text "Typing Constraints" $+$ (vsep $ map pretty cs)) $ return (clauses, qmap, p)

{- Implementation -}
  
type Generator = StateT (Int, [Constraint]) (Reader ConsGenParams)

freshId :: String -> Generator String
freshId prefix = ((prefix ++) . show) <$> state (\(i, cs) -> (i, (i + 1, cs)))

freshVarId :: BaseType -> Generator String
freshVarId b = freshId $ show b
  
-- | 'freshRefinements' @t@ : a type with the same shape and value variables as @t@ but fresh unknowns as refinements
freshRefinements :: RType -> Generator RType
freshRefinements (ScalarT base _) = do
  k <- freshId "u"  
  return $ ScalarT base (Unknown Map.empty k)
freshRefinements (FunctionT x tArg tFun) = do
  liftM3 FunctionT (if isFunctionType tArg then freshId "f" else freshVarId $ baseType tArg) (freshRefinements tArg) (freshRefinements tFun)
  
addConstraint c = modify (\(i, cs) -> (i, c:cs))

-- | 'addVariableNames' @templ@ : generate fresh names for all bound variables in @templ@
-- (this has to be done before generating constraints)
addVariableNames :: Template -> Generator Template
addVariableNames (Program templ s) = (flip Program s) <$> case templ of
  PSymbol _ -> return templ
  PApp funTempl argTempl -> liftM2 PApp (addVariableNames funTempl) (addVariableNames argTempl)
  PFun _ bodyTempl -> liftM2 PFun (freshId "x") (addVariableNames bodyTempl)  
  PIf _ thenTempl elseTempl -> liftM2 (PIf ()) (addVariableNames thenTempl) (addVariableNames elseTempl)
  PMatch scrTempl caseTempls -> liftM2 PMatch (addVariableNames scrTempl) (mapM addToCase caseTempls)
  PFix _ bodyTempl -> liftM2 PFix (freshId "f") (addVariableNames bodyTempl)    
  where
    addToCase (Case consName args templ) = liftM2 (Case consName) (mapM (const (freshId "x")) args) (addVariableNames templ)  
  
-- | 'constraintsTopDown' @env t templ@ : a liquid program and typing constraints 
-- for a program of type @t@ following @templ@ in the typing environment @env@
constraintsTopDown :: Environment -> RType -> Template -> Generator LiquidProgram
constraintsTopDown env t (Program templ s) = case templ of
  PSymbol _ -> do
    abstract <- asks abstractLeaves
    t' <- if abstract then freshRefinements t else return t
    let symbols = symbolsByShape s env
    let leafConstraint = Map.mapWithKey (constraintForSymbol abstract t') symbols
    let disjuncts = map (:[]) $ Map.elems $ Map.mapWithKey (constraintForSymbol abstract t') symbols  
    if abstract  
      then do
        addConstraint $ WellFormedLeaf t' (Map.elems $ Map.mapWithKey symbolType symbols)
        when (isFunctionType s) $ addConstraint $ WellFormedSymbol disjuncts
        addConstraint $ Subtype env t' t
      else addConstraint $ WellFormedSymbol disjuncts  
    return $ Program (PSymbol leafConstraint) t'
    where    
      constraintForSymbol abstract t symb symbT = if abstract
                                                    then Subtype emptyEnv (symbolType symb symbT) t
                                                    else Subtype env (symbolType symb symbT) t
      symbolType x (ScalarT b _) = ScalarT b (varRefinement x b)
      symbolType _ t = t      
  PApp funTempl argTempl -> do
    x <- freshId "x"
    tArg <- freshRefinements $ refine $ typ argTempl
    let tFun = FunctionT x tArg t
    fun <- constraintsTopDown env tFun funTempl
    arg <- constraintsTopDown env tArg argTempl     
    addConstraint $ WellFormed env tArg
    return $ Program (PApp fun arg) t
  PFun x bodyTempl -> do
    let (FunctionT y tArg tRes) = t
    let env' = addSymbol x tArg env
    pBody <- constraintsTopDown env' (renameVar y x tArg tRes) bodyTempl
    return $ Program (PFun x pBody) t
  PIf _ thenTempl elseTempl -> do
    cond <- Unknown Map.empty <$> freshId "c"
    pThen <- constraintsTopDown (addAssumption cond env) t thenTempl
    pElse <- constraintsTopDown (addNegAssumption cond env) t elseTempl
    addConstraint $ WellFormedCond env cond
    return $ Program (PIf cond pThen pElse) t
  PMatch scrutineeTempl caseTempls -> do
    tScrutinee <- freshRefinements $ refine $ typ scrutineeTempl
    pScrutinee <- constraintsTopDown env tScrutinee scrutineeTempl
    
    x <- freshVarId (baseType $ typ scrutineeTempl)                         -- Generate a fresh variable that will represent the scrutinee in the case environments    
    let caseEnvs = map (addCaseSymbols env x tScrutinee) caseTempls         -- Add bindings for constructor arguments and refine the scrutinee type in the environment of each case     
    pCaseExprs <- zipWithM (\e temp -> constraintsTopDown e t temp) caseEnvs (map expr caseTempls)
    let pCases = zipWith (\(Case c args _) e -> Case c args e) caseTempls pCaseExprs
    addConstraint $ WellFormed env tScrutinee
    return $ Program (PMatch pScrutinee pCases) t        
  PFix f bodyTempl -> do
    abstract <- asks abstractFix
    t'@(FunctionT x tArg tRes) <- if abstract then freshRefinements t else return t
    let (Program (PFun argName _) _) = bodyTempl                  -- `bodyTempl' must be lambda
    let env' = addSymbol f (FunctionT x (recursiveTArg argName tArg) tRes) env
    pBody <- constraintsTopDown env' t bodyTempl
    when abstract $ (addConstraint $ WellFormed env t') >> (addConstraint $ Subtype env t' t)
    return $ Program (PFix f pBody) t'    
  
-- | 'constraintsBottomUp' @env templ@ : a liquid program, its type, and typing constraints 
-- for a program following @templ@ in the typing environment @env@  
constraintsBottomUp :: Environment -> Template -> Generator LiquidProgram
constraintsBottomUp env (Program templ s) = case templ of
  PSymbol _ -> do
    t <- freshRefinements $ refine s
    let symbols = symbolsByShape s env
    let leafConstraint = Map.mapWithKey (constraintForSymbol t) symbols
    let disjuncts = map (:[]) $ Map.elems $ Map.mapWithKey (constraintForSymbol t) symbols
    
    addConstraint $ WellFormedLeaf t (Map.elems $ Map.mapWithKey symbolType symbols)
    when (isFunctionType s) $ addConstraint $ WellFormedSymbol disjuncts
    return $ Program (PSymbol leafConstraint) t
    where    
      constraintForSymbol t symb symbT = Subtype emptyEnv (symbolType symb symbT) t
      symbolType x (ScalarT b _) = ScalarT b (varRefinement x b)
      symbolType _ t = t
  PApp funTempl argTempl -> do
    fun <- constraintsBottomUp env funTempl
    arg <- constraintsBottomUp env argTempl
    let FunctionT x tArg tRes = typ fun
    addConstraint $ Subtype env (typ arg) tArg
    return $ Program (PApp fun arg) (typeConjunction (renameVar valueVarName x tArg $ typ arg) tRes)
  PFun x bodyTempl -> do
    t@(FunctionT y tArg tRes) <- freshRefinements $ refine s
    let env' = addSymbol x tArg env
    pBody <- constraintsBottomUp env' bodyTempl
    addConstraint $ WellFormed env t
    addConstraint $ Subtype env' (renameVar x y tArg $ typ pBody) tRes
    return $ Program (PFun x pBody) t
  PIf _ thenTempl elseTempl -> do
    t <- freshRefinements $ refine s
    cond <- Unknown Map.empty <$> freshId "c"
    let envThen = addAssumption cond env
    let envElse = addNegAssumption cond env
    pThen <- constraintsBottomUp envThen thenTempl
    pElse <- constraintsBottomUp envElse elseTempl
    addConstraint $ WellFormed env t
    addConstraint $ WellFormedCond env cond
    addConstraint $ Subtype envThen (typ pThen) t
    addConstraint $ Subtype envElse (typ pElse) t  
    return $ Program (PIf cond pThen pElse) t
  PMatch scrutineeTempl caseTempls -> do
    t <- freshRefinements $ refine s                                          -- Abstract the type of the match, since it has to be an upper bound of multiple cases 
    pScrutinee <- constraintsBottomUp env scrutineeTempl                      -- Generate the scrutinee program
    
    x <- freshVarId (baseType $ typ scrutineeTempl)                           -- Generate a fresh variable that will represent the scrutinee in the case environments    
    let caseEnvs = map (addCaseSymbols env x (typ pScrutinee)) caseTempls         -- Add bindings for constructor arguments and refine the scrutinee type in the environment of each case     
    pCaseExprs <- zipWithM constraintsBottomUp caseEnvs (map expr caseTempls)
    let pCases = zipWith (\(Case c args _) e -> Case c args e) caseTempls pCaseExprs
    addConstraint $ WellFormed env t
    zipWithM_ (\env' t' -> addConstraint $ Subtype env' t' t) caseEnvs (map typ pCaseExprs)
    return $ Program (PMatch pScrutinee pCases) t    
  PFix f bodyTempl -> do
    t@(FunctionT x tArg tRes) <- freshRefinements $ refine s                    -- `s' must be a function type
    let (Program (PFun argName _) _) = bodyTempl                                -- `bodyTempl' must be lambda
    let env' = addSymbol f (FunctionT x (recursiveTArg argName tArg) tRes) env  -- `f' is added to the environment with additional assumptions on its argument to ensure termination
    pBody <- constraintsBottomUp env' bodyTempl
    addConstraint $ WellFormed env t
    addConstraint $ Subtype env (typ pBody) t
    return $ Program (PFix f pBody) t

-- | 'addCaseSymbols' @env x tX case@ : extension of @env@ that assumes that scrutinee @x@ of type @tX@ matches @case@.
addCaseSymbols env x tX (Case consName argNames _) = 
  case Map.lookup consName (env ^. symbols) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env 
    Just t -> addCaseSymbols' env argNames x tX t
addCaseSymbols' env [] x (ScalarT baseT fml) (ScalarT _ fml') = let subst = substitute (Map.singleton valueVarName (Var baseT x)) in 
  addAssumption (subst fml) . addNegAssumption (fnot $ subst fml') $ env -- fml' is added since it does not contain unknowns (it is the constructor type), and we want to allow vacuous cases
addCaseSymbols' env (arg : args) x tX (FunctionT y tArg tRes) = addCaseSymbols' (addSymbol arg tArg env) args x tX (renameVar y arg tArg tRes)

-- | 'recursiveTArg' @argName t@ : type of the argument of a recursive call,
-- inside the body of the recursive function where its argument has name @argName@ and type @t@
-- (@t@ strengthened with a termination condition)
recursiveTArg argName (ScalarT IntT fml) = ScalarT IntT (fml  |&|  valInt |>=| IntLit 0  |&|  valInt |<| intVar argName)
recursiveTArg argName (ScalarT ListT fml) = ScalarT ListT (fml  |&|  Measure IntT "len" valList |<| Measure IntT "len" (listVar argName))
      
-- | 'split' @c@ : split typing constraint @c@ that may contain function types into simple constraints (over only scalar types)
split :: Constraint -> [Constraint]
split (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2)) =
  split (Subtype env tArg2 tArg1) ++ split (Subtype (addSymbol y tArg2 env) (renameVar x y tArg2 tRes1) tRes2)
split (WellFormed env (FunctionT x tArg tRes)) = 
  split (WellFormed env tArg) ++ split (WellFormed (addSymbol x tArg env) tRes)
split (WellFormedLeaf (FunctionT x tArg tRes) ts) =
  split (WellFormedLeaf tArg (map argType ts)) ++ split (WellFormedLeaf tRes (map (\(FunctionT y tArg' tRes') -> renameVar y x tArg tRes') ts))
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
toFormula _ _ (Subtype env (ScalarT baseT fml) (ScalarT baseT' fml')) | baseT == baseT' 
  = let (poss, negs) = embedding env 
  in _1 %= ((Horn $ conjunction (Set.insert fml poss) |=>| disjunction (Set.insert fml' negs)) :)
toFormula _ tq (WellFormed env (ScalarT baseT (Unknown _ u))) = 
  _2 %= Map.insert u (tq $ Var baseT valueVarName : allScalars env)
toFormula cq _ (WellFormedCond env (Unknown _ u)) =
  _2 %= Map.insert u (cq $ allScalars env)
toFormula _ _ (WellFormedSymbol disjuncts) =
  _1 %= ((Disjunctive $ map (map fromHorn . fst . toFormulas emptyGen emptyGen) disjuncts) :)
toFormula _ _ (WellFormedLeaf (ScalarT baseT (Unknown _ u)) ts) = do
  spaces <- mapM qualsFromType ts
  let quals = Set.toList $ Set.unions $ spaces
  let n = maximum $ map Set.size spaces
  _2 %= Map.insert u (QSpace quals n)
  where
    qualsFromType (ScalarT baseT fml) = Set.unions <$> mapM spaceFromQual (Set.toList $ conjunctsOf fml)
    spaceFromQual q@(Unknown _ _) = do
      qmap <- gets snd
      return $ Set.fromList $ lookupQualsSubst qmap q
    spaceFromQual (BoolLit True) = return $ Set.empty
    spaceFromQual q = return $ Set.singleton q  
toFormula _ _ c = error $ show $ text "Not a simple constraint:" $+$ pretty c

-- | 'extract' @sol prog@ : simple program encoded in @prog@ when all unknowns are instantiated according to @sol@
extract :: SMTSolver s => Solution -> LiquidProgram -> MaybeT s SimpleProgram
extract sol (Program prog t) = let go = extract sol in (flip Program (typeApplySolution sol t)) <$> case prog of
  PSymbol leafConstraint -> msum $ map extractSymbol (Map.toList $ leafConstraint)     
  PApp pFun pArg -> liftM2 PApp (go pFun) (go pArg)
  PFun x pBody -> liftM (PFun x) (go pBody)
  PIf cond pThen pElse -> liftM2 (PIf $ applySolution sol cond) (go pThen) (go pElse)
  PMatch pScr pCases -> liftM2 PMatch (go pScr) (mapM extractCase pCases)
  PFix f pBody -> liftM (PFix f) (go pBody)
  where
    extractSymbol (symb, c) = do   
      let fml = conjunction $ Set.fromList $ map fromHorn $ fst $ toFormulas emptyGen emptyGen $ split c
      let fml' = applySolution sol fml
      res <- debug 1 (text "Check symbol" <+> pretty symb <+> parens (pretty fml) <+> pretty fml') $ lift $ isValid fml'
      if res then debug 1 (text "OK") $ return (PSymbol symb) else debug 1 (text "MEH") $ mzero
      
    extractCase (Case consName argNames expr) = liftM (Case consName argNames) (extract sol expr)
