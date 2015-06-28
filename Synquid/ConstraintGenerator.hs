{-# LANGUAGE TemplateHaskell #-}

-- | Generating synthesis constraints from specifications, qualifiers, and program templates
module Synquid.ConstraintGenerator where

import Synquid.Logic
import Synquid.Program
import Synquid.Util
import Synquid.Pretty
import Synquid.SMTSolver
import Data.Maybe
import Data.Either
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
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

-- | Parameters of program template exploration
data ExplorerParams = ExplorerParams {
  _eGuessDepth :: Int,      -- ^ Maximum depth of application trees
  _scrutineeDepth :: Int,   -- ^ Maximum depth of application trees inside match scrutinees
  _matchDepth :: Int,       -- ^ Maximum nesting level of matches
  _condDepth :: Int,        -- ^ Maximum nesting level of conditionals
  _abstractLeafs :: Bool    -- ^ Use symbolic leaf search?
}

makeLenses ''ExplorerParams

-- | Computations that explore program templates (parametrized by the backtracking monad)
type Explorer m = StateT (Int, [Constraint]) (ReaderT ExplorerParams m)

--- | 'genConstraints' @params cq tq env typ@ : given parameters @params@, search space generators for conditionals and types @cq@ and @tq@,
--- top-level type environment @env@, and refinement type @typ@,
--- generate a set of constraints, a search space map for the unknowns inside those constraints, and a liquid program,
--- such that a valid solution for the constraints, if exists, would turn the liquid program into a simple program of type @typ@.
genConstraints :: MonadPlus m => ExplorerParams -> QualsGen -> QualsGen -> Environment -> RType -> m ([Clause], QMap, LiquidProgram)
genConstraints params cq tq env t = runReaderT (evalStateT go (0, [])) params 
  where
    go = do
      p <- generateI env t
      cs <- gets snd
      let cs' = concatMap split cs
      let (clauses, qmap) = toFormulas cq tq cs'
      debug 1 ( text "Typing Constraints" $+$ (vsep $ map pretty cs) $+$ 
          text "Liquid Program" $+$ pretty p) $ 
          return (clauses, qmap, p)

{- Implementation -}

addConstraint c = modify (\(i, cs) -> (i, c:cs))

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: MonadPlus m => String -> Explorer m String
freshId prefix = do
  i <- use _1
  _1 .= i + 1
  return $ prefix ++ show i
  
-- | 'freshRefinements @t@ : a type with the same shape and variables as @t@ but fresh unknowns as refinements
freshRefinements :: MonadPlus m => RType -> Explorer m RType
freshRefinements (ScalarT base _) = do
  k <- freshId "u"  
  return $ ScalarT base (Unknown Map.empty k)
freshRefinements (FunctionT x tArg tFun) = do
  liftM3 FunctionT (freshId "x") (freshRefinements tArg) (freshRefinements tFun)
  
-- | 'generateE' @env s@ : explore all liquid e-terms of type shape @s@ in environment @env@
-- (bottom-up phase of bidirectional typechecking)  
generateE :: MonadPlus m => Environment -> SType -> Explorer m (Environment, LiquidProgram)
generateE env s = generateVar `mplus` generateApp
  where
    -- | Explore all variables of shape @s@
    generateVar = do
          let symbols = symbolsByShape s env
          abstract <- asks _abstractLeafs
          if abstract && Map.size symbols > 1
            then do
              t <- freshRefinements $ refineTop s          
              let leafConstraint = Map.mapWithKey (constraintForSymbol t) symbols
              let disjuncts = map (:[]) $ Map.elems $ Map.mapWithKey (constraintForSymbol t) symbols          
              addConstraint $ WellFormedLeaf t (Map.elems $ Map.mapWithKey symbolType symbols)
              when (isFunctionType s) $ addConstraint $ WellFormedSymbol disjuncts
              return (env, Program (PSymbol leafConstraint) t)
            else msum $ map genKnownSymbol $ Map.toList symbols
        
    genKnownSymbol (name, t) = return (env, Program (PSymbol $ Map.singleton name Unconstrained) (symbolType name t))
    
    constraintForSymbol t symb symbT = Subtype emptyEnv (symbolType symb symbT) t
    
    symbolType x (ScalarT b _) = ScalarT b (varRefinement x b)
    symbolType _ t = t    
    
    -- | Explore all applications of shape @s@ of an e-term to an i-term
    generateApp = do
      d <- asks _eGuessDepth
      if d == 0 
        then mzero 
        else 
          -- Since we know that the head of an e-term is always a variable, 
          -- check the function variables in the context to decide what the last argument shape can be
          let argShapes = nub $ catMaybes $ map (argProducing s) $ Map.keys (env ^. symbolsOfShape)
          in msum $ map generateWithArgShape argShapes
         
    -- | 'argProducing' @s sF@ : if @sF@ is a function type that can eventually produce @s@, the type of the last argument in @sF@ before @s@;
    -- otherwise Nothing
    argProducing :: SType -> SType -> Maybe SType
    argProducing s (ScalarT _ _) = Nothing
    argProducing s (FunctionT _ sArg sRes) = if s == sRes then Just sArg else argProducing s sRes          
          
    -- | Explore all applications of shape @s@ of an e-term to an i-term of shape @sArg@
    generateWithArgShape sArg = do
      (env', fun) <- generateE env (sArg |->| s)
      let FunctionT x tArg tRes = typ fun            
      -- arg <- local (over eGuessDepth (-1 +) . set matchDepth 0) $ generateI env' tArg -- the argument is an i-term but matches and conditionals are disallowed; TODO: is this complete?
      (env'', arg) <- local (over eGuessDepth (-1 +)) $ generateE env' sArg
      addConstraint $ Subtype env'' (typ arg) tArg
      
      let env''' = addGhost x (typ arg) env''      
      return (env''', Program (PApp fun arg) tRes)
      
    addGhost x (ScalarT baseT fml) env = let subst = substitute (Map.singleton valueVarName (Var baseT x)) in 
      addAssumption (subst fml) env
    addGhost _ (FunctionT _ _ _) env = env
     
-- | 'generateI' @env t@ : explore all liquid terms of type @t@ in environment @env@
-- (top-down phase of bidirectional typechecking)  
generateI :: MonadPlus m => Environment -> RType -> Explorer m LiquidProgram
generateI env t@(FunctionT x tArg tRes) = generateFix x tArg tRes
  where
    generateFix x tArg tRes = do
      -- TODO: abstract fix type?
      f <- freshId "f"
      y <- freshId "x"
      let env' =  addSymbol x tArg .
                  addSymbol f (FunctionT y (recursiveTArg x tArg) (renameVar x y tArg tRes))
                  $ env
      pBody <- generateI env' tRes
      return $ Program (PFix f (Program (PFun x pBody) t)) t
      
    -- | 'recursiveTArg' @argName t@ : type of the argument of a recursive call,
    -- inside the body of the recursive function where its argument has name @argName@ and type @t@
    -- (@t@ strengthened with a termination condition)
    recursiveTArg argName (ScalarT IntT fml) = ScalarT IntT (fml  |&|  valInt |>=| IntLit 0  |&|  valInt |<| intVar argName)
    recursiveTArg argName (ScalarT IListT fml) = ScalarT IListT (fml  |&|  Measure IntT "len" valList |<| Measure IntT "len" (listVar argName))
          
generateI env t@(ScalarT _ _) = guessE `mplus` generateMatch `mplus` generateIf
  where
    -- | Guess and check
    guessE = do
      (env', res) <- generateE env (shape t)
      addConstraint $ Subtype env' (typ res) t
      return res
      
    -- | Generate a match term of type @t@
    generateMatch = do
      d <- asks _matchDepth
      if d == 0
        then mzero
        else do
          let scrShape = ScalarT IListT ()                                                                                        -- Pick a datatype to match on (TODO: other datatypes)
          (env', pScrutinee) <- local (\params -> set eGuessDepth (view scrutineeDepth params) params) $ generateE env scrShape   -- Guess a scrutinee of the chosen shape
          
          x <- freshId "x"                                                                                                        -- Generate a fresh variable that will represent the scrutinee in the case environments
          pCases <- mapM (generateCase env' x (typ pScrutinee)) $ (env ^. constructors) Map.! (baseType scrShape)                 -- Generate a case for each constructor of the datatype
          return $ Program (PMatch pScrutinee pCases) t
      
    -- | Generate the @consName@ case of a match term with scrutinee variable @scrName@ and scrutinee type @scrType@
    generateCase env scrName scrType consName = do
      case Map.lookup consName (env ^. symbols) of
        Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env 
        Just consT -> do
          (args, caseEnv) <- addCaseSymbols env scrName scrType consT -- Add bindings for constructor arguments and refine the scrutinee type in the environment
          pCaseExpr <- local (over matchDepth (-1 +)) $ generateI caseEnv t          
          return $ Case consName args pCaseExpr
          
    -- | 'addCaseSymbols' @env x tX case@ : extension of @env@ that assumes that scrutinee @x@ of type @tX@.
    addCaseSymbols env x (ScalarT baseT fml) (ScalarT _ fml') = let subst = substitute (Map.singleton valueVarName (Var baseT x)) in 
      return $ ([], addAssumption (subst fml) . addNegAssumption (fnot $ subst fml') $ env) -- fml' is added since it does not contain unknowns (it is the constructor type), and we want to allow vacuous cases
    addCaseSymbols env x tX (FunctionT y tArg tRes) = do
      argName <- freshId "y"
      (args, env') <- addCaseSymbols (addSymbol argName tArg env) x tX (renameVar y argName tArg tRes)
      return (argName : args, env')          
    
    -- | Generate a conditional term of type @t@
    generateIf = do
      d <- asks _condDepth
      if d == 0
        then mzero
        else do    
          cond <- Unknown Map.empty `liftM` freshId "c"
          pThen <- local (over condDepth (-1 +)) $ generateI (addAssumption cond env) t
          pElse <- local (over condDepth (-1 +)) $ generateI (addNegAssumption cond env) t
          addConstraint $ WellFormedCond env cond
          return $ Program (PIf cond pThen pElse) t
      
      
-- | 'split' @c@ : split typing constraint @c@ that may contain function types into simple constraints (over only scalar types)
split :: Constraint -> [Constraint]
split Unconstrained = []
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
  let n = if null spaces then 0 else maximum $ map Set.size spaces
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
