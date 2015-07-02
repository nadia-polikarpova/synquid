{-# LANGUAGE TemplateHaskell #-}

-- | Generating synthesis constraints from specifications, qualifiers, and program templates
module Synquid.Explorer where

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

-- | Incremental second-order constraint solver
data ConstraintSolver s = ConstraintSolver {
  csInit :: s Candidate,                                                          -- ^ Initial candidate solution
  csRefine :: [Clause] -> QMap -> LiquidProgram -> [Candidate] -> s [Candidate],  -- ^ Refine current list of candidates to satisfy new constraints
  csExtract :: LiquidProgram -> Candidate -> s SimpleProgram                      -- ^ Extract a program from a valid solution
}

-- | Parameters of program exploration
data ExplorerParams s = ExplorerParams {
  _eGuessDepth :: Int,            -- ^ Maximum depth of application trees
  _scrutineeDepth :: Int,         -- ^ Maximum depth of application trees inside match scrutinees
  _matchDepth :: Int,             -- ^ Maximum nesting level of matches
  _condDepth :: Int,              -- ^ Maximum nesting level of conditionals
  _abstractLeafs :: Bool,         -- ^ Use symbolic leaf search?
  _condQualsGen :: QualsGen,      -- ^ Qualifier generator for conditionals
  _typeQualsGen :: QualsGen,      -- ^ Qualifier generator for types
  _solver :: ConstraintSolver s   -- ^ Constraint solver
}

makeLenses ''ExplorerParams

-- | State of program exploration
data ExplorerState = ExplorerState {
  _idCount :: Int,                      -- ^ Number of unique identifiers issued so far
  _candidates :: [Candidate],           -- ^ Current set of candidate solutions to unknowns
  _unsolvedConstraints :: [Constraint], -- ^ Typing constraints accumulated since the candidates have been last refined
  _qualifierMap :: QMap                 -- ^ State spaces for all the unknowns
}

makeLenses ''ExplorerState

-- | Computations that explore programs, parametrized by the the constraint solver and the backtracking monad
type Explorer s m = StateT ExplorerState (ReaderT (ExplorerParams s) (m s))

-- | 'explore' @params env typ@ : explore all programs that have type @typ@ in the environment @env@;
-- exploration is driven by @params@
explore :: (Monad s, MonadTrans m, MonadPlus (m s)) => ExplorerParams s -> Environment -> RType -> m s SimpleProgram
explore params env t = do
    initCand <- lift $ csInit (_solver params)
    runReaderT (evalStateT go (ExplorerState 0 [initCand] [] Map.empty)) params 
  where
    go :: (Monad s, MonadTrans m, MonadPlus (m s)) => Explorer s m SimpleProgram
    go = do
      p <- generateI env t          
      -- solveConstraints p
      solv <- asks _solver
      cands <- use candidates
      lift . lift . lift $ (csExtract solv) p (head cands)

{- Implementation -}

-- | Impose typing constraint @c@ on the programs
addConstraint c = unsolvedConstraints %= (c :)

-- | Solve all currently unsolved constraints
-- (program @p@ is only used for debug information)
solveConstraints :: (Monad s, MonadTrans m, MonadPlus (m s)) => LiquidProgram -> Explorer s m ()
solveConstraints p = do
  -- Convert new constraints into formulas and augment the current qualifier map with new unknowns
  cs <- use unsolvedConstraints
  let cs' = concatMap split cs  
  oldQuals <- use qualifierMap
  cq <- asks _condQualsGen
  tq <- asks _typeQualsGen
  let (clauses, newQuals) = toFormulas cq tq cs'
  let qmap = Map.union oldQuals newQuals
  debug 1 ( text "Typing Constraints" $+$ (vsep $ map pretty cs) $+$ 
    text "Liquid Program" $+$ pretty p) $ 
    return ()
  
  -- Refine the current candidate solutions using the new constraints; fail if no solution
  cands <- use candidates      
  solv <- asks _solver
  cands' <- if null clauses then return cands else lift . lift .lift $ (csRefine solv) clauses qmap p cands
  guard (not $ null cands')
  
  -- Update state
  unsolvedConstraints .= []
  candidates .= cands'
  qualifierMap .= qmap
  
-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: (Monad s, MonadTrans m, MonadPlus (m s)) =>String -> Explorer s m String
freshId prefix = do
  i <- use idCount
  idCount .= i + 1
  return $ prefix ++ show i
  
-- | 'freshRefinements @t@ : a type with the same shape and variables as @t@ but fresh unknowns as refinements
freshRefinements :: (Monad s, MonadTrans m, MonadPlus (m s)) => RType -> Explorer s m RType
freshRefinements (ScalarT base _) = do
  k <- freshId "u"  
  return $ ScalarT base (Unknown Map.empty k)
freshRefinements (FunctionT x tArg tFun) = do
  liftM3 FunctionT (freshId "x") (freshRefinements tArg) (freshRefinements tFun)
  
-- | 'generateE' @env s@ : explore all liquid e-terms of type shape @s@ in environment @env@
-- (bottom-up phase of bidirectional typechecking)  
generateE :: (Monad s, MonadTrans m, MonadPlus (m s)) => Environment -> SType -> Explorer s m (Environment, LiquidProgram)
generateE env s = generateVar `mplus` generateApp
  where
    -- | Explore all variables of shape @s@
    generateVar = do
          let symbols = symbolsByShape s env
          -- abstract <- asks _abstractLeafs
          -- if abstract && Map.size symbols > 1
            -- then do
              -- t <- freshRefinements $ refine s          
              -- let leafConstraint = Map.mapWithKey (constraintForSymbol t) symbols
              -- let disjuncts = map (:[]) $ Map.elems $ Map.mapWithKey (constraintForSymbol t) symbols          
              -- addConstraint $ WellFormedLeaf t (Map.elems $ Map.mapWithKey symbolType symbols)
              -- when (isFunctionType s) $ addConstraint $ WellFormedSymbol disjuncts
              -- return (env, Program (PSymbol leafConstraint) t)
            -- else msum $ map genKnownSymbol $ Map.toList symbols
          msum $ map genKnownSymbol $ Map.toList symbols
        
    genKnownSymbol (name, (typeSubst, sch)) = case sch of 
      Monotype t -> return (env, Program (PSymbol (Map.singleton name Unconstrained) Map.empty) (symbolType name t)) -- Precise match
      sch -> do -- Unification
        ts <- mapM (freshRefinements . refine) (Map.elems typeSubst)
        mapM_ (addConstraint . WellFormed emptyEnv) ts
        let typeSubst' = Map.fromList $ zip (Map.keys typeSubst) ts        
        return (env, Program
                      (PSymbol (Map.singleton name Unconstrained) typeSubst')
                      (typeSubstitute typeSubst' $ toMonotype sch))

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
          let argShapes = undefined -- nub $ catMaybes $ map (argProducing s) $ Map.keys (env ^. symbolsOfShape)
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
      solveConstraints arg
      
      y <- freshId "x" 
      let env''' = addGhost y (typ arg) env''      
      return (env''', Program (PApp fun arg) (renameVar x y tArg tRes))      
      
    addGhost x (ScalarT baseT fml) env = let subst = substitute (Map.singleton valueVarName (Var baseT x)) in 
      addAssumption (subst fml) env
    addGhost _ (FunctionT _ _ _) env = env
     
-- | 'generateI' @env t@ : explore all liquid terms of type @t@ in environment @env@
-- (top-down phase of bidirectional typechecking)  
generateI :: (Monad s, MonadTrans m, MonadPlus (m s)) => Environment -> RType -> Explorer s m LiquidProgram  

generateI env t@(FunctionT x tArg tRes) = generateFix
  where
    generateFix = do
      -- TODO: abstract fix type?      
      y <- freshId "x"
      let env' = addSymbol x tArg $ env
      
      let recTArgMb = recursiveTArg x tArg
      case recTArgMb of
        Nothing -> do -- Cannot recurse on this argument: generate an ordinary abstraction          
          pBody <- generateI env' tRes
          return $ Program (PFun x pBody) t
                  
        Just recTArg -> do  -- Can recurse on this argument: generate a fixpoint
          f <- freshId "f"      
          let env'' = addSymbol f (FunctionT y recTArg (renameVar x y tArg tRes)) $ env'
          pBody <- generateI env'' tRes
          return $ Program (PFix f (Program (PFun x pBody) t)) t
      
    -- generateFix x tArg tRes = do
      -- let env' = addSymbol x tArg env
      -- pBody <- generateI env' tRes
      -- return $ Program (PFun x pBody) t      
      
    -- | 'recursiveTArg' @argName t@ : type of the argument of a recursive call,
    -- inside the body of the recursive function where its argument has name @argName@ and type @t@
    -- (@t@ strengthened with a termination condition)
    recursiveTArg _ (FunctionT _ _ _) = Nothing
    recursiveTArg argName (ScalarT IntT fml) = Just $ ScalarT IntT (fml  |&|  valInt |>=| IntLit 0  |&|  valInt |<| intVar argName)
    recursiveTArg argName (ScalarT (TypeVarT _) fml) = Nothing
    recursiveTArg argName (ScalarT dt@(DatatypeT name) fml) = case env ^. datatypes . to (Map.! name) . wfMetric of
      Nothing -> Nothing
      Just metric -> Just $ ScalarT (DatatypeT name) (fml |&| metric (Var dt valueVarName) |<| metric (Var dt argName))
          
generateI env t@(ScalarT _ _) = guessE `mplus` generateMatch `mplus` generateIf
  where
    -- | Guess and check
    guessE = do
      (env', res) <- generateE env (shape t)
      addConstraint $ Subtype env' (typ res) t
      solveConstraints res
      return res
      
    -- | Generate a match term of type @t@
    generateMatch = do
      d <- asks _matchDepth
      if d == 0
        then mzero
        else do
          scrDT <- msum (map return $ Map.keys (env ^. datatypes))                                         -- Pick a datatype to match on
          (env', pScrutinee) <- local (\params -> set eGuessDepth (view scrutineeDepth params) params) $ generateE env (ScalarT (DatatypeT scrDT) ())   -- Guess a scrutinee of the chosen shape
          
          x <- freshId "x"                                                                                                        -- Generate a fresh variable that will represent the scrutinee in the case environments
          pCases <- mapM (generateCase env' x (typ pScrutinee)) $ ((env ^. datatypes) Map.! scrDT) ^. constructors                -- Generate a case for each constructor of the datatype
          return $ Program (PMatch pScrutinee pCases) t
      
    -- | Generate the @consName@ case of a match term with scrutinee variable @scrName@ and scrutinee type @scrType@
    generateCase env scrName scrType consName = do
      case Map.lookup consName (env ^. symbols) of
        Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env 
        Just consT -> do
          (args, caseEnv) <- addCaseSymbols env scrName scrType (toMonotype consT) -- Add bindings for constructor arguments and refine the scrutinee type in the environment
          pCaseExpr <- local (over matchDepth (-1 +)) $ generateI caseEnv t          
          return $ Case consName args pCaseExpr
          
    -- | 'addCaseSymbols' @env x tX case@ : extension of @env@ that assumes that scrutinee @x@ of type @tX@.
    addCaseSymbols env x (ScalarT baseT fml) (ScalarT _ fml') = let subst = substitute (Map.singleton valueVarName (Var baseT x)) in 
      return $ ([], addAssumption (subst fml) . addNegAssumption (fnot $ subst fml') $ env) -- here vacuous cases are allowed
      -- return $ ([], addAssumption (subst fml) . addAssumption (subst fml') $ env) -- here disallowed unless no other choice
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
          addConstraint $ WellFormedCond env cond
          pThen <- local (over condDepth (-1 +)) $ generateI (addAssumption cond env) t
          pElse <- local (over condDepth (-1 +)) $ generateI (addNegAssumption cond env) t          
          return $ Program (PIf cond pThen pElse) t
      
      
-- | 'split' @c@ : split typing constraint @c@ that may contain function types into simple constraints (over only scalar types)
split :: Constraint -> [Constraint]
split Unconstrained = []
split (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2)) = -- TODO: rename type vars
  split (Subtype env tArg2 tArg1) ++ split (Subtype (addSymbol y tArg2 env) (renameVar x y tArg2 tRes1) tRes2)
split (WellFormed env (FunctionT x tArg tRes)) = 
  split (WellFormed env tArg) ++ split (WellFormed (addSymbol x tArg env) tRes)
split (WellFormedLeaf (FunctionT x tArg tRes) ts) = -- TODO: typ vars?
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
toFormula _ _ (Subtype env (ScalarT baseT _) (ScalarT baseT' (BoolLit True))) | baseT == baseT' 
  = return ()
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

-- | 'extractProgram' @sol prog@ : simple program encoded in @prog@ when all unknowns are instantiated according to @sol@
extractProgram :: SMTSolver s => Solution -> LiquidProgram -> MaybeT s SimpleProgram
extractProgram sol (Program prog sch) = let go = extractProgram sol in (flip Program (typeApplySolution sol sch)) <$> case prog of
  PSymbol leafConstraint subst -> msum $ map (extractSymbol $ Map.map (typeApplySolution sol) subst) (Map.toList $ leafConstraint) -- TODO: different substitutions
  PApp pFun pArg -> liftM2 PApp (go pFun) (go pArg)
  PFun x pBody -> liftM (PFun x) (go pBody)
  PIf cond pThen pElse -> liftM2 (PIf $ applySolution sol cond) (go pThen) (go pElse)
  PMatch pScr pCases -> liftM2 PMatch (go pScr) (mapM extractCase pCases)
  PFix f pBody -> liftM (PFix f) (go pBody)
  where
    extractSymbol subst (symb, c) = do   
      let fml = conjunction $ Set.fromList $ map fromHorn $ fst $ toFormulas emptyGen emptyGen $ split c
      let fml' = applySolution sol fml
      res <- debug 1 (text "Check symbol" <+> pretty symb <+> parens (pretty fml) <+> pretty fml') $ lift $ isValid fml'
      if res then debug 1 (text "OK") $ return (PSymbol symb subst) else debug 1 (text "MEH") $ mzero
      
    extractCase (Case consName argNames expr) = liftM (Case consName argNames) (extractProgram sol expr)
