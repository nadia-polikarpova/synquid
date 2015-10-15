{-# LANGUAGE TemplateHaskell, FlexibleContexts, TupleSections #-}

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
import qualified Data.Traversable as T
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
  csInit :: s Candidate,                                                      -- ^ Initial candidate solution
  csRefine :: [Formula] -> QMap -> RProgram -> [Candidate] -> s [Candidate],  -- ^ Refine current list of candidates to satisfy new constraints
  csPruneQuals :: QSpace -> s QSpace                                          -- ^ Prune redundant qualifiers
}

-- | Choices for the type of terminating fixpoint operator
data FixpointStrategy = 
    DisableFixpoint   -- ^ Do not use fixpoint
  | FirstArgument     -- ^ Fixpoint decreases the first well-founded argument
  | AllArguments      -- ^ Fixpoint decreases the lexicographical tuple of all well-founded argument in declaration order 

-- | Parameters of program exploration
data ExplorerParams s = ExplorerParams {
  _eGuessDepth :: Int,                -- ^ Maximum depth of application trees
  _scrutineeDepth :: Int,             -- ^ Maximum depth of application trees inside match scrutinees
  _matchDepth :: Int,                 -- ^ Maximum nesting level of matches
  _condDepth :: Int,                  -- ^ Maximum nesting level of conditionals
  _fixStrategy :: FixpointStrategy,   -- ^ How to generate terminating fixpoints
  _polyRecursion :: Bool,             -- ^ Enable polymorphic recursion?
  _incrementalSolving :: Bool,        -- ^ Solve constraints as they appear (as opposed to all at once)?
  _condQualsGen :: QualsGen,          -- ^ Qualifier generator for conditionals
  _typeQualsGen :: QualsGen,          -- ^ Qualifier generator for types
  _solver :: ConstraintSolver s       -- ^ Constraint solver
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

-- | Impose typing constraint @c@ on the programs
addConstraint c = unsolvedConstraints %= (c :)

-- | Computations that explore programs, parametrized by the the constraint solver and the backtracking monad
type Explorer s m = StateT ExplorerState (ReaderT (ExplorerParams s) (m s))

-- | 'explore' @params env typ@ : explore all programs that have type @typ@ in the environment @env@;
-- exploration is driven by @params@
explore :: (Monad s, MonadTrans m, MonadPlus (m s)) => ExplorerParams s -> Environment -> RSchema -> m s RProgram
explore params env sch = do
    initCand <- lift $ csInit (_solver params)
    runReaderT (evalStateT go (ExplorerState 0 [initCand] [] Map.empty)) params 
  where
    go :: (Monad s, MonadTrans m, MonadPlus (m s)) => Explorer s m RProgram
    go = do
      p <- generateTopLevel env sch
      ifM (asks _incrementalSolving) (return ()) (solveConstraints p)
      sol <- uses candidates (solution . head)
      return $ programApplySolution sol p

{- AST exploration -}
    
-- | 'generateTopLevel' @env t@ : explore all terms that have refined type schema @sch@ in environment @env@    
generateTopLevel :: (Monad s, MonadTrans m, MonadPlus (m s)) => Environment -> RSchema -> Explorer s m RProgram
generateTopLevel env (Forall a sch) = generateTopLevel (addTypeVar a env) sch
generateTopLevel env (Monotype t@(FunctionT _ _ _)) = generateFix env t
  where
    generateFix env t = do
      recCalls <- recursiveCalls t
      polymorphic <- asks _polyRecursion
      -- TODO: add unification constraint
      let env' = if polymorphic
                    then let tvs = env ^. boundTypeVars in 
                      foldr (\(f, t') -> addPolyVariable f (foldr Forall (Monotype t') tvs) . (shapeConstraints %~ Map.insert f (shape t))) env recCalls -- polymorphic recursion enabled: generalize on all bound variables
                    else foldr (\(f, t') -> addVariable f t') env recCalls  -- do not generalize
      p <- generateI env' t
      return $ if null recCalls then p else Program (PFix (map fst recCalls) p) t

    -- | 'recursiveCalls' @t@: name-type pairs for recursive calls to a function with type @t@;
    -- (when using lexicographic termination metrics, different calls differ in the component they decrease; otherwise at most one call). 
    recursiveCalls (FunctionT x tArg tRes) = do
      y <- freshId "x"
      calls' <- recursiveCalls tRes
      case recursiveTArg x tArg of
        Nothing -> return $ map (\(f, tRes') -> (f, FunctionT y tArg (renameVar x y tArg tRes'))) calls'
        Just (tArgLt, tArgEq) -> do
          f <- freshId "f"
          fixStrategy <- asks _fixStrategy
          case fixStrategy of
            AllArguments -> return $ (f, FunctionT y tArgLt (renameVar x y tArg tRes)) : map (\(f, tRes') -> (f, FunctionT y tArgEq (renameVar x y tArg tRes'))) calls'
            FirstArgument -> return [(f, FunctionT y tArgLt (renameVar x y tArg tRes))]
            DisableFixpoint -> return []
    recursiveCalls _ = return []
        
    -- | 'recursiveTArg' @argName t@ : type of the argument of a recursive call,
    -- inside the body of the recursive function where its argument has name @argName@ and type @t@
    -- (@t@ strengthened with a termination condition)    
    recursiveTArg argName (ScalarT IntT _ fml) = Just $ (int (fml  |&|  valInt |>=| IntLit 0  |&|  valInt |<| intVar argName), int (fml  |&|  valInt |=| intVar argName))
    recursiveTArg argName (ScalarT dt@(DatatypeT name) tArgs fml) = case env ^. datatypes . to (Map.! name) . wfMetric of
      Nothing -> Nothing
      Just metric -> Just $ (ScalarT (DatatypeT name) tArgs (fml |&| metric (Var dt valueVarName) |<| metric (Var dt argName)), 
        ScalarT (DatatypeT name) tArgs (fml |&| metric (Var dt valueVarName) |=| metric (Var dt argName)))
    recursiveTArg _ _ = Nothing
    
generateTopLevel env (Monotype t) = generateI env t    

-- | 'generateI' @env t@ : explore all terms that have refined type @t@ in environment @env@
-- (top-down phase of bidirectional typechecking)  
generateI :: (Monad s, MonadTrans m, MonadPlus (m s)) => Environment -> RType -> Explorer s m RProgram  

generateI env t@(FunctionT x tArg tRes) = generateLambda
  where
    generateLambda = do
      pBody <- generateI (addVariable x tArg $ env) tRes
      return $ Program (PFun x pBody) t    
            
generateI env t@(ScalarT _ _ _) = guessE `mplus` generateMatch `mplus` generateIf
  where
    -- | Guess and check
    guessE = do
      (env', res) <- generateE env (shape t)
      addConstraint $ Subtype env' (typ res) t
      ifM (asks _incrementalSolving) (solveConstraints res) (return ())
      return res
      
    -- | Generate a match term of type @t@
    generateMatch = do
      d <- asks _matchDepth
      if d == 0
        then mzero
        else do
          scrDT <- msum (map return $ Map.keys (env ^. datatypes))                                         -- Pick a datatype to match on
          tArgs <- map vart_ `liftM` replicateM (((env ^. datatypes) Map.! scrDT) ^. typeArgCount) (freshId "_a")
          (env', pScrutinee) <- local (\params -> set eGuessDepth (view scrutineeDepth params) params) $ generateE env (ScalarT (DatatypeT scrDT) tArgs ())   -- Guess a scrutinee of the chosen shape
          guard (Set.null $ typeVarsOf (typ pScrutinee) `Set.difference` Set.fromList (env ^. boundTypeVars)) -- Reject scrutinees with free type variables
          
          x <- freshId "x"                                                                                                        -- Generate a fresh variable that will represent the scrutinee in the case environments
          pCases <- mapM (generateCase env' x (typ pScrutinee)) $ ((env ^. datatypes) Map.! scrDT) ^. constructors                -- Generate a case for each constructor of the datatype
          return $ Program (PMatch pScrutinee pCases) t
      
    -- | Generate the @consName@ case of a match term with scrutinee variable @scrName@ and scrutinee type @scrType@
    generateCase env scrName scrType consName = do
      case Map.lookup consName (allSymbols env) of
        Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env 
        Just consSch -> do
          consT <- toMonotype `liftM` freshTypeVars consSch          
          let u = fromJust $ unifier (env ^. boundTypeVars) scrType (lastType $ consT)
          let consT' = rTypeSubstitute u consT
          (args, caseEnv) <- addCaseSymbols env scrName scrType consT' -- Add bindings for constructor arguments and refine the scrutinee type in the environment
          pCaseExpr <- local (over matchDepth (-1 +)) $ generateI caseEnv t          
          return $ Case consName args pCaseExpr
          
    lastType t@(ScalarT _ _ _) = t
    lastType (FunctionT _ _ tRes) = lastType tRes
          
    -- | 'addCaseSymbols' @env x tX case@ : extension of @env@ that assumes that scrutinee @x@ of type @tX@.
    addCaseSymbols env x (ScalarT baseT _ fml) (ScalarT _ _ fml') = let subst = substitute (Map.singleton valueVarName (Var baseT x)) in 
      return $ ([], addAssumption (subst fml) . addNegAssumption (fnot $ subst fml') $ env) -- here vacuous cases are allowed
      -- return $ ([], addAssumption (subst fml) . addAssumption (subst fml') $ env) -- here disallowed unless no other choice
    addCaseSymbols env x tX (FunctionT y tArg tRes) = do
      argName <- freshId "y"
      (args, env') <- addCaseSymbols (addVariable argName tArg env) x tX (renameVar y argName tArg tRes)
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

  
-- | 'generateE' @env s@ : explore all elimination terms of type shape @s@ in environment @env@
-- (bottom-up phase of bidirectional typechecking)  
generateE :: (Monad s, MonadTrans m, MonadPlus (m s)) => Environment -> SType -> Explorer s m (Environment, RProgram)
generateE env s = generateVar `mplus` generateApp
  where
    -- | Explore all variables of shape @s@
    generateVar = do
      symbols <- symbolsUnifyingWith s env
      msum $ map genKnownSymbol $ Map.toList symbols
      
    instantiate (name, (typeSubst, sch)) = do
      let rhsSubst = Map.filterWithKey  (\a _ -> not $ Set.member a $ typeVarsOf s) typeSubst        
      rhsSubst' <- freshRefinementsSubst env rhsSubst
      return $ symbolType name $ rTypeSubstitute rhsSubst' (toMonotype sch)
                  
    genKnownSymbol (name, typeInfo) = do
      t <- instantiate (name, typeInfo)
      return (env, Program (PSymbol name) t)

    constraintForSymbol t name t' = Subtype env t' t
    
    symbolType x t@(ScalarT b args _)
      | Set.member x (env ^. constants) = t -- x is a constant, use it's type (it must be very precise)
      | otherwise                       = ScalarT b args (varRefinement x b) -- x is a scalar variable, use _v = x
    symbolType _ t = t    
    
    -- | Explore all applications of shape @s@ of an e-term to an i-term
    generateApp = do
      d <- asks _eGuessDepth
      let maxArity = fst $ Map.findMax (env ^. symbols)
      if d == 0 || arity s == maxArity
        then mzero 
        else do          
          a <- freshId "_a"
          (env', fun) <- generateE env (vart_ a |->| s) -- Find all functions that unify with (? -> s)
          let FunctionT _ tArg tRes = typ fun
          
          -- if isFunctionType tArg
            -- then do
              -- arg <- generateI env' tArg
              -- let u = fromJust $ unifier (env ^. boundTypeVars) (shape tArg) (shape $ typ arg)
              -- u' <- freshRefinementsSubst env' u
              -- let FunctionT x tArg' tRes' = rTypeSubstitute u' (typ fun)              
              -- return (env', Program (PApp fun arg) tRes')
            -- else do
          (env'', arg) <- local (over eGuessDepth (-1 +)) $ generateE env' (shape tArg)
          let u = fromJust $ unifier (env ^. boundTypeVars) (shape tArg) (shape $ typ arg)
          u' <- freshRefinementsSubst env'' u
          let FunctionT x tArg' tRes' = rTypeSubstitute u' (typ fun)
          addConstraint $ Subtype env'' (typ arg) tArg'
          ifM (asks _incrementalSolving) (solveConstraints arg) (return ())
          
          y <- freshId "g" 
          let env''' = addGhost y (typ arg) env''      
          return (env''', Program (PApp fun arg) (renameVar x y tArg tRes'))
      
    addGhost x t@(ScalarT baseT _ fml) env = -- addVariable x t env
      let subst = substitute (Map.singleton valueVarName (Var baseT x)) in addAssumption (subst fml) env
    addGhost _ (FunctionT _ _ _) env = env      
    
{- Constraint solving -}

-- | Solve all currently unsolved constraints
-- (program @p@ is only used for debug information)
solveConstraints :: (Monad s, MonadTrans m, MonadPlus (m s)) => RProgram -> Explorer s m ()
solveConstraints p = do
  solv <- asks _solver

  -- Convert new constraints into formulas and augment the current qualifier map with new unknowns
  cs <- use unsolvedConstraints
  let cs' = concatMap split cs  
  oldQuals <- use qualifierMap
  cq <- asks _condQualsGen
  tq <- asks _typeQualsGen
  let (clauses, newQuals) = toFormulas cq tq cs'
  newQuals' <- T.mapM (lift . lift . lift . csPruneQuals solv) newQuals
  let qmap = Map.union oldQuals newQuals'
  debug 1 (
    -- text "Liquid Program" $+$ programDoc (\typ -> option (not $ Set.null $ unknownsOfType typ) (pretty typ)) p
    text "Liquid Program" $+$ programDoc (const Synquid.Pretty.empty) p
    $+$ text "Typing Constraints" $+$ (vsep $ map pretty cs)
    ) $ return ()
  
  -- Refine the current candidate solutions using the new constraints; fail if no solution
  cands <- use candidates        
  cands' <- if null clauses then return cands else lift . lift .lift $ csRefine solv clauses qmap p cands
  guard (not $ null cands')
  
  -- Update state
  unsolvedConstraints .= []
  candidates .= cands'
  qualifierMap .= qmap    
      
-- | 'split' @c@ : split typing constraint @c@ that may contain function types into simple constraints (over only scalar types)
split :: Constraint -> [Constraint]
split (Subtype env (ScalarT baseT tArgs fml) (ScalarT baseT' tArgs' fml')) =
  (Subtype env (ScalarT baseT [] fml) (ScalarT baseT' [] fml')) : concatMap split (zipWith (Subtype env) tArgs tArgs') -- assuming covariance
split (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2)) = -- TODO: rename type vars
  split (Subtype env tArg2 tArg1) ++ split (Subtype (addVariable y tArg2 env) (renameVar x y tArg2 tRes1) tRes2)
split (WellFormed env (ScalarT baseT tArgs fml)) = 
  (WellFormed env (ScalarT baseT tArgs fml)) : concatMap (split . WellFormed env) tArgs
split (WellFormed env (FunctionT x tArg tRes)) = 
  split (WellFormed env tArg) ++ split (WellFormed (addVariable x tArg env) tRes)  
split c = [c]

toFormulas :: QualsGen -> QualsGen -> [Constraint] -> ([Formula], QMap)
toFormulas cq tq cs = execState (mapM_ (toFormula cq tq) cs) ([], Map.empty)

-- | 'toFormula' @cq tq c@ : translate simple typing constraint @c@ into either a logical constraint or an element of the search space,
-- given search space generators @cq@ and @tq@
toFormula :: QualsGen -> QualsGen -> Constraint -> State ([Formula], QMap) ()
toFormula _ _ (Subtype env (ScalarT baseT [] _) (ScalarT baseT' [] (BoolLit True))) | baseT == baseT' 
  = return ()
toFormula _ _ (Subtype env (ScalarT baseT [] fml) (ScalarT baseT' [] fml')) | baseT == baseT' 
  = let (poss, negs) = embedding env 
  in _1 %= ((conjunction (Set.insert fml poss) |=>| disjunction (Set.insert fml' negs)) :)
toFormula _ tq (WellFormed env (ScalarT baseT _ (Unknown _ u))) = 
  _2 %= Map.insert u (tq $ Var baseT valueVarName : allScalars env)
toFormula _ tq (WellFormed env (ScalarT baseT _ _)) = 
  return ()
toFormula cq _ (WellFormedCond env (Unknown _ u)) =
  _2 %= Map.insert u (cq $ allScalars env)
toFormula _ _ c = error $ show $ text "Not a simple constraint:" $+$ pretty c
    
{- Utility -}

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: (Monad s, MonadTrans m, MonadPlus (m s)) => String -> Explorer s m String
freshId prefix = do
  i <- use idCount
  idCount .= i + 1
  return $ prefix ++ show i
  
-- | 'freshRefinements @t@ : a type with the same shape and variables as @t@ but fresh unknowns as refinements
freshRefinements :: (Monad s, MonadTrans m, MonadPlus (m s)) => Environment -> RType -> Explorer s m RType
freshRefinements env t@(ScalarT (TypeVarT a) [] _)
  | not (a `elem` env ^. boundTypeVars) = return t
freshRefinements env (ScalarT base args _) = do
  k <- freshId "u"
  args' <- mapM (freshRefinements env) args
  return $ ScalarT base args' (Unknown Map.empty k)
freshRefinements env (FunctionT x tArg tFun) = do
  liftM3 FunctionT (freshId "x") (freshRefinements env tArg) (freshRefinements env tFun)

-- | 'unifier' @bvs t sch@ : most general unifier of a type @t@ and schema @sch@, 
-- where types variables @bvs@ can occur in @t@ but are bound in the context and thus cannot be substituted;
-- we assume that the free types variables of @t@ and @sch@ and bound variables of @sch@ are all pairwise disjoint;
unifier :: (Pretty (TypeSkeleton r), Eq r) => [Id] -> TypeSkeleton r -> TypeSkeleton r -> Maybe (TypeSubstitution r)
unifier bvs lhs rhs | lhs == rhs = Just $ Map.empty
unifier bvs lhs@(ScalarT (TypeVarT name) [] _) rhs
  | not $ name `elem` bvs = if Set.member name (typeVarsOf rhs) 
      then Nothing 
      -- error $ show $ text "unifier: free type variable" <+> text name <+> text "occurs on both sides:" <+> commaSep [pretty lhs, pretty rhs]
      else Just $ Map.singleton name rhs   -- Free type variable on the left      
unifier bvs lhs rhs@(ScalarT (TypeVarT name) [] _)
  | not $ name `elem` bvs = if Set.member name (typeVarsOf lhs) 
      then Nothing
      -- error $ show $ text "unifier: free type variable" <+> text name <+> text "occurs on both sides:" <+> commaSep [pretty lhs, pretty rhs]
      else Just $ Map.singleton name lhs   -- Free type variable on the right
unifier bvs lhs@(ScalarT baseL argsL _) rhs@(ScalarT baseR argsR _)
  | baseL == baseR = listUnifier bvs argsL argsR
unifier bvs (FunctionT _ argL resL) (FunctionT _ argR resR) = listUnifier bvs [argL, resL] [argR, resR]
unifier _ _ _ = Nothing

listUnifier _ [] [] = Just $ Map.empty
listUnifier bvs (lhs : lhss) (rhs : rhss) = do
  u <- unifier bvs lhs rhs
  u' <- listUnifier bvs (map (typeSubstitute id const u) lhss) (map (typeSubstitute id const u) rhss)
  return $ u `Map.union` u'
  
pair x y = (x, y)  

-- | 'symbolsUnifyingWith' @s env@ : symbols of simple type @s@ in @env@ 
symbolsUnifyingWith :: (Monad s, MonadTrans m, MonadPlus (m s)) => SType -> Environment -> Explorer s m (Map Id (TypeSubstitution (), RSchema))
symbolsUnifyingWith s env = (Map.map (over _1 fromJust) . Map.filter (isJust . fst) . Map.fromList) `liftM` mapM unify (Map.toList $ symbolsOfArity (arity s) env)
  where
    unify (name, sch) = (name, ) `liftM` do
      sch' <- freshTypeVars sch
      case Map.lookup name (env ^. shapeConstraints) of
        Nothing -> do -- No constraints on shape of sch': simply unify with s
          let res = unifier (env ^. boundTypeVars) s (shape $ toMonotype sch') 
          debug 1 (text "Unifier" <+> parens (commaSep [pretty s, pretty (polyShape sch')]) <+> text "->" <+> pretty res) $ return (res, sch')
        Just s' -> do -- The shape of sch' has to be s' (used in polymorphic recursion)
          let res = fromJust $ unifier (env ^. boundTypeVars) s' (shape $ toMonotype sch')
          case unifier (env ^. boundTypeVars) s' s of
            Nothing -> return (Nothing, sch')
            Just res' -> return (Just $ Map.union res res', sch')
    
-- | Replace all bound type variables with fresh identifiers    
freshTypeVars :: (Monad s, MonadTrans m, MonadPlus (m s)) => RSchema -> Explorer s m RSchema    
freshTypeVars sch = freshTypeVars' Map.empty sch
  where
    freshTypeVars' subst (Forall a sch) = do
      a' <- freshId "a"      
      (Forall a') `liftM` freshTypeVars' (Map.insert a (vartAll a') subst) sch
    freshTypeVars' subst (Monotype t) = return $ Monotype $ rTypeSubstitute subst t
  
freshRefinementsSubst env subst = do
  subst' <- T.mapM (freshRefinements env . refine) subst
  mapM_ (addConstraint . WellFormed env) (Map.elems subst')
  return subst'
