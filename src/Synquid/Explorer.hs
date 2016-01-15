{-# LANGUAGE TemplateHaskell, FlexibleContexts, TupleSections #-}

-- | Generating synthesis constraints from specifications, qualifiers, and program templates
module Synquid.Explorer where

import Synquid.Logic
import Synquid.Program
import Synquid.SolverMonad
import Synquid.TypeConstraintSolver hiding (freshId)
import qualified Synquid.TypeConstraintSolver as TCSolver (freshId)
import Synquid.Util
import Synquid.Pretty
import Synquid.Tokens

import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative hiding (empty)
import Control.Lens
import Debug.Trace

{- Interface -}

-- | Choices for the type of terminating fixpoint operator
data FixpointStrategy =
    DisableFixpoint   -- ^ Do not use fixpoint
  | FirstArgument     -- ^ Fixpoint decreases the first well-founded argument
  | AllArguments      -- ^ Fixpoint decreases the lexicographical tuple of all well-founded argument in declaration order

-- | Choices for the order of e-term enumeration
data PickSymbolStrategy = PickDepthFirst | PickInterleave

-- | Parameters of program exploration
data ExplorerParams = ExplorerParams {
  _eGuessDepth :: Int,                    -- ^ Maximum depth of application trees
  _scrutineeDepth :: Int,                 -- ^ Maximum depth of application trees inside match scrutinees
  _matchDepth :: Int,                     -- ^ Maximum nesting level of matches
  _fixStrategy :: FixpointStrategy,       -- ^ How to generate terminating fixpoints
  _polyRecursion :: Bool,                 -- ^ Enable polymorphic recursion?
  _hideScrutinees :: Bool,                -- ^ Should scrutinized variables be removed from the environment?
  _abduceScrutinees :: Bool,              -- ^ Should we match eagerly on all unfolded variables?
  _partialSolution :: Bool,                -- ^ Should implementations that only cover part of the input space be accepted?
  _incrementalChecking :: Bool,           -- ^ Solve subtyping constraints during the bottom-up phase
  _consistencyChecking :: Bool,           -- ^ Check consistency of function's type with the goal before exploring arguments?
  _context :: RProgram -> RProgram,       -- ^ Context in which subterm is currently being generated (used only for logging)
  _useMemoization :: Bool,                -- ^ Should we memoize enumerated terms (and corresponding environments)
  _explorerLogLevel :: Int                -- ^ How verbose logging is
} 

makeLenses ''ExplorerParams

-- | State of program exploration
data ExplorerState = ExplorerState {
  _typingState :: TypingState,    -- ^ Type-checking state
  _auxGoals :: [Goal],            -- ^ Subterms to be synthesized independently
  _symbolUseCount :: Map Id Int   -- ^ Number of times each symbol has been used in the program so far
} deriving (Eq, Ord)

makeLenses ''ExplorerState

-- | Key in the memoization store
data MemoKey = MemoKey {
  keyEnv :: Environment,
  keyTypeArity :: Int,
  keyLastShape :: SType,
  keyState :: ExplorerState,
  keyDepth :: Int
} deriving (Eq, Ord)

instance Pretty MemoKey where
  -- pretty (MemoKey env arity t d st) = pretty env <+> text "|-" <+> hsep (replicate arity (text "? ->")) <+> pretty t <+> text "AT" <+> pretty d
  pretty (MemoKey env arity t st d) = hsep (replicate arity (text "? ->")) <+> pretty t <+> text "AT" <+> pretty d <+> parens (pretty (st ^. typingState . candidates))

-- | Memoization store
type Memo = Map MemoKey [(Environment, RProgram, ExplorerState)]

-- | Computations that explore program space, parametrized by the the horn solver @s@
type Explorer s = StateT ExplorerState (ReaderT (ExplorerParams, TypingParams) (LogicT (StateT (Memo, [TypeError]) s)))

-- | 'runExplorer' @eParams tParams initTS go@ : execute exploration @go@ with explorer parameters @eParams@, typing parameters @tParams@ in typing state @initTS@
runExplorer :: MonadHorn s => ExplorerParams -> TypingParams -> TypingState -> Explorer s a -> s (Either TypeError a)
runExplorer eParams tParams initTS go = do
  (ress, (_, errs)) <- runStateT (observeManyT 1 $ runReaderT (evalStateT go (ExplorerState initTS [] Map.empty)) (eParams, tParams)) (Map.empty, [])
  case ress of
    [] -> return $ Left $ if null errs then text "No solution" else head errs
    (res : _) -> return $ Right res

-- | 'generateI' @env t@ : explore all terms that have refined type @t@ in environment @env@
-- (top-down phase of bidirectional typechecking)
generateI :: MonadHorn s => Environment -> RType -> Explorer s RProgram
generateI env t@(FunctionT x tArg tRes) = do
  x' <- if x == dontCare then freshId "x" else return x
  let ctx = \p -> Program (PFun x' p) t
  pBody <- inContext ctx $ generateI (unfoldAllVariables $ addVariable x' tArg $ env) tRes
  return $ ctx pBody
generateI env t@(ScalarT _ _) = ifM (asks $ _abduceScrutinees . fst)
                                    (generateMaybeMatchIf env t)
                                    (generateMaybeIf env t)
            

-- | Generate a possibly conditional term type @t@, depending on whether a condition is abduced
generateMaybeIf :: MonadHorn s => Environment -> RType -> Explorer s RProgram
generateMaybeIf env t = ifte generateThen generateElse (generateMatch env t) -- If at least one solution without a match exists, go with it and continue with the else branch; otherwise try to match
  where
    -- | Guess an E-term and abduce a condition for it
    generateThen = do
      cUnknown <- Unknown Map.empty <$> freshId "u"
      addConstraint $ WellFormedCond env cUnknown
      (_, pThen) <- cut $ generateE (addAssumption cUnknown env) t -- Do not backtrack: if we managed to find a soution for a nonempty subset of inputs, we go with it      
      cond <- conjunction <$> currentValuation cUnknown
      return (cond, pThen)

    -- | Proceed after solution @pThen@ has been found under assumption @cond@
    generateElse (cond, pThen) = if cond == ftrue
      then return pThen -- @pThen@ is valid under no assumptions: return it
      else do -- @pThen@ is valid under a nontrivial assumption, proceed to look for the solution for the rest of the inputs
        pCond <- generateCondition env cond        
        pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond pThen p) t) $ generateI (addAssumption (fnot cond) env) t
        return $ Program (PIf pCond pThen pElse) t
            
generateCondition env fml = do
  conjuncts <- mapM genConjunct allConjuncts
  return $ fmap (flip addRefinement $ valBool |=| fml) (foldl1 conjoin conjuncts)
  where
    allConjuncts = Set.toList $ conjunctsOf fml
    genConjunct c = if isExecutable c
                              then return $ fmlToProgram c
                              else snd <$> cut (generateE env (ScalarT BoolT $ valBool |=| c))
    andSymb = Program (PSymbol $ binOpTokens Map.! And) (toMonotype $ binOpType And)
    conjoin p1 p2 = Program (PApp (Program (PApp andSymb p1) boolAll) p2) boolAll
                
-- | If partial solutions are accepted, try @gen@, and if it fails, just leave a hole of type @t@; otherwise @gen@
optionalInPartial :: MonadHorn s => RType -> Explorer s RProgram -> Explorer s RProgram
optionalInPartial t gen = ifM (asks $ _partialSolution . fst) (ifte gen return (return $ Program PHole t)) gen
  
-- | Generate a match term of type @t@
generateMatch env t = do
  d <- asks $ _matchDepth . fst
  if d == 0
    then mzero
    else do
      (env', pScrutinee) <- local (over _1 (\params -> set eGuessDepth (view scrutineeDepth params) params))
                                  $ inContext (\p -> Program (PMatch p []) t)
                                  $ generateE env AnyT -- Generate a scrutinee of an arbitrary type

      scrType <- runInSolver $ currentAssignment (typeOf pScrutinee)
      case scrType of
        (ScalarT (DatatypeT scrDT _ _) _) -> do -- Type of the scrutinee is a datatype
          let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors

          let scrutineeSymbols = symbolList pScrutinee
          let isGoodScrutinee = not (null ctors) &&                                               -- Datatype is not abstract
                                (not $ pScrutinee `elem` (env ^. usedScrutinees)) &&              -- We only need this in case the hiding flag is off
                                (not $ head scrutineeSymbols `elem` ctors) &&                     -- Is not a value
                                (any (not . flip Set.member (env ^. constants)) scrutineeSymbols) -- Has variables (not just constants)
          guard isGoodScrutinee

          (env'', x) <- toVar pScrutinee (addScrutinee pScrutinee env')
          (pCase, cond) <- cut $ generateFirstCase env'' x pScrutinee t (head ctors)             -- First case generated separately in an attempt to abduce a condition for the whole match
          if cond == ftrue
            then do -- First case is valid unconditionally
              pCases <- mapM (cut . generateCase env'' x pScrutinee t) (tail ctors)              -- Generate a case for each of the remaining constructors
              return $ Program (PMatch pScrutinee (pCase : pCases)) t
            else do -- First case is valid under a condition
              pCases <- mapM (cut . generateCase (addAssumption cond env'') x pScrutinee t) (tail ctors)  -- Generate a case for each of the remaining constructors under the assumption
              let pThen = Program (PMatch pScrutinee (pCase : pCases)) t
              pCond <- generateCondition env cond
              pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond pThen p) t) $               -- Generate the else branch
                          generateI (addAssumption (fnot cond) env) t            
              return $ Program (PIf pCond pThen pElse) t

        _ -> mzero -- Type of the scrutinee is not a datatype: it cannot be used in a match
        
generateFirstCase env scrVar pScrutinee t consName = do
  case Map.lookup consName (allSymbols env) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env
    Just consSch -> do
      consT <- instantiate env consSch ftrue
      scrType <- runInSolver $ currentAssignment (typeOf pScrutinee)
      runInSolver $ matchConsType (lastType consT) scrType
      let ScalarT baseT _ = scrType
      let consT' = symbolType env consName consT
      binders <- replicateM (arity consT') (freshId "x")
      (syms, ass) <- caseSymbols scrVar binders consT'

      -- Try to find a vacuousness condition:
      deadUnknown <- Unknown Map.empty <$> freshId "u"
      solveLocally $ WellFormedMatchCond env deadUnknown      
      deadBranchCond <- runInSolver $ isEnvironmentInconsistent env (foldr (uncurry addVariable) (addAssumption ass emptyEnv) syms) deadUnknown
      case deadBranchCond of
        Nothing -> do
                    let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
                    pCaseExpr <- local (over (_1 . matchDepth) (-1 +)) 
                                  $ inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) t)
                                  $ generateI caseEnv t
                    return $ (Case consName binders pCaseExpr, ftrue)
        
        Just cond -> return $ (Case consName binders (Program (PSymbol "error") t), cond)

-- | Generate the @consName@ case of a match term with scrutinee variable @scrName@ and scrutinee type @scrType@
generateCase env scrVar pScrutinee t consName = do
  case Map.lookup consName (allSymbols env) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env
    Just consSch -> do
      consT <- instantiate env consSch ftrue
      scrType <- runInSolver $ currentAssignment (typeOf pScrutinee)
      runInSolver $ matchConsType (lastType consT) scrType
      let ScalarT baseT _ = scrType
      let consT' = symbolType env consName consT
      binders <- replicateM (arity consT') (freshId "x")
      (syms, ass) <- caseSymbols scrVar binders consT'
      let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
      pCaseExpr <- optionalInPartial t $ local (over (_1 . matchDepth) (-1 +))
                                       $ inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) t)
                                       $ generateI caseEnv t
      return $ Case consName binders pCaseExpr

caseSymbols x [] (ScalarT _ fml) = let subst = substitute (Map.singleton valueVarName x) in
  return ([], subst fml)
caseSymbols x (name : names) (FunctionT y tArg tRes) = do
  (syms, ass) <- caseSymbols x names (renameVar y name tArg tRes)
  return ((name, tArg) : syms, ass)  

-- | Generate a possibly conditinal possibly match term, depending on which conditions are abduced
generateMaybeMatchIf :: MonadHorn s => Environment -> RType -> Explorer s RProgram
generateMaybeMatchIf env t = ifte generateOneBranch generateOtherBranches (generateMatch env t)
  where
    -- | Guess an E-term and abduce a condition and a match-condition for it
    generateOneBranch = do
      matchUnknown <- Unknown Map.empty <$> freshId "u"
      addConstraint $ WellFormedMatchCond env matchUnknown
      condUnknown <- Unknown Map.empty <$> freshId "u"
      addConstraint $ WellFormedCond env condUnknown
      (matchConds, p0) <- cut $ do
        -- solveLocally $ WellFormedMatchCond env matchUnknown
        -- deadBranchCond <- runInSolver $ isEnvironmentInconsistent emptyEnv env matchUnknown
        -- (p0, matchValuation) <- case deadBranchCond of
                    -- Just cond -> return (Program (PSymbol "error") t, Set.toList $ conjunctsOf cond) 
                    -- Nothing -> do
                      -- (_, p0) <- generateE (addAssumption matchUnknown . addAssumption condUnknown $ env) t
                      -- matchValuation <- Set.toList <$> currentValuation matchUnknown
                      -- return (p0, matchValuation)                    
                      
        (_, p0) <- generateE (addAssumption matchUnknown . addAssumption condUnknown $ env) t
        matchValuation <- Set.toList <$> currentValuation matchUnknown        
        let allVars = Set.toList $ Set.unions (map varsOf matchValuation)
        let matchConds = map (conjunction . Set.fromList . (\var -> filter (Set.member var . varsOf) matchValuation)) allVars -- group by vars
        d <- asks $ _matchDepth . fst -- Backtrack if too many matches, maybe we can find a solution with fewer
        guard $ length matchConds <= d
        return (matchConds, p0)

      cond <- conjunction <$> currentValuation condUnknown
      return (matchConds, cond, p0)

    -- | Proceed after solution @p0@ has been found under assumption @cond@ and match-assumption @matchCond@
    generateOtherBranches (matchConds, cond, p0) = case matchConds of
      [] -> if cond == ftrue
        then return p0 -- @p0@ is valid under no assumptions: return it
        else do -- @p0@ is valid under a nontrivial assumption, but no need to match
              pCond <- generateCondition env cond
              pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond p0 p) t) $ generateI (addAssumption (fnot cond) env) t
              return $ Program (PIf pCond p0 pElse) t
      _ -> if cond == ftrue
        then generateMatchesFor env matchConds p0 t
        else do -- @p0@ needs both a match and a condition; let's put the match inside the conditional because it's easier
              pCond <- generateCondition env cond
              pThen <- cut $ generateMatchesFor (addAssumption cond env) matchConds p0 t
              pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond pThen p) t) $
                          generateI (addAssumption (fnot cond) env) t
              return $ Program (PIf pCond pThen pElse) t

    generateMatchesFor env [] pBaseCase t = return pBaseCase
    generateMatchesFor env (matchCond : rest) pBaseCase t = do
      let matchVar@(Var _ x) = Set.findMin $ varsOf matchCond
      let scrT@(ScalarT (DatatypeT scrDT _ _) _) = toMonotype $ symbolsOfArity 0 env Map.! x
      let pScrutinee = Program (PSymbol x) scrT
      let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors
      pBaseCase' <- cut $ inContext (\p -> Program (PMatch pScrutinee [Case (head ctors) [] p]) t) $
                            generateMatchesFor (addScrutinee pScrutinee . addAssumption matchCond $ env) rest pBaseCase t -- TODO: if matchCond contains only a subset of case conjuncts, we should add the rest
      generateKnownMatch env matchVar pBaseCase' t

    generateKnownMatch :: MonadHorn s => Environment -> Formula -> RProgram -> RType -> Explorer s RProgram
    generateKnownMatch env var@(Var s x) pBaseCase t = do
      let scrT@(ScalarT (DatatypeT scrDT _ _) _) = toMonotype $ symbolsOfArity 0 env Map.! x
      let pScrutinee = Program (PSymbol x) scrT
      let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors
      let env' = addScrutinee pScrutinee env
      pCases <- mapM (cut . generateCase env' var pScrutinee t) (tail ctors)              -- Generate a case for each constructor of the datatype
      return $ Program (PMatch pScrutinee (Case (head ctors) [] pBaseCase : pCases)) t

-- | 'generateE' @env typ@ : explore all elimination terms of type @typ@ in environment @env@
-- (bottom-up phase of bidirectional typechecking)
generateE :: MonadHorn s => Environment -> RType -> Explorer s (Environment, RProgram)
generateE env typ = do
  d <- asks $ _eGuessDepth . fst
  (finalEnv, p) <- generateEUpTo env typ d
  runInSolver solveTypeConstraints
  return (finalEnv, p)

-- | 'generateEUpTo' @env typ d@ : explore all applications of type shape @shape typ@ in environment @env@ of depth up to @d@
generateEUpTo :: MonadHorn s => Environment -> RType -> Int -> Explorer s (Environment, RProgram)
generateEUpTo env typ d = msum $ map (generateEAt env typ) [0..d]

-- | 'generateEAt' @env typ d@ : explore all applications of type shape @shape typ@ in environment @env@ of depth exactly to @d@
generateEAt :: MonadHorn s => Environment -> RType -> Int -> Explorer s (Environment, RProgram)
generateEAt _ _ d | d < 0 = mzero
generateEAt env typ d = do
  useMem <- asks $ (_useMemoization . fst)
  if not useMem || d == 0
    then do -- Do not use memoization
      (envFinal, p) <- enumerateAt env typ d
      checkE envFinal typ p
      return (envFinal, p)
    else do -- Try to fetch from memoization store
      startState <- get
      let tass = startState ^. typingState . typeAssignment
      let memoKey = MemoKey env (arity typ) (shape $ typeSubstitute tass (lastType typ)) startState d
      startMemo <- getMemo
      case Map.lookup memoKey startMemo of
        Just results -> do -- Found memoizaed results: fetch
          writeLog 3 (text "Fetching for:" <+> pretty memoKey $+$
                      text "Result:" $+$ vsep (map (\(env', p, _) -> pretty p) results))
          msum $ map applyMemoized results
        Nothing -> do -- Nothing found: enumerate and memoize
          writeLog 3 (text "Nothing found for:" <+> pretty memoKey)
          (envFinal, p) <- enumerateAt env typ d

          memo <- getMemo
          finalState <- get
          let memo' = Map.insertWith (flip (++)) memoKey [(envFinal, p, finalState)] memo
          writeLog 3 (text "Memoizing for:" <+> pretty memoKey <+> pretty p <+> text "::" <+> pretty (typeOf p))

          putMemo memo'

          checkE envFinal typ p
          return (envFinal, p)
  where
    applyMemoized (finalEnv, p, finalState) = do
      put finalState
      let env' = joinEnv env finalEnv
      checkE env' typ p
      return (env', p)

    joinEnv currentEnv memoEnv = over ghosts (Map.union (memoEnv ^. ghosts)) currentEnv

-- | Perform a gradual check that @p@ has type @typ@ in @env@:
-- if @p@ is a scalar, perform a full subtyping check;
-- if @p@ is a (partially applied) function, check as much as possible with unknown arguments
checkE :: MonadHorn s => Environment -> RType -> RProgram -> Explorer s ()
checkE env typ p = do
  ctx <- asks $ _context . fst
  writeLog 1 $ text "Checking" <+> pretty p <+> text "::" <+> pretty typ <+> text "in" $+$ pretty (ctx p)
                              
  if arity typ == 0
    then addConstraint $ Subtype env (typeOf p) typ False
    else do
      addConstraint $ Subtype env (removeDependentRefinements (Set.fromList $ allArgs $ typeOf p) (lastType (typeOf p))) (lastType typ) False
      ifM (asks $ _consistencyChecking . fst) (addConstraint $ Subtype env (typeOf p) typ True) (return ()) -- add constraint that t and tFun be consistent (i.e. not provably disjoint)
      
  fTyp <- runInSolver $ finalizeType typ
  typingState . errorContext .= errorText "when checking" </> pretty p </> text "::" </> pretty fTyp </> errorText "in" $+$ pretty (ctx p)
  solveIncrementally
  typingState . errorContext .= empty
  where
    removeDependentRefinements argNames (ScalarT (DatatypeT name typeArgs pArgs) fml) = 
      ScalarT (DatatypeT name (map (removeDependentRefinements argNames) typeArgs) (map (removeFrom argNames) pArgs)) (removeFrom argNames fml)
    removeDependentRefinements argNames (ScalarT baseT fml) = ScalarT baseT (removeFrom argNames fml)
    removeFrom argNames fml = if varsOf fml `disjoint` argNames then fml else ffalse

enumerateAt :: MonadHorn s => Environment -> RType -> Int -> Explorer s (Environment, RProgram)
enumerateAt env typ 0 = do
  -- case soleConstructor (lastType typ) of
    -- Just (name, sch) -> do -- @typ@ is a datatype with only on constructor, so all terms must start with that constructor
      -- guard $ arity (toMonotype sch) == arity typ
      -- pickSymbol (name, sch)

    -- Nothing -> do
      let symbols = Map.toList $ symbolsOfArity (arity typ) env
      useCounts <- use symbolUseCount
      let symbols' = if arity typ == 0
                        then sortBy (mappedCompare (\(x, _) -> (Set.member x (env ^. constants), Map.findWithDefault 0 x useCounts))) symbols
                        else sortBy (mappedCompare (\(x, _) -> (not $ Set.member x (env ^. constants), Map.findWithDefault 0 x useCounts))) symbols
      msum $ map pickSymbol symbols'
  where
    pickSymbol (name, sch) = do
      t <- freshInstance sch
      let p = Program (PSymbol name) (symbolType env name t)
      ifM (asks $ _hideScrutinees . fst) (guard $ not $ elem p (env ^. usedScrutinees)) (return ())
      writeLog 1 $ text "Trying" <+> pretty p
      symbolUseCount %= Map.insertWith (+) name 1      
      case Map.lookup name (env ^. shapeConstraints) of
        Nothing -> return ()
        Just sch -> solveLocally $ Subtype env (refineBot $ shape t) (refineTop sch) False      
      return (env, p)
      
    freshInstance sch = if arity (toMonotype sch) == 0
      then instantiate env sch ffalse -- This is a nullary constructor of a polymorphic type: it's safe to instantiate it with bottom refinements
      else instantiate env sch ftrue

    soleConstructor (ScalarT (DatatypeT name _ _) _) = let ctors = _constructors ((env ^. datatypes) Map.! name)
      in if length ctors == 1
          then Just (head ctors, allSymbols env Map.! (head ctors))
          else Nothing
    soleConstructor _ = Nothing
    
enumerateAt env typ d = do
  let maxArity = fst $ Map.findMax (env ^. symbols)
  guard $ arity typ < maxArity
  generateAllApps
  where
    generateAllApps =
      generateApp (\e t -> generateEUpTo e t (d - 1)) (\e t -> generateEAt e t (d - 1)) `mplus`
        generateApp (\e t -> generateEAt e t d) (\e t -> generateEUpTo e t (d - 1))

    generateApp genFun genArg = do
      x <- freshId "x"
      (env', fun) <- inContext (\p -> Program (PApp p (Program PHole AnyT)) typ)
                            $ genFun env (FunctionT x AnyT typ) -- Find all functions that unify with (? -> typ)
      let FunctionT x tArg tRes = typeOf fun

      (envfinal, pApp) <- if isFunctionType tArg
        then do -- Higher-order argument: its value is not required for the function type, return a placeholder and enqueue an auxiliary goal
          arg <- enqueueGoal env' tArg (untyped PHole)
          return (env', Program (PApp fun arg) tRes)
        else do -- First-order argument: generate now
          (env'', arg) <- local (over (_1 . eGuessDepth) (-1 +))
                            $ inContext (\p -> Program (PApp fun p) tRes)
                            $ genArg env' tArg
          (env''', y) <- toVar arg env''
          return (env''', Program (PApp fun arg) (renameVarFml x y tRes))
      ifM (asks $ _hideScrutinees . fst) (guard $ not $ elem pApp (env ^. usedScrutinees)) (return ())
      return (envfinal, pApp)

-- | 'toVar' @p env@: a variable representing @p@ (can be @p@ itself or a fresh ghost)
toVar (Program (PSymbol name) t) env 
  | not (isConstant name env)  = return (env, Var (toSort $ baseTypeOf t) name)
toVar (Program _ t) env = do
  g <- freshId "g"
  return (addGhost g t env, (Var (toSort $ baseTypeOf t) g))

enqueueGoal env typ impl = do
  g <- freshId "f"
  auxGoals %= ((Goal g env (Monotype typ) impl) :)
  return $ Program (PSymbol g) typ

{- Utility -}

-- | Get memoization store
getMemo :: MonadHorn s => Explorer s Memo
getMemo = lift . lift . lift $ use _1

-- | Set memoization store
putMemo :: MonadHorn s => Memo -> Explorer s ()
putMemo memo = lift . lift . lift $ _1 .= memo

-- | Record type error and backtrack
throwError :: MonadHorn s => TypeError -> Explorer s a  
throwError e = do
  writeLog 1 $ text "TYPE ERROR:" <+> plain e
  lift . lift . lift $ _2 %= (e :)
  mzero
  
-- | Impose typing constraint @c@ on the programs
addConstraint c = typingState %= addTypingConstraint c

-- | Embed a type-constraint checker computation @f@ in the explorer; on type error, record the error and backtrack
runInSolver :: MonadHorn s => TCSolver s a -> Explorer s a
runInSolver f = do
  tParams <- asks snd
  tState <- use typingState  
  res <- lift . lift . lift . lift $ runTCSolver tParams tState f
  case res of
    Left err -> throwError err
    Right (res, st) -> do
      typingState .= st
      return res
      
solveIncrementally :: MonadHorn s => Explorer s ()        
solveIncrementally = ifM (asks $ _incrementalChecking . fst) (runInSolver solveTypeConstraints) (return ())

solveLocally :: MonadHorn s => Constraint -> Explorer s ()  
solveLocally c = do
  writeLog 1 (text "Solving Locally" $+$ pretty c)
  oldTC <- use $ typingState . typingConstraints
  addConstraint c
  runInSolver solveTypeConstraints
  typingState . typingConstraints .= oldTC

freshId :: MonadHorn s => String -> Explorer s String
freshId = runInSolver . TCSolver.freshId

currentValuation :: MonadHorn s => Formula -> Explorer s (Set Formula)
currentValuation u = do
  results <- runInSolver $ currentValuations u
  msum $ map return results

inContext ctx f = local (over (_1 . context) (. ctx)) f
    
-- | Replace all type variables with fresh identifiers
instantiate :: MonadHorn s => Environment -> RSchema -> Formula -> Explorer s RType
instantiate env sch fml = do
  t <- instantiate' Map.empty Map.empty sch
  writeLog 2 (text "INSTANTIATE" <+> pretty sch $+$ text "INTO" <+> pretty t)
  return t
  where
    instantiate' subst pSubst (ForallT a sch) = do
      a' <- freshId "a"
      addConstraint $ WellFormed env (vart a' ftrue)
      instantiate' (Map.insert a (vart a' fml) subst) pSubst sch
    instantiate' subst pSubst (ForallP p argSorts sch) = do
      p' <- freshId "P"
      let argSorts' = map (sortSubstitute (asSortSubst subst)) argSorts
      addConstraint $ WellFormedPredicate env argSorts' p'
      instantiate' subst (Map.insert p (Pred BoolS p' (zipWith Var argSorts deBrujns)) pSubst) sch
    instantiate' subst pSubst (Monotype t) = go subst pSubst t
    go subst pSubst (FunctionT x tArg tRes) = do
      x' <- freshId "x"
      liftM2 (FunctionT x') (go subst pSubst tArg) (go subst pSubst (renameVar x x' tArg tRes))
    go subst pSubst t = return $ typeSubstitutePred pSubst . typeSubstitute subst $ t
  
symbolType env x (ScalarT b@(DatatypeT dtName _ _) fml)
  | x `elem` ((env ^. datatypes) Map.! dtName) ^. constructors = ScalarT b (fml |&| (Var (toSort b) valueVarName) |=| Cons (toSort b) x [])
symbolType env x t@(ScalarT b _)
  | isConstant x env = t -- x is a constant, use it's type (it must be very precise)
  | otherwise        = ScalarT b (varRefinement x (toSort b)) -- x is a scalar variable, use _v = x
symbolType env x t = case lastType t of
  (ScalarT b@(DatatypeT dtName _ _) fml) -> if x `elem` ((env ^. datatypes) Map.! dtName) ^. constructors
                                              then addRefinementToLast t ((Var (toSort b) valueVarName) |=| Cons (toSort b) x (allArgs t))
                                              else t
  _ -> t
  
-- | Perform an exploration, and once it succeeds, do not backtrack it  
cut :: MonadHorn s => Explorer s a -> Explorer s a
cut = once
-- cut e = do
  -- res <- once e
  -- typingState . candidates %= take 1 -- We also stick to the current valuations of unknowns
  -- return res

writeLog level msg = do
  maxLevel <- asks $ _explorerLogLevel . fst
  if level <= maxLevel then traceShow (plain msg) $ return () else return ()
