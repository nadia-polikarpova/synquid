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
  _auxDepth :: Int,                       -- ^ Maximum nesting level of auxiliary functions (lambdas used as arguments)
  _fixStrategy :: FixpointStrategy,       -- ^ How to generate terminating fixpoints
  _polyRecursion :: Bool,                 -- ^ Enable polymorphic recursion?
  _predPolyRecursion :: Bool,             -- ^ Enable recursion polymorphic in abstract predicates?
  _abduceScrutinees :: Bool,              -- ^ Should we match eagerly on all unfolded variables?
  _unfoldLocals :: Bool,                  -- ^ Unfold binders introduced by matching (to use them in match abduction)?
  _partialSolution :: Bool,               -- ^ Should implementations that only cover part of the input space be accepted?
  _incrementalChecking :: Bool,           -- ^ Solve subtyping constraints during the bottom-up phase
  _consistencyChecking :: Bool,           -- ^ Check consistency of function's type with the goal before exploring arguments?
  _context :: RProgram -> RProgram,       -- ^ Context in which subterm is currently being generated (used only for logging)
  _useMemoization :: Bool,                -- ^ Should enumerated terms be memoized?
  _symmetryReduction :: Bool,             -- ^ Should partial applications be memoized to check for redundancy?
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

data PartialKey = PartialKey {
    pKeyEnv :: Environment,
    pKeyType :: RType,
    pKeyState :: ExplorerState,
    pKeyMaxDepth :: Int
} deriving (Eq, Ord)

type PartialMemo = Map PartialKey [RType]
-- | Persistent state accross explorations
data PersistentState = PersistentState {
  _termMemo :: Memo,
  _partialFailures :: PartialMemo,
  _typeErrors :: [TypeError]
}

makeLenses ''PersistentState

-- | Computations that explore program space, parametrized by the the horn solver @s@
type Explorer s = StateT ExplorerState (ReaderT (ExplorerParams, TypingParams) (LogicT (StateT PersistentState s)))

-- | 'runExplorer' @eParams tParams initTS go@ : execute exploration @go@ with explorer parameters @eParams@, typing parameters @tParams@ in typing state @initTS@
runExplorer :: MonadHorn s => ExplorerParams -> TypingParams -> TypingState -> Explorer s a -> s (Either TypeError a)
runExplorer eParams tParams initTS go = do
  (ress, (PersistentState _ _ errs)) <- runStateT (observeManyT 1 $ runReaderT (evalStateT go (ExplorerState initTS [] Map.empty)) (eParams, tParams)) (PersistentState Map.empty Map.empty [])
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
generateI env t@(ScalarT _ _) = do
  maEnabled <- asks $ _abduceScrutinees . fst -- Is match abduction enabled?
  d <- asks $ _matchDepth . fst
  maPossible <- runInSolver $ hasPotentialScrutinees env -- Are there any potential scrutinees in scope?
  if maEnabled && d > 0 && maPossible then generateMaybeMatchIf env t else generateMaybeIf env t            

-- | Generate a possibly conditional term type @t@, depending on whether a condition is abduced
generateMaybeIf :: MonadHorn s => Environment -> RType -> Explorer s RProgram
generateMaybeIf env t = ifte generateThen (uncurry $ generateElse env t) (generateMatch env t) -- If at least one solution without a match exists, go with it and continue with the else branch; otherwise try to match
  where
    -- | Guess an E-term and abduce a condition for it
    generateThen = do
      cUnknown <- Unknown Map.empty <$> freshId "u"
      addConstraint $ WellFormedCond env cUnknown
      (_, pThen) <- cut $ generateE (addAssumption cUnknown env) t -- Do not backtrack: if we managed to find a solution for a nonempty subset of inputs, we go with it      
      cond <- conjunction <$> currentValuation cUnknown
      return (cond, pThen)

-- | Proceed after solution @pThen@ has been found under assumption @cond@
generateElse env t cond pThen = if cond == ftrue
  then return pThen -- @pThen@ is valid under no assumptions: return it
  else do -- @pThen@ is valid under a nontrivial assumption, proceed to look for the solution for the rest of the inputs
    pCond <- inContext (\p -> Program (PIf p uHole uHole) t) $ generateCondition env cond
    
    cUnknown <- Unknown Map.empty <$> freshId "u"
    runInSolver $ addFixedUnknown (unknownName cUnknown) (Set.singleton $ fnot cond) -- Create a fixed-valuation unknown to assume @!cond@
    pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond pThen p) t) $ generateI (addAssumption cUnknown env) t
    let conditional = Program (PIf pCond pThen pElse) t
    if isHole pElse
      then return conditional
      else ifte -- If synthesis of the else branch succeeded, try to remove the conditional
            (runInSolver $ setUnknownRecheck (unknownName cUnknown) Set.empty) -- Re-check subsumption constraints after retracting @!cond@
            (const $ return pElse)                                             -- constraints still hold: @pElse@ is a valid solution for both branches
            (return conditional)                                               -- constraints don't hold: the conditional is essential               
            
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

      case typeOf pScrutinee of
        (ScalarT (DatatypeT scrDT _ _) _) -> do -- Type of the scrutinee is a datatype
          let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors

          let scrutineeSymbols = symbolList pScrutinee
          let isGoodScrutinee = not (null ctors) &&                                               -- Datatype is not abstract
                                (not $ pScrutinee `elem` (env ^. usedScrutinees)) &&              -- Hasn't been scrutinized yet
                                (not $ head scrutineeSymbols `elem` ctors) &&                     -- Is not a value
                                (any (not . flip Set.member (env ^. constants)) scrutineeSymbols) -- Has variables (not just constants)
          guard isGoodScrutinee

          (env'', x) <- toVar pScrutinee (addScrutinee pScrutinee env')
          (pCase, cond) <- cut $ generateFirstCase env'' x pScrutinee t (head ctors)                  -- First case generated separately in an attempt to abduce a condition for the whole match
          pCases <- mapM (cut . generateCase (addAssumption cond env'') x pScrutinee t) (tail ctors)  -- Generate a case for each of the remaining constructors under the assumption
          let pThen = Program (PMatch pScrutinee (pCase : pCases)) t
          generateElse env t cond pThen                                                               -- Generate the else branch

        _ -> mzero -- Type of the scrutinee is not a datatype: it cannot be used in a match
        
generateFirstCase env scrVar pScrutinee t consName = do
  case Map.lookup consName (allSymbols env) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env
    Just consSch -> do
      consT <- instantiate env consSch True
      runInSolver $ matchConsType (lastType consT) (typeOf pScrutinee)
      consT' <- runInSolver $ currentAssignment consT
      binders <- replicateM (arity consT') (freshId "x")
      (syms, ass) <- caseSymbols scrVar binders consT'
      let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms

      ifte  (do -- Try to find a vacuousness condition:
              deadUnknown <- Unknown Map.empty <$> freshId "u"
              addConstraint $ WellFormedCond env deadUnknown
              err <- inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) t) $ generateError (addAssumption deadUnknown caseEnv)
              deadValuation <- currentValuation deadUnknown
              return (err, conjunction deadValuation)) 
            (\(err, deadCond) -> return $ (Case consName binders err, deadCond)) 
            (do
              pCaseExpr <- local (over (_1 . matchDepth) (-1 +)) 
                            $ inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) t)
                            $ generateI caseEnv t
              return $ (Case consName binders pCaseExpr, ftrue))

-- | Generate the @consName@ case of a match term with scrutinee variable @scrName@ and scrutinee type @scrType@
generateCase env scrVar pScrutinee t consName = do
  case Map.lookup consName (allSymbols env) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env
    Just consSch -> do
      consT <- instantiate env consSch True
      runInSolver $ matchConsType (lastType consT) (typeOf pScrutinee)
      consT' <- runInSolver $ currentAssignment consT
      binders <- replicateM (arity consT') (freshId "x")
      (syms, ass) <- caseSymbols scrVar binders consT'
      unfoldSyms <- asks $ _unfoldLocals . fst
      let caseEnv = (if unfoldSyms then unfoldAllVariables else id) $ foldr (uncurry addVariable) (addAssumption ass env) syms
      pCaseExpr <- optionalInPartial t $ local (over (_1 . matchDepth) (-1 +))
                                       $ inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) t)
                                       $ generateError caseEnv `mplus` generateI caseEnv t
      return $ Case consName binders pCaseExpr

caseSymbols x [] (ScalarT _ fml) = let subst = substitute (Map.singleton valueVarName x) in
  return ([], subst fml)
caseSymbols x (name : names) (FunctionT y tArg tRes) = do
  (syms, ass) <- caseSymbols x names (renameVar y name tArg tRes)
  return ((name, tArg) : syms, ass)  

-- | Generate a possibly conditional possibly match term, depending on which conditions are abduced
generateMaybeMatchIf :: MonadHorn s => Environment -> RType -> Explorer s RProgram
generateMaybeMatchIf env t = (generateOneBranch >>= generateOtherBranches) `mplus` (generateMatch env t) -- might need to backtrack a successful match due to match depth limitation
  where
    -- | Guess an E-term and abduce a condition and a match-condition for it
    generateOneBranch = do
      matchUnknown <- Unknown Map.empty <$> freshId "u"
      addConstraint $ WellFormedMatchCond env matchUnknown
      condUnknown <- Unknown Map.empty <$> freshId "u"
      addConstraint $ WellFormedCond env condUnknown
      cut $ do
        p0 <- generateEOrError (addAssumption matchUnknown . addAssumption condUnknown $ env) t
        matchValuation <- Set.toList <$> currentValuation matchUnknown
        let matchVars = Set.toList $ Set.unions (map varsOf matchValuation)
        condValuation <- currentValuation condUnknown
        let badError = isError p0 && length matchVars /= 1 -- null matchValuation && (not $ Set.null condValuation) -- Have we abduced a nontrivial vacuousness condition that is not a match branch?
        writeLog 2 $ text "Match valuation" <+> pretty matchValuation <+> if badError then text ": discarding error" else empty
        guard $ not badError -- Such vacuousness conditions are not productive (do not add to the environment assumptions and can be discovered over and over infinitely)        
        let matchConds = map (conjunction . Set.fromList . (\var -> filter (Set.member var . varsOf) matchValuation)) matchVars -- group by vars
        d <- asks $ _matchDepth . fst -- Backtrack if too many matches, maybe we can find a solution with fewer
        guard $ length matchConds <= d
        return (matchConds, conjunction condValuation, p0)
        
    generateEOrError env typ = generateError env `mplus` (snd <$> generateE env typ)

    -- | Proceed after solution @p0@ has been found under assumption @cond@ and match-assumption @matchCond@
    generateOtherBranches (matchConds, cond, p0) = do
      pThen <- cut $ generateMatchesFor (addAssumption cond env) matchConds p0 t
      generateElse env t cond pThen

    generateMatchesFor env [] pBaseCase t = return pBaseCase
    generateMatchesFor env (matchCond : rest) pBaseCase t = do
      let matchVar@(Var _ x) = Set.findMin $ varsOf matchCond
      let scrT@(ScalarT (DatatypeT scrDT _ _) _) = toMonotype $ symbolsOfArity 0 env Map.! x
      let pScrutinee = Program (PSymbol x) scrT
      let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors
      let env' = addScrutinee pScrutinee env
      pBaseCase' <- cut $ inContext (\p -> Program (PMatch pScrutinee [Case (head ctors) [] p]) t) $
                            generateMatchesFor (addAssumption matchCond env') rest pBaseCase t      
      pOtherCases <- mapM (cut . generateCase env' matchVar pScrutinee t) (tail ctors)
      return $ Program (PMatch pScrutinee (Case (head ctors) [] pBaseCase : pOtherCases)) t  


-- | 'generateE' @env typ@ : explore all elimination terms of type @typ@ in environment @env@
-- (bottom-up phase of bidirectional typechecking)
generateE :: MonadHorn s => Environment -> RType -> Explorer s (Environment, RProgram)
generateE env typ = do
  d <- asks $ _eGuessDepth . fst
  (finalEnv, Program pTerm pTyp) <- generateEUpTo env typ d
  pTyp' <- runInSolver $ solveTypeConstraints >> currentAssignment pTyp
  cleanupTypeVars
  return (finalEnv, Program pTerm pTyp')

-- | Forget free type variables, which cannot escape an E-term
-- (after substituting outstanding auxiliary goals)
cleanupTypeVars :: MonadHorn s => Explorer s ()  
cleanupTypeVars = do
  goals <- use auxGoals >>= mapM goalSubstituteTypes
  auxGoals .= goals
  runInSolver $ typeAssignment .= Map.empty
  where
    goalSubstituteTypes g = do
      spec' <- runInSolver $ currentAssignment (toMonotype $ gSpec g)
      return g { gSpec = Monotype spec' }
  
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
      checkE envFinal typ p (Just d)
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

          checkE envFinal typ p (Just d)
          return (envFinal, p)
  where
    applyMemoized (finalEnv, p, finalState) = do
      put finalState
      let env' = joinEnv env finalEnv
      checkE env' typ p (Just d)
      return (env', p)

    joinEnv currentEnv memoEnv = over ghosts (Map.union (memoEnv ^. ghosts)) currentEnv

-- | Perform a gradual check that @p@ has type @typ@ in @env@:
-- if @p@ is a scalar, perform a full subtyping check;
-- if @p@ is a (partially applied) function, check as much as possible with unknown arguments
checkE :: MonadHorn s => Environment -> RType -> RProgram -> Maybe Int -> Explorer s ()
checkE env typ p@(Program pTerm pTyp) md = do
  ctx <- asks $ _context . fst
  writeLog 1 $ text "Checking" <+> pretty p <+> text "::" <+> pretty typ <+> text "in" $+$ pretty (ctx p)
  
  ifM (asks $ _symmetryReduction . fst) checkSymmetry (return ())
  
  if arity typ == 0
    then addConstraint $ Subtype env pTyp typ False
    else do
      addConstraint $ Subtype env (removeDependentRefinements (Set.fromList $ allArgs pTyp) (lastType pTyp)) (lastType typ) False
      ifM (asks $ _consistencyChecking . fst) (addConstraint $ Subtype env pTyp typ True) (return ()) -- add constraint that t and tFun be consistent (i.e. not provably disjoint)
      
  fTyp <- runInSolver $ finalizeType typ
  typingState . errorContext .= errorText "when checking" </> pretty p </> text "::" </> pretty fTyp </> errorText "in" $+$ pretty (ctx p)  
  solveIncrementally
  typingState . errorContext .= empty
    where
      removeDependentRefinements argNames (ScalarT (DatatypeT name typeArgs pArgs) fml) = 
        ScalarT (DatatypeT name (map (removeDependentRefinements argNames) typeArgs) (map (removeFrom argNames) pArgs)) (removeFrom argNames fml)
      removeDependentRefinements argNames (ScalarT baseT fml) = ScalarT baseT (removeFrom argNames fml)
      removeFrom argNames fml = if varsOf fml `disjoint` argNames then fml else ffalse
      
      checkSymmetry = 
        case md of
          Just d -> do          
            startState <- get
            let partialKey = PartialKey env typ startState d
            startPartials <- getPartials
            let pastPartials = maybe [] id (Map.lookup partialKey startPartials)

            writeLog 1 $ text "Checking" <+> pretty pTyp <+> text "doesn't match any of" <+> pretty pastPartials <+> text "at depth" <+> pretty d

            -- Check that pTyp is not a subtype of any stored partial.
            if d > 0
              then mapM_ (\oldTyp -> ifte (solveLocally $ Subtype env pTyp oldTyp False)
                                        (\_ -> do
                                          writeLog 1 $ text "Subtype of failed predecessor:" <+> pretty pTyp <+> text "Is a subtype of" <+> pretty oldTyp
                                          mzero)
                                        (return ())) pastPartials
              else return ()

            let newPartials = pTyp : pastPartials
            let newPartialMap = Map.insert partialKey newPartials startPartials
            putPartials newPartialMap

          Nothing -> return ()

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
      writeLog 1 $ text "Trying" <+> pretty p
      symbolUseCount %= Map.insertWith (+) name 1      
      case Map.lookup name (env ^. shapeConstraints) of
        Nothing -> return ()
        Just sch -> solveLocally $ Subtype env (refineBot $ shape t) (refineTop sch) False      
      return (env, p)
      
    freshInstance sch = if arity (toMonotype sch) == 0
      then instantiate env sch False -- Nullary polymorphic function: it is safe to instantiate it with bottom refinements, since nothing can force the refinements to be weaker
      else instantiate env sch True

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
      (env', fun) <- inContext (\p -> Program (PApp p uHole) typ)
                            $ genFun env (FunctionT x AnyT typ) -- Find all functions that unify with (? -> typ)
      let FunctionT x tArg tRes = typeOf fun

      (envfinal, pApp) <- if isFunctionType tArg
        then do -- Higher-order argument: its value is not required for the function type, return a placeholder and enqueue an auxiliary goal
          d <- asks $ _auxDepth . fst
          when (d <= 0) $ writeLog 1 (text "Cannot synthesize higher-order argument: no auxiliary functions allowed") >> mzero
          arg <- enqueueGoal env' tArg (untyped PHole) (d - 1)
          return (env', Program (PApp fun arg) tRes)
        else do -- First-order argument: generate now
          (env'', arg) <- local (over (_1 . eGuessDepth) (-1 +))
                            $ inContext (\p -> Program (PApp fun p) tRes)
                            $ genArg env' tArg
          writeLog 2 (text "Synthesized argument" <+> pretty arg <+> text "of type" <+> pretty (typeOf arg))
          (env''', y) <- toVar arg env''
          return (env''', Program (PApp fun arg) (renameVarFml x y tRes))
      return (envfinal, pApp)
      
-- | Make environment inconsistent (if possible with current unknown assumptions)      
generateError :: MonadHorn s => Environment -> Explorer s RProgram
generateError env = do
  ctx <- asks $ _context . fst  
  writeLog 1 $ text "Checking" <+> pretty errorProgram <+> text "in" $+$ pretty (ctx errorProgram)
  tass <- use (typingState . typeAssignment)
  addConstraint $ Subtype env (int $ conjunction $ Set.fromList $ map trivial (allScalars env tass)) (int ffalse) False
  typingState . errorContext .= errorText "when checking" </> pretty errorProgram </> errorText "in" $+$ pretty (ctx errorProgram)
  runInSolver solveTypeConstraints
  typingState . errorContext .= empty
  return errorProgram
  where
    trivial var = var |=| var

-- | 'toVar' @p env@: a variable representing @p@ (can be @p@ itself or a fresh ghost)
toVar (Program (PSymbol name) t) env 
  | not (isConstant name env)  = return (env, Var (toSort $ baseTypeOf t) name)
toVar (Program _ t) env = do
  g <- freshId "g"
  return (addGhost g t env, (Var (toSort $ baseTypeOf t) g))

enqueueGoal _ typ (Program (PSymbol f) _) depth = do -- Known goal, must have been defined before with a let
 goalsByName <- uses auxGoals (filter (\g -> gName g == f))
 if null goalsByName
  then throwError $ errorText "Not in scope: function" </> squotes (text f)
  else do
    let goal@(Goal _ env _ impl _) = head goalsByName
    auxGoals %= ((Goal f env (Monotype typ) impl depth) :) . delete goal
    return $ Program (PSymbol f) typ  
enqueueGoal env typ impl depth = do
  g <- freshId "f"
  -- env' <- (set boundTypeVars (env ^. boundTypeVars ) . set boundPredicates (env ^. boundPredicates )) <$> runInSolver (use initEnv)
  auxGoals %= ((Goal g env (Monotype typ) impl depth) :)
  return $ Program (PSymbol g) typ

{- Utility -}

-- | Get memoization store
getMemo :: MonadHorn s => Explorer s Memo
getMemo = lift . lift . lift $ use termMemo

-- | Set memoization store
putMemo :: MonadHorn s => Memo -> Explorer s ()
putMemo memo = lift . lift . lift $ termMemo .= memo

getPartials :: MonadHorn s => Explorer s PartialMemo
getPartials = lift . lift . lift $ use partialFailures

putPartials :: MonadHorn s => PartialMemo -> Explorer s ()
putPartials partials = lift . lift . lift $ partialFailures .= partials

-- | Record type error and backtrack
throwError :: MonadHorn s => TypeError -> Explorer s a  
throwError e = do
  writeLog 1 $ text "TYPE ERROR:" <+> plain e
  lift . lift . lift $ typeErrors %= (e :)
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
solveIncrementally = ifM (asks $ _incrementalChecking . fst) (runInSolver $ isFinal .= False >> solveTypeConstraints >> isFinal .= True) (return ())

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
  msum $ map pickCandidiate (zip [0..] results)
  where
    pickCandidiate (i, res)  = do
      typingState . candidates %= take 1 . drop i
      return res

inContext ctx f = local (over (_1 . context) (. ctx)) f
    
-- | Replace all bound type and predicate variables with fresh free variables
-- (if @top@ is @False@, instantiate with bottom refinements instead of top refinements)
instantiate :: MonadHorn s => Environment -> RSchema -> Bool -> Explorer s RType
instantiate env sch top = do
  t <- instantiate' Map.empty Map.empty sch
  writeLog 2 (text "INSTANTIATE" <+> pretty sch $+$ text "INTO" <+> pretty t)
  return t
  where
    instantiate' subst pSubst (ForallT a sch) = do
      a' <- freshId "a"
      addConstraint $ WellFormed env (vart a' ftrue)
      instantiate' (Map.insert a (vart a' (BoolLit top)) subst) pSubst sch
    instantiate' subst pSubst (ForallP p argSorts sch) = do
      let argSorts' = map (sortSubstitute (asSortSubst subst)) argSorts
      fml <- if top
              then do
                p' <- freshId "P"
                addConstraint $ WellFormedPredicate env argSorts' p'
                return $ Pred BoolS p' (zipWith Var argSorts' deBrujns)
              else return ffalse
      instantiate' subst (Map.insert p fml pSubst) sch        
    instantiate' subst pSubst (Monotype t) = go subst pSubst t
    go subst pSubst (FunctionT x tArg tRes) = do
      x' <- freshId "x"
      liftM2 (FunctionT x') (go subst pSubst tArg) (go subst pSubst (renameVar x x' tArg tRes))
    go subst pSubst t = return $ typeSubstitutePred pSubst . typeSubstitute subst $ t  
    
symbolType env x t@(ScalarT b _)
  | isConstant x env = t -- x is a constant, use it's type (it must be very precise)
  | otherwise        = ScalarT b (varRefinement x (toSort b)) -- x is a scalar variable, use _v = x
symbolType _ _ t = t
  
-- | Perform an exploration, and once it succeeds, do not backtrack it  
cut :: MonadHorn s => Explorer s a -> Explorer s a
cut = once

writeLog level msg = do
  maxLevel <- asks $ _explorerLogLevel . fst
  if level <= maxLevel then traceShow (plain msg) $ return () else return ()
