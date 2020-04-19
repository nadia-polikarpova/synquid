{-# LANGUAGE TemplateHaskell, FlexibleContexts, TupleSections #-}

-- | Generating synthesis constraints from specifications, qualifiers, and program templates
module Synquid.Explorer where

import Synquid.Logic
import Synquid.Type hiding (set)
import Synquid.Program
import Synquid.Error
import Synquid.SolverMonad
import Synquid.TypeConstraintSolver hiding (freshId, freshVar)
import qualified Synquid.TypeConstraintSolver as TCSolver (freshId, freshVar)
import Synquid.Util
import Synquid.Pretty
import Synquid.Tokens

import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Char
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
  | Nonterminating    -- ^ Fixpoint without termination check

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
  _splitMeasures :: Bool,                 -- ^ Split subtyping constraints between datatypes into constraints over each measure
  _context :: RProgram -> RProgram,       -- ^ Context in which subterm is currently being generated (used only for logging and symmetry reduction)
  _useMemoization :: Bool,                -- ^ Should enumerated terms be memoized?
  _symmetryReduction :: Bool,             -- ^ Should partial applications be memoized to check for redundancy?
  _sourcePos :: SourcePos,                -- ^ Source position of the current goal
  _explorerLogLevel :: Int                -- ^ How verbose logging is
}

makeLenses ''ExplorerParams

type Requirements = Map Id [RType]

-- | State of program exploration
data ExplorerState = ExplorerState {
  _typingState :: TypingState,                     -- ^ Type-checking state
  _auxGoals :: [Goal],                             -- ^ Subterms to be synthesized independently
  _solvedAuxGoals :: Map Id RProgram,              -- Synthesized auxiliary goals, to be inserted into the main program
  _lambdaLets :: Map Id (Environment, UProgram),   -- ^ Local bindings to be checked upon use (in type checking mode)
  _requiredTypes :: Requirements,                  -- ^ All types that a variable is required to comply to (in repair mode)
  _symbolUseCount :: Map Id Int                    -- ^ Number of times each symbol has been used in the program so far
} deriving (Eq, Ord)

makeLenses ''ExplorerState

-- | Key in the memoization store
data MemoKey = MemoKey {
  keyTypeArity :: Int,
  keyLastShape :: SType,
  keyState :: ExplorerState,
  keyDepth :: Int
} deriving (Eq, Ord)
instance Pretty MemoKey where
  -- pretty (MemoKey arity t d st) = pretty env <+> text "|-" <+> hsep (replicate arity (text "? ->")) <+> pretty t <+> text "AT" <+> pretty d
  pretty (MemoKey arity t st d) = hsep (replicate arity (text "? ->")) <+> pretty t <+> text "AT" <+> pretty d <+> parens (pretty (st ^. typingState . candidates))

-- | Memoization store
type Memo = Map MemoKey [(RProgram, ExplorerState)]

newtype PartialKey = PartialKey { pKeyContext :: RProgram } deriving (Eq, Ord)

type PartialMemo = Map PartialKey (Map RProgram (Int, Environment))
-- | Persistent state accross explorations
data PersistentState = PersistentState {
  _termMemo :: Memo,
  _partialFailures :: PartialMemo,
  _typeErrors :: [ErrorMessage]
}

makeLenses ''PersistentState

-- | Computations that explore program space, parametrized by the the horn solver @s@
type Explorer s = StateT ExplorerState (
                    ReaderT (ExplorerParams, TypingParams, Reconstructor s) (
                    LogicT (StateT PersistentState s)))

-- | This type encapsulates the 'reconstructTopLevel' function of the type checker,
-- which the explorer calls for auxiliary goals
data Reconstructor s = Reconstructor (Goal -> Explorer s RProgram)

-- | 'runExplorer' @eParams tParams initTS go@ : execute exploration @go@ with explorer parameters @eParams@, typing parameters @tParams@ in typing state @initTS@
runExplorer :: MonadHorn s => ExplorerParams -> TypingParams -> Reconstructor s -> TypingState -> Explorer s a -> s (Either ErrorMessage a)
runExplorer eParams tParams topLevel initTS go = do
  (ress, (PersistentState _ _ errs)) <- runStateT (observeManyT 1 $ runReaderT (evalStateT go initExplorerState) (eParams, tParams, topLevel)) (PersistentState Map.empty Map.empty [])
  case ress of
    [] -> 
      case errs of 
        [] -> return $ Left impossible
        (e:_) -> return $ Left e
    (res : _) -> return $ Right res
  where
    initExplorerState = ExplorerState initTS [] Map.empty Map.empty Map.empty Map.empty
    impossible = ErrorMessage {
        emKind = SynthesisError,
        emPosition = _sourcePos eParams,
        emDescription = text "Synthesis goal is impossible: components or search parameters are insufficient."
      }

-- | 'generateI' @env t@ : explore all terms that have refined type @t@ in environment @env@
-- (top-down phase of bidirectional typechecking)
generateI :: MonadHorn s => Environment -> RType -> Explorer s RProgram
generateI env t@(FunctionT x tArg tRes) = do
  let ctx = \p -> Program (PFun x p) t
  pBody <- inContext ctx $ generateI (unfoldAllVariables $ addVariable x tArg $ env) tRes
  return $ ctx pBody
generateI env t@(ScalarT _ _) = do
  maEnabled <- asks . view $ _1 . abduceScrutinees -- Is match abduction enabled?
  d <- asks . view $ _1 . matchDepth
  maPossible <- runInSolver $ hasPotentialScrutinees env -- Are there any potential scrutinees in scope?
  if maEnabled && d > 0 && maPossible then generateMaybeMatchIf env t else generateMaybeIf env t

-- | Generate a possibly conditional term type @t@, depending on whether a condition is abduced
generateMaybeIf :: MonadHorn s => Environment -> RType -> Explorer s RProgram
generateMaybeIf env t = ifte generateThen (uncurry3 $ generateElse env t) (generateMatch env t) -- If at least one solution without a match exists, go with it and continue with the else branch; otherwise try to match
  where
    -- | Guess an E-term and abduce a condition for it
    generateThen = do
      cUnknown <- Unknown Map.empty <$> freshId "C"
      addConstraint $ WellFormedCond env cUnknown
      pThen <- cut $ generateE (addAssumption cUnknown env) t -- Do not backtrack: if we managed to find a solution for a nonempty subset of inputs, we go with it
      cond <- conjunction <$> currentValuation cUnknown
      return (cond, unknownName cUnknown, pThen)

-- | Proceed after solution @pThen@ has been found under assumption @cond@
generateElse env t cond condUnknown pThen = if cond == ftrue
  then return pThen -- @pThen@ is valid under no assumptions: return it
  else do -- @pThen@ is valid under a nontrivial assumption, proceed to look for the solution for the rest of the inputs
    pCond <- inContext (\p -> Program (PIf p uHole uHole) t) $ generateCondition env cond

    cUnknown <- Unknown Map.empty <$> freshId "C"
    runInSolver $ addFixedUnknown (unknownName cUnknown) (Set.singleton $ fnot cond) -- Create a fixed-valuation unknown to assume @!cond@
    pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond pThen p) t) $ generateI (addAssumption cUnknown env) t
    ifM (tryEliminateBranching pElse (runInSolver $ setUnknownRecheck (unknownName cUnknown) Set.empty (Set.singleton condUnknown)))
      (return pElse)
      (return $ Program (PIf pCond pThen pElse) t)

tryEliminateBranching branch recheck =
  if isHole branch
      then return False
      else ifte -- If synthesis of the branch succeeded, try to remove the branching construct
            recheck -- Re-check Horn constraints after retracting the branch guard
            (const $ return True) -- constraints still hold: @branch@ is a valid solution overall
            (return False) -- constraints don't hold: the guard is essential

generateCondition env fml = do
  conjuncts <- mapM genConjunct allConjuncts
  return $ fmap (flip addRefinement $ valBool |=| fml) (foldl1 conjoin conjuncts)
  where
    allConjuncts = Set.toList $ conjunctsOf fml
    genConjunct c = if isExecutable c
                              then return $ fmlToProgram c
                              else cut (generateE env (ScalarT BoolT $ valBool |=| c))
    andSymb = Program (PSymbol $ binOpTokens Map.! And) (toMonotype $ binOpType And)
    conjoin p1 p2 = Program (PApp (Program (PApp andSymb p1) boolAll) p2) boolAll

-- | If partial solutions are accepted, try @gen@, and if it fails, just leave a hole of type @t@; otherwise @gen@
optionalInPartial :: MonadHorn s => RType -> Explorer s RProgram -> Explorer s RProgram
optionalInPartial t gen = ifM (asks . view $ _1 . partialSolution) (ifte gen return (return $ Program PHole t)) gen

-- | Generate a match term of type @t@
generateMatch env t = do
  d <- asks . view $ _1 . matchDepth
  if d == 0
    then mzero
    else do
      (Program p tScr) <- local (over _1 (\params -> set eGuessDepth (view scrutineeDepth params) params))
                      $ inContext (\p -> Program (PMatch p []) t)
                      $ generateE env anyDatatype -- Generate a scrutinee of an arbitrary type
      let (env', tScr') = embedContext env tScr
      let pScrutinee = Program p tScr'

      case tScr of
        (ScalarT (DatatypeT scrDT _ _) _) -> do -- Type of the scrutinee is a datatype
          let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors

          let scrutineeSymbols = symbolList pScrutinee
          let isGoodScrutinee = not (null ctors) &&                                               -- Datatype is not abstract
                                (not $ pScrutinee `elem` (env ^. usedScrutinees)) &&              -- Hasn't been scrutinized yet
                                (not $ head scrutineeSymbols `elem` ctors) &&                     -- Is not a value
                                (any (not . flip Set.member (env ^. constants)) scrutineeSymbols) -- Has variables (not just constants)
          guard isGoodScrutinee

          (env'', x) <- toVar (addScrutinee pScrutinee env') pScrutinee
          (pCase, cond, condUnknown) <- cut $ generateFirstCase env'' x pScrutinee t (head ctors)                  -- First case generated separately in an attempt to abduce a condition for the whole match
          pCases <- map fst <$> mapM (cut . generateCase (addAssumption cond env'') x pScrutinee t) (tail ctors)  -- Generate a case for each of the remaining constructors under the assumption
          let pThen = Program (PMatch pScrutinee (pCase : pCases)) t
          generateElse env t cond condUnknown pThen                                                               -- Generate the else branch

        _ -> mzero -- Type of the scrutinee is not a datatype: it cannot be used in a match

generateFirstCase env scrVar pScrutinee t consName = do
  case Map.lookup consName (allSymbols env) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env
    Just consSch -> do
      consT <- instantiate env consSch True []
      runInSolver $ matchConsType (lastType consT) (typeOf pScrutinee)
      consT' <- runInSolver $ currentAssignment consT
      binders <- replicateM (arity consT') (freshVar env "x")
      (syms, ass) <- caseSymbols env scrVar binders consT'
      let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms

      ifte  (do -- Try to find a vacuousness condition:
              deadUnknown <- Unknown Map.empty <$> freshId "C"
              addConstraint $ WellFormedCond env deadUnknown
              err <- inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) t) $ generateError (addAssumption deadUnknown caseEnv)
              deadValuation <- conjunction <$> currentValuation deadUnknown
              ifte (generateError (addAssumption deadValuation env)) (const mzero) (return ()) -- The error must be possible only in this case
              return (err, deadValuation, unknownName deadUnknown))
            (\(err, deadCond, deadUnknown) -> return $ (Case consName binders err, deadCond, deadUnknown))
            (do
              pCaseExpr <- local (over (_1 . matchDepth) (-1 +))
                            $ inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) t)
                            $ generateI caseEnv t
              return $ (Case consName binders pCaseExpr, ftrue, dontCare))

-- | Generate the @consName@ case of a match term with scrutinee variable @scrName@ and scrutinee type @scrType@
generateCase :: MonadHorn s => Environment -> Formula -> RProgram -> RType -> Id -> Explorer s (Case RType, Explorer s ())
generateCase env scrVar pScrutinee t consName = do
  case Map.lookup consName (allSymbols env) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env
    Just consSch -> do
      consT <- instantiate env consSch True []
      runInSolver $ matchConsType (lastType consT) (typeOf pScrutinee)
      consT' <- runInSolver $ currentAssignment consT
      binders <- replicateM (arity consT') (freshVar env "x")
      (syms, ass) <- caseSymbols env scrVar binders consT'
      unfoldSyms <- asks . view $ _1 . unfoldLocals

      cUnknown <- Unknown Map.empty <$> freshId "M"
      runInSolver $ addFixedUnknown (unknownName cUnknown) (Set.singleton ass) -- Create a fixed-valuation unknown to assume @ass@

      let caseEnv = (if unfoldSyms then unfoldAllVariables else id) $ foldr (uncurry addVariable) (addAssumption cUnknown env) syms
      pCaseExpr <- optionalInPartial t $ local (over (_1 . matchDepth) (-1 +))
                                       $ inContext (\p -> Program (PMatch pScrutinee [Case consName binders p]) t)
                                       $ generateError caseEnv `mplus` generateI caseEnv t

      let recheck = if disjoint (symbolsOf pCaseExpr) (Set.fromList binders)
                      then runInSolver $ setUnknownRecheck (unknownName cUnknown) Set.empty Set.empty -- ToDo: provide duals here
                      else mzero

      return (Case consName binders pCaseExpr, recheck)

-- | 'caseSymbols' @scrutinee binders consT@: a pair that contains (1) a list of bindings of @binders@ to argument types of @consT@
-- and (2) a formula that is the return type of @consT@ applied to @scrutinee@
caseSymbols env x [] (ScalarT _ fml) = let subst = substitute (Map.singleton valueVarName x) in
  return ([], subst fml)
caseSymbols env x (name : names) (FunctionT y tArg tRes) = do
  (syms, ass) <- caseSymbols env x names (renameVar (isBound env) y name tArg tRes)
  return ((name, tArg) : syms, ass)

-- | Generate a possibly conditional possibly match term, depending on which conditions are abduced
generateMaybeMatchIf :: MonadHorn s => Environment -> RType -> Explorer s RProgram
generateMaybeMatchIf env t = (generateOneBranch >>= generateOtherBranches) `mplus` (generateMatch env t) -- might need to backtrack a successful match due to match depth limitation
  where
    -- | Guess an E-term and abduce a condition and a match-condition for it
    generateOneBranch = do
      matchUnknown <- Unknown Map.empty <$> freshId "M"
      addConstraint $ WellFormedMatchCond env matchUnknown
      condUnknown <- Unknown Map.empty <$> freshId "C"
      addConstraint $ WellFormedCond env condUnknown
      cut $ do
        p0 <- generateEOrError (addAssumption matchUnknown . addAssumption condUnknown $ env) t
        matchValuation <- Set.toList <$> currentValuation matchUnknown
        let matchVars = Set.toList $ Set.unions (map varsOf matchValuation)
        condValuation <- currentValuation condUnknown
        let badError = isError p0 && length matchVars /= 1 -- null matchValuation && (not $ Set.null condValuation) -- Have we abduced a nontrivial vacuousness condition that is not a match branch?
        writeLog 3 $ text "Match valuation" <+> pretty matchValuation <+> if badError then text ": discarding error" else empty
        guard $ not badError -- Such vacuousness conditions are not productive (do not add to the environment assumptions and can be discovered over and over infinitely)
        let matchConds = map (conjunction . Set.fromList . (\var -> filter (Set.member var . varsOf) matchValuation)) matchVars -- group by vars
        d <- asks . view $ _1 . matchDepth -- Backtrack if too many matches, maybe we can find a solution with fewer
        guard $ length matchConds <= d
        return (matchConds, conjunction condValuation, unknownName condUnknown, p0)

    generateEOrError env typ = generateError env `mplus` generateE env typ

    -- | Proceed after solution @p0@ has been found under assumption @cond@ and match-assumption @matchCond@
    generateOtherBranches (matchConds, cond, condUnknown, p0) = do
      pThen <- cut $ generateMatchesFor (addAssumption cond env) matchConds p0 t
      generateElse env t cond condUnknown pThen

    generateMatchesFor env [] pBaseCase t = return pBaseCase
    generateMatchesFor env (matchCond : rest) pBaseCase t = do
      let (Binary Eq matchVar@(Var _ x) (Cons _ c _)) = matchCond
      scrT <- runInSolver $ currentAssignment (toMonotype $ symbolsOfArity 0 env Map.! x)
      let (ScalarT (DatatypeT scrDT _ _) _) = scrT
      let pScrutinee = Program (PSymbol x) scrT
      let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors
      let env' = addScrutinee pScrutinee env
      pBaseCase' <- cut $ inContext (\p -> Program (PMatch pScrutinee [Case c [] p]) t) $
                            generateMatchesFor (addAssumption matchCond env') rest pBaseCase t

      let genOtherCases previousCases ctors =
            case ctors of
              [] -> return $ Program (PMatch pScrutinee previousCases) t
              (ctor:rest) -> do
                (c, recheck) <- cut $ generateCase env' matchVar pScrutinee t ctor
                ifM (tryEliminateBranching (expr c) recheck)
                  (return $ expr c)
                  (genOtherCases (previousCases ++ [c]) rest)

      genOtherCases [Case c [] pBaseCase] (delete c ctors)

-- | 'generateE' @env typ@ : explore all elimination terms of type @typ@ in environment @env@
-- (bottom-up phase of bidirectional typechecking)
generateE :: MonadHorn s => Environment -> RType -> Explorer s RProgram
generateE env typ = do
  putMemo Map.empty                                     -- Starting E-term enumeration in a new environment: clear memoization store
  d <- asks . view $ _1 . eGuessDepth
  (Program pTerm pTyp) <- generateEUpTo env typ d                            -- Generate the E-term
  runInSolver $ isFinal .= True >> solveTypeConstraints >> isFinal .= False  -- Final type checking pass that eliminates all free type variables
  newGoals <- uses auxGoals (map gName)                                      -- Remember unsolved auxiliary goals
  generateAuxGoals                                                           -- Solve auxiliary goals
  pTyp' <- runInSolver $ currentAssignment pTyp                              -- Finalize the type of the synthesized term
  addLambdaLets pTyp' (Program pTerm pTyp') newGoals                         -- Check if some of the auxiliary goal solutions are large and have to be lifted into lambda-lets
  where
    addLambdaLets t body [] = return body
    addLambdaLets t body (g:gs) = do
      pAux <- uses solvedAuxGoals (Map.! g)
      if programNodeCount pAux > 5
        then addLambdaLets t (Program (PLet g uHole body) t) gs
        else addLambdaLets t body gs

-- | 'generateEUpTo' @env typ d@ : explore all applications of type shape @shape typ@ in environment @env@ of depth up to @d@
generateEUpTo :: MonadHorn s => Environment -> RType -> Int -> Explorer s RProgram
generateEUpTo env typ d = msum $ map (generateEAt env typ) [0..d]

-- | 'generateEAt' @env typ d@ : explore all applications of type shape @shape typ@ in environment @env@ of depth exactly to @d@
generateEAt :: MonadHorn s => Environment -> RType -> Int -> Explorer s RProgram
generateEAt _ _ d | d < 0 = mzero
generateEAt env typ d = do
  useMem <- asks . view $ _1 . useMemoization
  if not useMem || d == 0
    then do -- Do not use memoization
      p <- enumerateAt env typ d
      checkE env typ p
      return p
    else do -- Try to fetch from memoization store
      startState <- get
      let tass = startState ^. typingState . typeAssignment
      let memoKey = MemoKey (arity typ) (shape $ typeSubstitute tass (lastType typ)) startState d
      startMemo <- getMemo
      case Map.lookup memoKey startMemo of
        Just results -> do -- Found memoized results: fetch
          writeLog 3 (text "Fetching for:" <+> pretty memoKey $+$
                      text "Result:" $+$ vsep (map (\(p, _) -> pretty p) results))
          msum $ map applyMemoized results
        Nothing -> do -- Nothing found: enumerate and memoize
          writeLog 3 (text "Nothing found for:" <+> pretty memoKey)
          p <- enumerateAt env typ d

          memo <- getMemo
          finalState <- get
          let memo' = Map.insertWith (flip (++)) memoKey [(p, finalState)] memo
          writeLog 3 (text "Memoizing for:" <+> pretty memoKey <+> pretty p <+> text "::" <+> pretty (typeOf p))

          putMemo memo'

          checkE env typ p
          return p
  where
    applyMemoized (p, finalState) = do
      put finalState
      checkE env typ p
      return p

-- | Perform a gradual check that @p@ has type @typ@ in @env@:
-- if @p@ is a scalar, perform a full subtyping check;
-- if @p@ is a (partially applied) function, check as much as possible with unknown arguments
checkE :: MonadHorn s => Environment -> RType -> RProgram -> Explorer s ()
checkE env typ p@(Program pTerm pTyp) = do
  ctx <- asks . view $ _1 . context
  writeLog 2 $ text "Checking" <+> pretty p <+> text "::" <+> pretty typ <+> text "in" $+$ pretty (ctx (untyped PHole))

  -- ifM (asks $ _symmetryReduction . fst) checkSymmetry (return ())

  incremental <- asks . view $ _1 . incrementalChecking -- Is incremental type checking of E-terms enabled?
  consistency <- asks . view $ _1 . consistencyChecking -- Is consistency checking enabled?

  when (incremental || arity typ == 0) (addConstraint $ Subtype env pTyp typ False "") -- Add subtyping check, unless it's a function type and incremental checking is diasbled
  when (consistency && arity typ > 0) (addConstraint $ Subtype env pTyp typ True "") -- Add consistency constraint for function types
  fTyp <- runInSolver $ finalizeType typ
  pos <- asks . view $ _1 . sourcePos
  typingState . errorContext .= (pos, text "when checking" </> pretty p </> text "::" </> pretty fTyp </> text "in" $+$ pretty (ctx p))
  runInSolver solveTypeConstraints
  typingState . errorContext .= (noPos, empty)

enumerateAt :: MonadHorn s => Environment -> RType -> Int -> Explorer s RProgram
enumerateAt env typ 0 = do
    let symbols = Map.toList $ symbolsOfArity (arity typ) env
    useCounts <- use symbolUseCount
    let symbols' = filter (\(x, _) -> notElem x setConstructors) $ if arity typ == 0
                      then sortBy (mappedCompare (\(x, _) -> (Set.member x (env ^. constants), Map.findWithDefault 0 x useCounts))) symbols
                      else sortBy (mappedCompare (\(x, _) -> (not $ Set.member x (env ^. constants), Map.findWithDefault 0 x useCounts))) symbols
    msum $ map pickSymbol symbols'
  where
    pickSymbol (name, sch) = do
      when (Set.member name (env ^. letBound)) mzero
      t <- symbolType env name sch
      let p = Program (PSymbol name) t
      writeLog 2 $ text "Trying" <+> pretty p
      symbolUseCount %= Map.insertWith (+) name 1
      case Map.lookup name (env ^. shapeConstraints) of
        Nothing -> return ()
        Just sc -> addConstraint $ Subtype env (refineBot env $ shape t) (refineTop env sc) False ""
      return p

enumerateAt env typ d = do
  let maxArity = fst $ Map.findMax (env ^. symbols)
  guard $ arity typ < maxArity
  generateAllApps
  where
    generateAllApps =
      generateApp (\e t -> generateEUpTo e t (d - 1)) (\e t -> generateEAt e t (d - 1)) `mplus`
        generateApp (\e t -> generateEAt e t d) (\e t -> generateEUpTo e t (d - 1))

    generateApp genFun genArg = do
      x <- freshId "X"
      fun <- inContext (\p -> Program (PApp p uHole) typ)
                $ genFun env (FunctionT x AnyT typ) -- Find all functions that unify with (? -> typ)
      let FunctionT x tArg tRes = typeOf fun

      pApp <- if isFunctionType tArg
        then do -- Higher-order argument: its value is not required for the function type, return a placeholder and enqueue an auxiliary goal
          d <- asks . view $ _1 . auxDepth
          when (d <= 0) $ writeLog 2 (text "Cannot synthesize higher-order argument: no auxiliary functions allowed") >> mzero
          arg <- enqueueGoal env tArg (untyped PHole) (d - 1)
          return $ Program (PApp fun arg) tRes
        else do -- First-order argument: generate now
          let mbCut = id -- if Set.member x (varsOfType tRes) then id else cut
          arg <- local (over (_1 . eGuessDepth) (-1 +))
                    $ inContext (\p -> Program (PApp fun p) tRes)
                    $ mbCut (genArg env tArg)
          writeLog 3 (text "Synthesized argument" <+> pretty arg <+> text "of type" <+> pretty (typeOf arg))
          let tRes' = appType env arg x tRes
          return $ Program (PApp fun arg) tRes'
      return pApp

-- | Make environment inconsistent (if possible with current unknown assumptions)
generateError :: MonadHorn s => Environment -> Explorer s RProgram
generateError env = do
  ctx <- asks . view $ _1. context
  writeLog 2 $ text "Checking" <+> pretty (show errorProgram) <+> text "in" $+$ pretty (ctx errorProgram)
  tass <- use (typingState . typeAssignment)
  let env' = typeSubstituteEnv tass env
  addConstraint $ Subtype env (int $ conjunction $ Set.fromList $ map trivial (allScalars env')) (int ffalse) False ""
  pos <- asks . view $ _1 . sourcePos
  typingState . errorContext .= (pos, text "when checking" </> pretty errorProgram </> text "in" $+$ pretty (ctx errorProgram))
  runInSolver solveTypeConstraints
  typingState . errorContext .= (noPos, empty)
  return errorProgram
  where
    trivial var = var |=| var

-- | 'toVar' @p env@: a variable representing @p@ (can be @p@ itself or a fresh ghost)
toVar :: MonadHorn s => Environment -> RProgram -> Explorer s (Environment, Formula)
toVar env (Program (PSymbol name) t) = return (env, symbolAsFormula env name t)
toVar env (Program _ t) = do
  g <- freshId "G"
  return (addLetBound g t env, (Var (toSort $ baseTypeOf t) g))

-- | 'appType' @env p x tRes@: a type semantically equivalent to [p/x]tRes;
-- if @p@ is not a variable, instead of a literal substitution use the contextual type LET x : (typeOf p) IN tRes
appType :: Environment -> RProgram -> Id -> RType -> RType
appType env (Program (PSymbol name) t) x tRes = substituteInType (isBound env) (Map.singleton x $ symbolAsFormula env name t) tRes
appType env (Program _ t) x tRes = contextual x t tRes

isPolyConstructor (Program (PSymbol name) t) = isTypeName name && (not . Set.null . typeVarsOf $ t)

enqueueGoal env typ impl depth = do
  g <- freshVar env "f"
  auxGoals %= ((Goal g env (Monotype typ) impl depth noPos True) :)
  return $ Program (PSymbol g) typ

{- Utility -}

-- | Get memoization store
getMemo :: MonadHorn s => Explorer s Memo
getMemo = lift . lift . lift $ use termMemo

-- | Set memoization store
putMemo :: MonadHorn s => Memo -> Explorer s ()
putMemo memo = lift . lift . lift $ termMemo .= memo

-- getPartials :: MonadHorn s => Explorer s PartialMemo
-- getPartials = lift . lift . lift $ use partialFailures

-- putPartials :: MonadHorn s => PartialMemo -> Explorer s ()
-- putPartials partials = lift . lift . lift $ partialFailures .= partials

throwErrorWithDescription :: MonadHorn s => Doc -> Explorer s a
throwErrorWithDescription msg = do
  pos <- asks . view $ _1 . sourcePos
  throwError $ ErrorMessage TypeError pos msg

-- | Record type error and backtrack
throwError :: MonadHorn s => ErrorMessage -> Explorer s a
throwError e = do
  writeLog 2 $ text "TYPE ERROR:" <+> plain (emDescription e)
  lift . lift . lift $ typeErrors %= (e :)
  mzero

-- | Impose typing constraint @c@ on the programs
addConstraint c = typingState %= addTypingConstraint c

-- | Embed a type-constraint checker computation @f@ in the explorer; on type error, record the error and backtrack
runInSolver :: MonadHorn s => TCSolver s a -> Explorer s a
runInSolver f = do
  tParams <- asks . view $ _2
  tState <- use typingState
  res <- lift . lift . lift . lift $ runTCSolver tParams tState f
  case res of
    Left err -> throwError err
    Right (res, st) -> do
      typingState .= st
      return res

freshId :: MonadHorn s => String -> Explorer s String
freshId = runInSolver . TCSolver.freshId

freshVar :: MonadHorn s => Environment -> String -> Explorer s String
freshVar env prefix = runInSolver $ TCSolver.freshVar env prefix

-- | Return the current valuation of @u@;
-- in case there are multiple solutions,
-- order them from weakest to strongest in terms of valuation of @u@ and split the computation
currentValuation :: MonadHorn s => Formula -> Explorer s Valuation
currentValuation u = do
  runInSolver $ solveAllCandidates
  cands <- use (typingState . candidates)
  let candGroups = groupBy (\c1 c2 -> val c1 == val c2) $ sortBy (\c1 c2 -> setCompare (val c1) (val c2)) cands
  msum $ map pickCandidiate candGroups
  where
    val c = valuation (solution c) u
    pickCandidiate cands' = do
      typingState . candidates .= cands'
      return $ val (head cands')

inContext ctx f = local (over (_1 . context) (. ctx)) f

-- | Replace all bound type and predicate variables with fresh free variables
-- (if @top@ is @False@, instantiate with bottom refinements instead of top refinements)
instantiate :: MonadHorn s => Environment -> RSchema -> Bool -> [Id] -> Explorer s RType
instantiate env sch top argNames = do
  t <- instantiate' Map.empty Map.empty sch
  writeLog 3 (text "INSTANTIATE" <+> pretty sch $+$ text "INTO" <+> pretty t)
  return t
  where
    instantiate' subst pSubst (ForallT a sch) = do
      a' <- freshId "A"
      addConstraint $ WellFormed env (vart a' ftrue)
      instantiate' (Map.insert a (vart a' (BoolLit top)) subst) pSubst sch
    instantiate' subst pSubst (ForallP (PredSig p argSorts _) sch) = do
      let argSorts' = map (sortSubstitute (asSortSubst subst)) argSorts
      fml <- if top
              then do
                p' <- freshId (map toUpper p)
                addConstraint $ WellFormedPredicate env argSorts' p'
                return $ Pred BoolS p' (zipWith Var argSorts' deBrujns)
              else return ffalse
      instantiate' subst (Map.insert p fml pSubst) sch
    instantiate' subst pSubst (Monotype t) = go subst pSubst argNames t
    go subst pSubst argNames (FunctionT x tArg tRes) = do
      x' <- case argNames of
              [] -> freshVar env "x"
              (argName : _) -> return argName
      liftM2 (FunctionT x') (go subst pSubst [] tArg) (go subst pSubst (drop 1 argNames) (renameVar (isBoundTV subst) x x' tArg tRes))
    go subst pSubst _ t = return $ typeSubstitutePred pSubst . typeSubstitute subst $ t
    isBoundTV subst a = (a `Map.member` subst) || (a `elem` (env ^. boundTypeVars))

-- | 'symbolType' @env x sch@: precise type of symbol @x@, which has a schema @sch@ in environment @env@;
-- if @x@ is a scalar variable, use "_v == x" as refinement;
-- if @sch@ is a polytype, return a fresh instance
symbolType :: MonadHorn s => Environment -> Id -> RSchema -> Explorer s RType
symbolType env x (Monotype t@(ScalarT b _))
    | isLiteral x = return t -- x is a literal of a primitive type, it's type is precise
    | isJust (lookupConstructor x env) = return t -- x is a constructor, it's type is precise
    | otherwise = return $ ScalarT b (varRefinement x (toSort b)) -- x is a scalar variable or monomorphic scalar constant, use _v = x
symbolType env _ sch = freshInstance sch
  where
    freshInstance sch = if arity (toMonotype sch) == 0
      then instantiate env sch False [] -- Nullary polymorphic function: it is safe to instantiate it with bottom refinements, since nothing can force the refinements to be weaker
      else instantiate env sch True []

-- | Perform an exploration, and once it succeeds, do not backtrack it
cut :: MonadHorn s => Explorer s a -> Explorer s a
cut = once

-- | Synthesize auxiliary goals accumulated in @auxGoals@ and store the result in @solvedAuxGoals@
generateAuxGoals :: MonadHorn s => Explorer s ()
generateAuxGoals = do
  goals <- use auxGoals
  writeLog 3 $ text "Auxiliary goals are:" $+$ vsep (map pretty goals)
  case goals of
    [] -> return ()
    (g : gs) -> do
        auxGoals .= gs
        writeLog 2 $ text "PICK AUXILIARY GOAL" <+> pretty g
        Reconstructor reconstructTopLevel <- asks . view $ _3
        p <- reconstructTopLevel g
        solvedAuxGoals %= Map.insert (gName g) (etaContract p)
        generateAuxGoals
  where
    etaContract p = case etaContract' [] (content p) of
                      Nothing -> p
                      Just f -> Program f (typeOf p)
    etaContract' [] (PFix _ p)                                               = etaContract' [] (content p)
    etaContract' binders (PFun x p)                                          = etaContract' (x:binders) (content p)
    etaContract' (x:binders) (PApp pFun (Program (PSymbol y) _)) | x == y    =  etaContract' binders (content pFun)
    etaContract' [] f@(PSymbol _)                                            = Just f
    etaContract' binders p                                                   = Nothing

writeLog level msg = do
  maxLevel <- asks . view $ _1 . explorerLogLevel
  if level <= maxLevel then traceShow (plain msg) $ return () else return ()
