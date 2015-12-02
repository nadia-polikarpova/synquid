{-# LANGUAGE TemplateHaskell, FlexibleContexts, TupleSections #-}

-- | Generating synthesis constraints from specifications, qualifiers, and program templates
module Synquid.Explorer where

import Synquid.Logic
import Synquid.Program
import Synquid.Util
import Synquid.Pretty
import Synquid.SMTSolver()
import Data.Maybe
import Data.Either()
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Traversable as T
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Control.Lens
import Control.Monad.Trans.Maybe
import Debug.Trace

{- Interface -}

-- | State space generator (returns a state space for a list of symbols in scope)
type QualsGen = (Environment, [Formula]) -> QSpace

-- | Empty state space generator
emptyGen = const emptyQSpace

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
  _condDepth :: Int,                      -- ^ Maximum nesting level of conditionals
  _fixStrategy :: FixpointStrategy,       -- ^ How to generate terminating fixpoints
  _polyRecursion :: Bool,                 -- ^ Enable polymorphic recursion?
  _hideScrutinees :: Bool,
  _abduceScrutinees :: Bool,              -- ^ Should we match eagerly on all unfolded variables?
  _incrementalChecking :: Bool,           -- ^ Solve subtyping constraints during the bottom-up phase
  _consistencyChecking :: Bool,           -- ^ Check consistency of fucntion's type with the goal before exploring arguments?
  _condQualsGen :: QualsGen,              -- ^ Qualifier generator for conditionals
  _matchQualsGen :: QualsGen,
  _typeQualsGen :: QualsGen,              -- ^ Qualifier generator for types
  _context :: RProgram -> RProgram,       -- ^ Context in which subterm is currently being generated (used only for logging)
  _explorerLogLevel :: Int,               -- ^ How verbose logging is
  _useMemoization :: Bool                 -- ^ Should we memoize enumerated terms (and corresponding environments)
}

makeLenses ''ExplorerParams

-- | State of program exploration
data ExplorerState = ExplorerState {
  _idCount :: Map String Int,                   -- ^ Number of unique identifiers issued so far
  _typingConstraints :: [Constraint],           -- ^ Typing constraints yet to be converted to horn clauses
  _qualifierMap :: QMap,                        -- ^ State spaces for all the unknowns generated from well-formedness constraints
  _hornClauses :: [Formula],                    -- ^ Horn clauses generated from subtyping constraints since the last liquid assignment refinement
  _consistencyChecks :: [Formula],              -- ^ Consistency clauses generated from incomplete subtyping constraints since the last liquid assignment refinement
  _typeAssignment :: TypeSubstitution,          -- ^ Current assignment to free type variables
  _predAssignment :: Substitution,              -- ^ Current assignment to free predicate variables
  _candidates :: [Candidate],                   -- ^ Current set of candidate liquid assignments to unknowns
  _auxGoals :: [Goal],                          -- ^ Subterms to be synthesized independently
  _initEnv :: Environment,
  _symbolUseCount :: Map Id Int                 -- ^ Number of times each symbol has been used in the program so far
}

makeLenses ''ExplorerState

instance Eq ExplorerState where
  (==) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (_idCount st1) == restrictDomain (Set.fromList ["a", "u"]) (_idCount st2)) &&
                  -- _typingConstraints st1 == _typingConstraints st2 &&
                  -- _qualifierMap st1 == _qualifierMap st2 &&
                  -- _hornClauses st1 == _hornClauses st2 &&
                  -- _consistencyChecks st1 == _consistencyChecks st2 &&
                  _typeAssignment st1 == _typeAssignment st2 &&
                  _candidates st1 == _candidates st2
                  -- _auxGoals st1 == _auxGoals st2

instance Ord ExplorerState where
  (<=) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (_idCount st1) <= restrictDomain (Set.fromList ["a", "u"]) (_idCount st2)) &&
                -- _typingConstraints st1 <= _typingConstraints st2 &&
                -- _qualifierMap st1 <= _qualifierMap st2 &&
                -- _hornClauses st1 <= _hornClauses st2 &&
                -- _consistencyChecks st1 <= _consistencyChecks st2 &&
                _typeAssignment st1 <= _typeAssignment st2 &&
                _candidates st1 <= _candidates st2
                -- _auxGoals st1 <= _auxGoals st2

instance Pretty ExplorerState where
  pretty st = hMapDoc pretty pretty $ _idCount st

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
  pretty (MemoKey env arity t st d) = hsep (replicate arity (text "? ->")) <+> pretty t <+> text "AT" <+> pretty d <+> parens (pretty (_candidates st))

-- | Memoization store
type Memo = Map MemoKey [(Environment, RProgram, ExplorerState)]

-- | Incremental second-order constraint solver
data ConstraintSolver s = ConstraintSolver {
  csInit :: s Candidate,                                                      -- ^ Initial candidate solution
  csRefine :: [Formula] -> QMap -> ExtractAssumptions -> RProgram -> [Candidate] -> s [Candidate],  -- ^ Refine current list of candidates to satisfy new constraints
  csPruneQuals :: QSpace -> s QSpace,                                         -- ^ Prune redundant qualifiers
  csCheckConsistency :: [Formula] -> [Candidate] -> s [Candidate],            -- ^ Check consistency of formulas under candidates
  csClearMemo :: s (),                                                        -- ^ Clear the memoization store
  csGetMemo :: s Memo,                                                        -- ^ Retrieve the memoization store
  csPutMemo :: Memo -> s()                                                    -- ^ Store the momization store
}

-- | Impose typing constraint @c@ on the programs
addConstraint c = typingConstraints %= (c :)
addTypeAssignment tv t = typeAssignment %= Map.insert tv t
addPredAssignment p fml = predAssignment %= Map.insert p fml
addHornClause fml = hornClauses %= (fml :)
addConsistencyCheck fml = consistencyChecks %= (fml :)

-- | Computations that explore programs, parametrized by the the constraint solver and the backtracking monad
type Explorer s = StateT ExplorerState (ReaderT (ExplorerParams, ConstraintSolver s) (LogicT s))

-- | 'explore' @params env typ@ : explore all programs that have type @typ@ in the environment @env@;
-- exploration is driven by @params@
explore :: Monad s => ExplorerParams -> ConstraintSolver s -> Goal -> s [RProgram]
explore params solver goal = observeManyT 1 $ do
    initCand <- lift $ csInit solver
    runReaderT (evalStateT go (ExplorerState Map.empty [] Map.empty [] [] Map.empty Map.empty [initCand] [] (gEnvironment goal) Map.empty)) (params, solver)
  where
    go = do
      pMain <- generateTopLevel goal
      pAuxs <- generateAuxGoals
      tass <- use typeAssignment
      sol <- uses candidates (solution . head)
      let resMain = (programApplySolution sol . programSubstituteTypes tass) pMain 
      let resAuxs = map (over _2 (programApplySolution sol . programSubstituteTypes tass)) pAuxs
      return (Program (PLet resAuxs resMain) (typeOf resMain))

    generateAuxGoals = do
      goals <- use auxGoals
      case goals of
        [] -> return []
        (g : gs) -> do
          auxGoals .= gs
          let g' = g { gEnvironment = removeVariable (gName goal) (gEnvironment g) } -- remove recursive calls of the main goal
          writeLog 1 $ text "AUXILIARY GOAL" <+> pretty g'          
          p <- generateTopLevel g'
          rest <- generateAuxGoals
          return $ (gName g, p) : rest

{- AST exploration -}

-- | 'generateTopLevel' @env t@ : explore all terms that have refined type schema @sch@ in environment @env@
generateTopLevel :: Monad s => Goal -> Explorer s RProgram
generateTopLevel (Goal funName env (ForallT a sch)) = generateTopLevel (Goal funName (addTypeVar a env) sch)
generateTopLevel (Goal funName env (ForallP pName pSorts sch)) = generateTopLevel (Goal funName (addPredicate pName pSorts env) sch)
generateTopLevel (Goal funName env (Monotype t@(FunctionT _ _ _))) = generateFix
  where
    generateFix = do    
      recCalls <- recursiveCalls t
      polymorphic <- asks $ _polyRecursion . fst
      let tvs = env ^. boundTypeVars
      let env' = if polymorphic && not (null tvs)
                    then foldr (\(f, t') -> addPolyVariable f (foldr ForallT (Monotype t') tvs) . (shapeConstraints %~ Map.insert f (shape t))) env recCalls -- polymorphic recursion enabled: generalize on all bound variables
                    else foldr (\(f, t') -> addVariable f t') env recCalls  -- do not generalize
      let ctx = \p -> if null recCalls then p else Program (PFix (map fst recCalls) p) t
      p <- local (over (_1 . context) (. ctx)) $ generateI env' t
      return $ ctx p

    -- | 'recursiveCalls' @t@: name-type pairs for recursive calls to a function with type @t@ (0 or 1)
    recursiveCalls t = do
      fixStrategy <- asks $ _fixStrategy . fst
      recType <- case fixStrategy of
        AllArguments -> fst <$> recursiveTypeTuple t ffalse
        FirstArgument -> recursiveTypeFirst t
        DisableFixpoint -> return t
      if recType == t
        then return []
        else return $ [(funName, recType)]

    -- | 'recursiveTypeTuple' @t fml@: type of the recursive call to a function of type @t@ when a lexicographic tuple of all recursible arguments decreases;
    -- @fml@ denotes the disjunction @x1' < x1 || ... || xk' < xk@ of strict termination conditions on all previously seen recursible arguments to be added to the type of the last recursible argument;
    -- the function returns a tuple of the weakend type @t@ and a flag that indicates if the last recursible argument has already been encountered and modified
    recursiveTypeTuple (FunctionT x tArg tRes) fml = do
      case terminationRefinement x tArg of
        Nothing -> do
          (tRes', seenLast) <- recursiveTypeTuple tRes fml
          return (FunctionT x tArg tRes', seenLast)
        Just (argLt, argLe) -> do
          y <- freshId "x"
          let yForVal = Map.singleton valueVarName (Var (toSort $ baseTypeOf tArg) y)
          (tRes', seenLast) <- recursiveTypeTuple (renameVar x y tArg tRes) (fml `orClean` substitute yForVal argLt)
          if seenLast
            then return (FunctionT y (addRefinement tArg argLe) tRes', True) -- already encountered the last recursible argument: add a nonstrict termination refinement to the current one
            -- else return (FunctionT y (addRefinement tArg (fml `orClean` argLt)) tRes', True) -- this is the last recursible argument: add the disjunction of strict termination refinements
            else if fml == ffalse
                  then return (FunctionT y (addRefinement tArg argLt) tRes', True)
                  else return (FunctionT y (addRefinement tArg (argLe `andClean` (fml `orClean` argLt))) tRes', True) -- TODO: this version in incomplete (does not allow later tuple values to go up), but is much faster
    recursiveTypeTuple t _ = return (t, False)

    -- | 'recursiveTypeFirst' @t fml@: type of the recursive call to a function of type @t@ when only the first recursible argument decreases
    recursiveTypeFirst (FunctionT x tArg tRes) = do
      case terminationRefinement x tArg of
        Nothing -> FunctionT x tArg <$> recursiveTypeFirst tRes
        Just (argLt, _) -> do
          y <- freshId "x"
          return $ FunctionT y (addRefinement tArg argLt) (renameVar x y tArg tRes)
    recursiveTypeFirst t = return t

    -- | If argument is recursible, return its strict and non-strict termination refinements, otherwise @Nothing@
    terminationRefinement argName (ScalarT IntT fml) = Just ( valInt |>=| IntLit 0  |&|  valInt |<| intVar argName,
                                                              valInt |>=| IntLit 0  |&|  valInt |<=| intVar argName)
    terminationRefinement argName (ScalarT dt@(DatatypeT name _ _) fml) = case env ^. datatypes . to (Map.! name) . wfMetric of
      Nothing -> Nothing
      Just mName -> let MeasureDef inSort outSort _ = (env ^. measures) Map.! mName
                        metric = Measure outSort mName
                    in Just ( metric (Var inSort valueVarName) |>=| IntLit 0  |&| metric (Var inSort valueVarName) |<| metric (Var inSort argName),
                              metric (Var inSort valueVarName) |>=| IntLit 0  |&| metric (Var inSort valueVarName) |<=| metric (Var inSort argName))
    terminationRefinement _ _ = Nothing


generateTopLevel (Goal _ env (Monotype t)) = generateI env t

-- | 'generateI' @env t@ : explore all terms that have refined type @t@ in environment @env@
-- (top-down phase of bidirectional typechecking)
generateI :: Monad s => Environment -> RType -> Explorer s RProgram
generateI env t@(FunctionT x tArg tRes) = do
  x' <- if x == dontCare then freshId "x" else return x
  let ctx = \p -> Program (PFun x' p) t
  pBody <- local (over (_1 . context) (. ctx)) $ generateI (unfoldAllVariables $ addVariable x' tArg $ env) tRes
  return $ ctx pBody
generateI env t@(ScalarT _ _) = ifM (asks $ _abduceScrutinees . fst)
                                    (generateMaybeMatchIf env t)
                                    (generateMaybeIf env t)
            

-- | Generate a possibly conditional term type @t@, depending on whether a condition is abduced
generateMaybeIf :: Monad s => Environment -> RType -> Explorer s RProgram
generateMaybeIf env t = ifte generateThen generateElse (generateMatch env t) -- If at least one solution without a match exists, go with it and continue with the else branch; otherwise try to match
  where
    -- | Guess an E-term and abduce a condition for it
    generateThen = do
      cUnknown <- Unknown Map.empty <$> freshId "u"
      addConstraint $ WellFormedCond env cUnknown
      (_, pThen) <- once $ generateE (addAssumption cUnknown env) t -- Do not backtrack: if we managed to find a soution for a nonempty subset of inputs, we go with it
      candidates %= take 1 -- We also stick to the current valuations of unknowns: there should be no reason to reconsider them, since we've closed a top-level goal
      cond <- uses candidates (conjunction . flip valuation cUnknown . solution . head)
      return (cond, pThen)

    -- | Proceed after solution @pThen@ has been found under assumption @cond@
    generateElse (cond, pThen) = if cond == ftrue
      then return pThen -- @pThen@ is valid under no assumptions: return it
      else do -- @pThen@ is valid under a nontrivial assumption, proceed to look for the solution for the rest of the inputs
            pCond <- generateCondition env cond
            pElse <- local (over (_1 . context) (. \p -> Program (PIf pCond pThen p) t)) $
                        generateMaybeIf (addAssumption (fnot cond) env) t            
            return $ Program (PIf pCond pThen pElse) t
            
generateCondition env fml = if isExecutable fml
                              then return $ fmlToProgram fml 
                              else snd <$> once (generateE env (ScalarT BoolT $ valBool |=| fml))            

-- | Generate a match term of type @t@
generateMatch env t = do
  d <- asks $ _matchDepth . fst
  if d == 0
    then mzero
    else do
      (env', pScrutinee) <- local (
                                    over _1 (\params -> set eGuessDepth (view scrutineeDepth params) params)
                                  . over (_1 . context) (. \p -> Program (PMatch p []) t))
                                  $ generateE env (vartAll dontCare) -- Generate a scrutinee of an arbitrary type

      case typeOf pScrutinee of
        (ScalarT (DatatypeT scrDT _ _) _) -> do -- Type of the scrutinee is a datatype
          let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors

          let scrutineeSymbols = symbolList pScrutinee
          let isGoodScrutinee = (not $ pScrutinee `elem` (env ^. usedScrutinees)) &&              -- We only need this in case the hiding flag is off
                                (not $ head scrutineeSymbols `elem` ctors) &&                     -- Is not a value
                                (any (not . flip Set.member (env ^. constants)) scrutineeSymbols) -- Has variables (not just constants)
          guard isGoodScrutinee

          (env'', x) <- toSymbol pScrutinee (addScrutinee pScrutinee env')
          (pCase, cond) <- once $ generateFirstCase env'' x pScrutinee t (head ctors)             -- First case generated separately in an attempt to abduce a condition for the whole match
          if cond == ftrue
            then do -- First case is valid unconditionally
              pCases <- mapM (once . generateCase env'' x pScrutinee t) (tail ctors)              -- Generate a case for each of the remaining constructors
              return $ Program (PMatch pScrutinee (pCase : pCases)) t
            else do -- First case is valid under a condition
              pCases <- mapM (once . generateCase (addAssumption cond env'') x pScrutinee t) (tail ctors)  -- Generate a case for each of the remaining constructors under the asumption
              let pThen = Program (PMatch pScrutinee (pCase : pCases)) t
              pCond <- generateCondition env cond
              pElse <- local (over (_1 . context) (. \p -> Program (PIf pCond pThen p) t)) $               -- Gnereate the else branch
                          generateI (addAssumption (fnot cond) env) t            
              return $ Program (PIf pCond pThen pElse) t

        _ -> mzero -- Type of the scrutinee is not a datatype: it cannot be used in a match
        
generateFirstCase env scrName pScrutinee t consName = do
  case Map.lookup consName (allSymbols env) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env
    Just consSch -> do
      consT <- instantiate env consSch ftrue
      matchConsType (lastType consT) (typeOf pScrutinee)
      let ScalarT baseT _ = (typeOf pScrutinee)
      (args, syms, ass) <- caseSymbols (Var (toSort baseT) scrName) (symbolType env consName consT)
      
      deadBranchCond <- isEnvironmentInconsistent env (foldr (uncurry addVariable) (addAssumption ass emptyEnv) syms) t
      case deadBranchCond of
        Nothing -> do
                    let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
                    pCaseExpr <- local (
                                         over (_1 . matchDepth) (-1 +)
                                       . over (_1 . context) (. \p -> Program (PMatch pScrutinee [Case consName args p]) t))
                                      $ generateI caseEnv t
                    return $ (Case consName args pCaseExpr, ftrue)
        
        Just cond -> return $ (Case consName args (Program (PSymbol "error") t), cond)

-- | Generate the @consName@ case of a match term with scrutinee variable @scrName@ and scrutinee type @scrType@
generateCase env scrName pScrutinee t consName = do
  case Map.lookup consName (allSymbols env) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env
    Just consSch -> do
      consT <- instantiate env consSch ftrue
      matchConsType (lastType consT) (typeOf pScrutinee)
      let ScalarT baseT _ = (typeOf pScrutinee)
      (args, syms, ass) <- caseSymbols (Var (toSort baseT) scrName) (symbolType env consName consT)
      let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
      pCaseExpr <- local (
                           over (_1 . matchDepth) (-1 +)
                         . over (_1 . context) (. \p -> Program (PMatch pScrutinee [Case consName args p]) t))
                        $ generateI caseEnv t
      return $ Case consName args pCaseExpr

caseSymbols x (ScalarT _ fml) = let subst = substitute (Map.singleton valueVarName x) in
  return ([], [], subst fml)
caseSymbols x (FunctionT y tArg tRes) = do
  argName <- freshId "x"
  (args, syms, ass) <- caseSymbols x (renameVar y argName tArg tRes)
  return (argName : args, (argName, tArg) : syms, ass)            

-- | Generate a possibly conditinal possibly match term, depending on which conditions are abduced
generateMaybeMatchIf env t = ifte generateOneBranch generateOtherBranches (generateMatch env t)
  where
    -- | Guess an E-term and abduce a condition and a match-condition for it
    generateOneBranch = do
      matchUnknown <- Unknown Map.empty <$> freshId "u"
      addConstraint $ WellFormedMatchCond env matchUnknown
      condUnknown <- Unknown Map.empty <$> freshId "u"
      addConstraint $ WellFormedCond env condUnknown
      (matchConds, p0) <- once $ do
        (_, p0) <- generateE (addAssumption matchUnknown . addAssumption condUnknown $ env) t
        matchValuation <- uses candidates (Set.toList . flip valuation matchUnknown . solution . head)
        let allVars = Set.toList $ Set.unions (map varsOf matchValuation)
        let matchConds = map (conjunction . Set.fromList . (\var -> filter (Set.member var . varsOf) matchValuation)) allVars -- group by vars
        d <- asks $ _matchDepth . fst -- Backtrack if too many matches, maybe we can find a solution with fewer
        guard $ length matchConds <= d
        return (matchConds, p0)

      cond <- uses candidates (conjunction . flip valuation condUnknown . solution . head)
      candidates %= take 1
      return (matchConds, cond, p0)

    -- | Proceed after solution @p0@ has been found under assumption @cond@ and match-assumption @matchCond@
    generateOtherBranches (matchConds, cond, p0) = case matchConds of
      [] -> if cond == ftrue
        then return p0 -- @p0@ is valid under no assumptions: return it
        else do -- @p0@ is valid under a nontrivial assumption, but no need to match
              pCond <- generateCondition env cond
              pElse <- local (over (_1 . context) (. \p -> Program (PIf pCond p0 p) t)) $
                          generateMaybeMatchIf (addAssumption (fnot cond) env) t
              return $ Program (PIf pCond p0 pElse) t
      _ -> if cond == ftrue
        then generateMatchesFor env matchConds p0 t
        else do -- @p0@ needs both a match and a condition; let's put the match inside the conditional because it's easier
              pCond <- generateCondition env cond
              pThen <- once $ generateMatchesFor (addAssumption cond env) matchConds p0 t
              pElse <- local (over (_1 . context) (. \p -> Program (PIf pCond pThen p) t)) $
                          generateMaybeMatchIf (addAssumption (fnot cond) env) t
              return $ Program (PIf pCond pThen pElse) t

    generateMatchesFor env [] pBaseCase t = return pBaseCase
    generateMatchesFor env (matchCond : rest) pBaseCase t = do
      let matchVar@(Var _ x) = Set.findMin $ varsOf matchCond
      let scrT@(ScalarT (DatatypeT scrDT _ _) _) = toMonotype $ symbolsOfArity 0 env Map.! x
      let pScrutinee = Program (PSymbol x) scrT
      let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors
      pBaseCase' <- once $ local (over (_1 . context) (. \p -> Program (PMatch pScrutinee [Case (head ctors) [] p]) t)) $
                            generateMatchesFor (addScrutinee pScrutinee . addAssumption matchCond $ env) rest pBaseCase t -- TODO: if matchCond contains only a subset of case conjuncts, we should add the rest
      generateKnownMatch env matchVar pBaseCase' t

    generateKnownMatch :: Monad s => Environment -> Formula -> RProgram -> RType -> Explorer s RProgram
    generateKnownMatch env var@(Var s x) pBaseCase t = do
      let scrT@(ScalarT (DatatypeT scrDT _ _) _) = toMonotype $ symbolsOfArity 0 env Map.! x
      let pScrutinee = Program (PSymbol x) scrT
      let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors
      let env' = addScrutinee pScrutinee env
      pCases <- mapM (once . generateCase env' x pScrutinee t) (tail ctors)              -- Generate a case for each constructor of the datatype
      return $ Program (PMatch pScrutinee (Case (head ctors) [] pBaseCase : pCases)) t

-- | 'generateE' @env typ@ : explore all elimination terms of type @typ@ in environment @env@
-- (bottom-up phase of bidirectional typechecking)
generateE :: Monad s => Environment -> RType -> Explorer s (Environment, RProgram)
generateE env typ = do
  d <- asks $ _eGuessDepth . fst
  (finalEnv, p) <- generateEUpTo env typ d
  ifM (asks $ _incrementalChecking . fst) (return ()) (solveConstraints p)
  return (finalEnv, p)

-- | 'generateEUpTo' @env typ d@ : explore all applications of type shape @shape typ@ in environment @env@ of depth up to @d@
generateEUpTo :: Monad s => Environment -> RType -> Int -> Explorer s (Environment, RProgram)
generateEUpTo env typ d = msum $ map (generateEAt env typ) [0..d]

-- | 'generateEAt' @env typ d@ : explore all applications of type shape @shape typ@ in environment @env@ of depth exactly to @d@
generateEAt :: Monad s => Environment -> RType -> Int -> Explorer s (Environment, RProgram)
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
      let tass = startState ^. typeAssignment
      let memoKey = MemoKey env (arity typ) (shape $ typeSubstitute tass (lastType typ)) startState d
      startMemo <- getMemo
      case Map.lookup memoKey startMemo of
        Just results -> do -- Found memoizaed results: fetch
          writeLog 1 (text "Fetching for:" <+> pretty memoKey $+$
                      text "Result:" $+$ vsep (map (\(env', p, _) -> programDoc (const Synquid.Pretty.empty) p) results))
          msum $ map applyMemoized results
        Nothing -> do -- Nothing found: enumerate and memoize
          writeLog 1 (text "Nothing found for:" <+> pretty memoKey)
          (envFinal, p) <- enumerateAt env typ d

          memo <- getMemo
          finalState <- get
          let memo' = Map.insertWith (flip (++)) memoKey [(envFinal, p, finalState)] memo
          writeLog 1 (text "Memoizing for:" <+> pretty memoKey <+> programDoc (const Synquid.Pretty.empty) p <+> text "::" <+> pretty (typeOf p))

          putMemo memo'

          checkE envFinal typ p
          return (envFinal, p)
  where
    getMemo = asks snd >>= lift . lift . lift . csGetMemo
    putMemo memo = asks snd >>= lift . lift . lift . (flip csPutMemo memo)

    applyMemoized (finalEnv, p, finalState) = do
      put finalState
      let env' = joinEnv env finalEnv
      checkE env' typ p
      return (env', p)

    joinEnv currentEnv memoEnv = over ghosts (Map.union (memoEnv ^. ghosts)) currentEnv

-- | Perform a gradual check that @p@ has type @typ@ in @env@:
-- if @p@ is a scalar, perform a full subtyping check;
-- if @p@ is a (partially applied) function, check as much as possible with unknown arguments
checkE :: Monad s => Environment -> RType -> RProgram -> Explorer s ()
checkE env typ p = do
  if arity typ == 0
    then addConstraint $ Subtype env (typeOf p) typ False
    else do
      addConstraint $ Subtype env (removeDependentRefinements (Set.fromList $ allArgs $ typeOf p) (lastType (typeOf p))) (lastType typ) False
      ifM (asks $ _consistencyChecking . fst) (addConstraint $ Subtype env (typeOf p) typ True) (return ()) -- add constraint that t and tFun be consistent (i.e. not provably disjoint)
  ifM (asks $ _incrementalChecking . fst) (solveConstraints p) (return ())
  where
    removeDependentRefinements argNames (ScalarT (DatatypeT name typeArgs pArgs) fml) = 
      ScalarT (DatatypeT name (map (removeDependentRefinements argNames) typeArgs) (map (removeFrom argNames) pArgs)) (removeFrom argNames fml)
    removeDependentRefinements argNames (ScalarT baseT fml) = ScalarT baseT (removeFrom argNames fml)
    removeFrom argNames fml = if varsOf fml `disjoint` argNames then fml else ffalse

enumerateAt :: Monad s => Environment -> RType -> Int -> Explorer s (Environment, RProgram)
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
      symbolUseCount %= Map.insertWith (+) name 1
      case Map.lookup name (env ^. shapeConstraints) of
        Nothing -> return ()
        Just sch -> solveLocally p $ Subtype env (refineBot $ shape t) (refineTop sch) False
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
      (env', fun) <- local (over (_1 . context) (. \p -> Program (PApp p (hole $ vartAll dontCare)) typ))
                            $ genFun env (FunctionT x (vartAll dontCare) typ) -- Find all functions that unify with (? -> typ)
      let FunctionT x tArg tRes = typeOf fun

      (envfinal, pApp) <- if isFunctionType tArg
        then do -- Higher-order argument: its value is not required for the function type, return a placeholder and enqueue an auxiliary goal
          arg <- enqueueGoal env' tArg
          return (env', Program (PApp fun arg) tRes)
        else do -- First-order argument: generate now
          (env'', arg) <- local (
                                  over (_1 . eGuessDepth) (-1 +)
                                . over (_1 . context) (. \p -> Program (PApp fun p) tRes))
                                $ genArg env' tArg
          (env''', y) <- toSymbol arg env''
          return (env''', Program (PApp fun arg) (renameVar x y tArg tRes))
      ifM (asks $ _hideScrutinees . fst) (guard $ not $ elem pApp (env ^. usedScrutinees)) (return ())
      return (envfinal, pApp)

-- | 'toSymbol' @p env@: a symbols with the same type as @p@ and an environment that defines that symbol (can be @p@ itself or a fresh ghost)
toSymbol (Program (PSymbol name) _) env | not (Set.member name (env ^. constants)) = return (env, name)
toSymbol p env = do
  g <- freshId "g"
  return (addGhost g (typeOf p) env, g)

enqueueGoal env typ = do
  g <- freshId "f"
  auxGoals %= ((Goal g env $ Monotype typ) :)
  return $ Program (PSymbol g) typ

{- Constraint solving -}

-- | Solve all currently unsolved constraints
-- (program @p@ is only used for logging)
solveConstraints :: Monad s => RProgram -> Explorer s ()
solveConstraints p = do
  ctx <- asks $ _context . fst
  writeLog 1 (text "Candidate Program" $+$ programDoc (const Synquid.Pretty.empty) (ctx p))

  simplifyAllConstraints
  processAllPredicates
  processAllConstraints
  solveHornClauses
  ifM (asks $ _consistencyChecking . fst) checkConsistency (return ())
  where
    -- | Decompose and unify typing constraints
    simplifyAllConstraints = do
      cs <- use typingConstraints
      tass <- use typeAssignment
      writeLog 1 (text "Typing Constraints" $+$ (vsep $ map pretty cs))

      typingConstraints .= []
      mapM_ simplifyConstraint cs
      tass' <- use typeAssignment
      writeLog 1 (text "Type assignment" $+$ vMapDoc text pretty tass')
      -- if type assignment has changed, we might be able to process more constraints:
      if Map.size tass' > Map.size tass
        then simplifyAllConstraints
        else return () -- writeLog 1 (text "With Shapes" $+$ programDoc (\typ -> option (not $ Set.null $ unknownsOfType typ) (pretty typ)) (programSubstituteTypes tass p))
        
    processAllPredicates = do
      cs <- use typingConstraints
      typingConstraints .= []
      mapM_ processWFPredicate cs
      pass' <- use predAssignment
      writeLog 1 (text "Pred assignment" $+$ vMapDoc text pretty pass')        

    -- | Convert simple typing constraints into horn clauses and qualifier maps
    processAllConstraints = do
      cs <- use typingConstraints
      typingConstraints .= []
      mapM_ processConstraint cs

    -- | Refine the current liquid assignments using the horn clauses
    solveHornClauses = do
      solv <- asks snd
      tass <- use typeAssignment
      qmap <- use qualifierMap
      clauses <- use hornClauses
      cands <- use candidates
      env <- use initEnv
      cands' <- lift . lift . lift $ csRefine solv clauses qmap (instantiateConsAxioms env) (programSubstituteTypes tass p) cands
      when (null cands') $ writeLog 1 (text "FAIL: horn clauses have no solutions") >> mzero
      candidates .= cands'
      hornClauses .= []

    checkConsistency = do
      solv <- asks snd
      fmls <- use consistencyChecks
      cands <- use candidates
      cands' <- lift . lift . lift $ csCheckConsistency solv fmls cands
      when (null cands') $ writeLog 1 (text "FAIL: inconsistent types") >> mzero
      candidates .= cands'
      consistencyChecks .= []

isEnvironmentInconsistent env env' t = do
  cUnknown <- Unknown Map.empty <$> freshId "u"
  solveLocally (Program (PSymbol "error") t) $ WellFormedCond env cUnknown 
  
  tass <- use typeAssignment
  pass <- use predAssignment
  qmap <- use qualifierMap
  let fml = conjunction $ embedding env tass pass
  let fml' = conjunction $ embedding env' tass pass
  solv <- asks snd
  cands <- use candidates
  env <- use initEnv
  cands' <- lift . lift . lift $ csRefine solv [(cUnknown |&| fml) |=>| fnot fml'] qmap (instantiateConsAxioms env) (Program (PSymbol "error") t) cands
  
  if null cands'
    then return Nothing
    else return $ Just $ (conjunction . flip valuation cUnknown . solution . head) cands'
    
solveLocally p c = do
  oldCs <- use typingConstraints
  typingConstraints .= []
  addConstraint c
  solveConstraints p
  typingConstraints .= oldCs    

simplifyConstraint :: Monad s => Constraint -> Explorer s ()
simplifyConstraint c = do
  tass <- use typeAssignment
  simplifyConstraint' tass c

simplifyConstraint' tass (Subtype env t tv@(ScalarT (TypeVarT a) _) consistent) | a == dontCare -- Dummy type variable: drop
  = return ()
-- -- Type variable with known assignment: substitute
simplifyConstraint' tass (Subtype env tv@(ScalarT (TypeVarT a) _) t consistent) | a `Map.member` tass
  = simplifyConstraint (Subtype env (typeSubstitute tass tv) t consistent)
simplifyConstraint' tass (Subtype env t tv@(ScalarT (TypeVarT a) _) consistent) | a `Map.member` tass
  = simplifyConstraint (Subtype env t (typeSubstitute tass tv) consistent)
simplifyConstraint' tass (WellFormed env tv@(ScalarT (TypeVarT a) _)) | a `Map.member` tass
  = simplifyConstraint (WellFormed env (typeSubstitute tass tv))
-- Two unknown free variables: nothing can be done for now
simplifyConstraint' _ c@(Subtype env (ScalarT (TypeVarT a) _) (ScalarT (TypeVarT b) _) _)
  | not (isBound a env) && not (isBound b env)
  = if a == b
      then writeLog 1 "simplifyConstraint: equal type variables on both sides"
      else addConstraint c
simplifyConstraint' _ c@(WellFormed env (ScalarT (TypeVarT a) _)) | not (isBound a env) = addConstraint c
-- Unknown free variable and a type: extend type assignment
simplifyConstraint' _ c@(Subtype env (ScalarT (TypeVarT a) _) t _)
  | not (isBound a env) = unify c env a t
simplifyConstraint' _ c@(Subtype env t (ScalarT (TypeVarT a) _) _)
  | not (isBound a env) = unify c env a t

-- Compound types: decompose
simplifyConstraint' _ (Subtype env (ScalarT (DatatypeT name (tArg:tArgs) pArgs) fml) (ScalarT (DatatypeT name' (tArg':tArgs') pArgs') fml') consistent)
  = do
      simplifyConstraint (Subtype env tArg tArg' consistent)
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name tArgs pArgs) fml) (ScalarT (DatatypeT name' tArgs' pArgs') fml') consistent)
simplifyConstraint' _ (Subtype env (ScalarT (DatatypeT name [] (pArg:pArgs)) fml) (ScalarT (DatatypeT name' [] (pArg':pArgs')) fml') consistent)
  = do
      -- simplifyConstraint (Subtype emptyEnv (int $ pArg) (int $ pArg') consistent) -- Is this a cheat?
      simplifyConstraint (Subtype env (int $ pArg) (int $ pArg') consistent) -- Is this a cheat?
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name [] pArgs) fml) (ScalarT (DatatypeT name' [] pArgs') fml') consistent)      
simplifyConstraint' _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) False)
  = do -- TODO: rename type vars
      simplifyConstraint (Subtype env tArg2 tArg1 False)
      -- writeLog 1 (text "RENAME VAR" <+> text x <+> text y <+> text "IN" <+> pretty tRes1)
      simplifyConstraint (Subtype (addVariable y tArg2 env) (renameVar x y tArg2 tRes1) tRes2 False)
simplifyConstraint' _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) True) -- This is a hack: we assume that arg in t2 is a free tv with no refinements
  = do -- TODO: rename type vars
      -- simplifyConstraint (Subtype env tArg2 tArg1 False)
      -- writeLog 1 (text "RENAME VAR" <+> text x <+> text y <+> text "IN" <+> pretty tRes1)
      simplifyConstraint (Subtype (addGhost y tArg1 env) (renameVar x y tArg1 tRes1) tRes2 True)
simplifyConstraint' _ (WellFormed env (ScalarT (DatatypeT name (tArg:tArgs) pArgs) fml))
  = do
      simplifyConstraint (WellFormed env tArg)
      simplifyConstraint (WellFormed env (ScalarT (DatatypeT name tArgs pArgs) fml))
simplifyConstraint' _ (WellFormed env (FunctionT x tArg tRes))
  = do
      simplifyConstraint (WellFormed env tArg)
      simplifyConstraint (WellFormed (addVariable x tArg env) tRes)

-- Simple constraint: add back
simplifyConstraint' _ c@(Subtype _ (ScalarT baseT _) (ScalarT baseT' _) _) | baseT == baseT' = addConstraint c
simplifyConstraint' _ c@(WellFormed _ (ScalarT baseT _)) = addConstraint c
simplifyConstraint' _ c@(WellFormedCond _ _) = addConstraint c
simplifyConstraint' _ c@(WellFormedMatchCond _ _) = addConstraint c
simplifyConstraint' _ c@(WellFormedPredicate _ _ _) = addConstraint c
-- Otherwise (shape mismatch): fail
simplifyConstraint' _ _ = writeLog 1 (text "FAIL: shape mismatch") >> mzero

unify c env a t = if a `Set.member` typeVarsOf t
  then writeLog 1 (text "simplifyConstraint: type variable occurs in the other type") >> mzero
  else do
    t' <- fresh env t
    writeLog 1 (text "UNIFY" <+> text a <+> text "WITH" <+> pretty t <+> text "PRODUCING" <+> pretty t')
    addTypeAssignment a t'
    simplifyConstraint c
    
processWFPredicate :: Monad s => Constraint -> Explorer s ()    
processWFPredicate c@(WellFormedPredicate env sorts p) 
  = do
      tass <- use typeAssignment
      pass <- use predAssignment      
      if Map.member p pass
        then return ()
        else let typeVars = Set.toList $ Set.unions $ map (typeVarsOf . fromSort) sorts
             in if any (isFreeVariable tass) typeVars
                then do
                  writeLog 1 $ text "WARNING: free vars in predicate" <+> pretty c
                  addConstraint c -- Still has type variables: cannot determine shape
                else do
                  u <- freshId "u"
                  addPredAssignment p (Unknown Map.empty u)
                  let sorts' = map (sortSubstitute $ asSortSubst tass) sorts
                  let vars = zipWith Var sorts' deBrujns
                  tq <- asks $ _typeQualsGen . fst
                  addQuals u (tq (env, last vars : (init vars ++ allScalars env tass)))
  where
    isFreeVariable tass a = not (isBound a env) && not (Map.member a tass)
processWFPredicate c = addConstraint c  
    

-- | Convert simple constraint to horn clauses and qualifier maps
processConstraint :: Monad s => Constraint -> Explorer s ()
processConstraint c@(Subtype env (ScalarT (TypeVarT a) _) (ScalarT (TypeVarT b) _) _)
  | not (isBound a env) && not (isBound b env) = addConstraint c
processConstraint c@(WellFormed env (ScalarT (TypeVarT a) _))
  | not (isBound a env) = addConstraint c
processConstraint c@(Subtype env (ScalarT baseTL l) (ScalarT baseTR r) False) | baseTL == baseTR
  = if l == ffalse || r == ftrue
      then return ()
      else do
        tass <- use typeAssignment
        pass <- use predAssignment
        let l' = substitutePredicate pass $ sortSubstituteFml (asSortSubst tass) l
        let r' = substitutePredicate pass $ sortSubstituteFml (asSortSubst tass) r
        if Set.null $ (predsOf l' `Set.union` predsOf r') Set.\\ (Map.keysSet $ env ^. boundPredicates)
          then do
            let lhss = embedding env tass pass `Set.union` Set.fromList [l'] -- (sortSubstFml l : allMeasurePostconditions baseT env)
            addHornClause $ conjunction lhss |=>| r'
          else -- One of the sides contains free predicates: nothing can be done yet            
            -- mzero
            addHornClause $ ftrue |=>| ffalse
processConstraint (Subtype env (ScalarT baseTL l) (ScalarT baseTR r) True) | baseTL == baseTR
  = do -- TODO: abs ref here
      tass <- use typeAssignment
      pass <- use predAssignment
      let l' = substitutePredicate pass $ sortSubstituteFml (asSortSubst tass) l
      let r' = substitutePredicate pass $ sortSubstituteFml (asSortSubst tass) r      
      addConsistencyCheck (conjunction (
                            Set.insert l' $ Set.insert r' $
                            embedding env tass pass))
processConstraint (WellFormed env (ScalarT baseT fml)) 
  = case fml of
      Unknown _ u -> do
        tass <- use typeAssignment
        tq <- asks $ _typeQualsGen . fst
        addQuals u (tq (env, Var (toSort baseT) valueVarName : allScalars env tass))
      _ -> return ()
processConstraint (WellFormedCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      cq <- asks $ _condQualsGen . fst
      addQuals u (cq (env, allScalars env tass))
processConstraint (WellFormedMatchCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      mq <- asks $ _matchQualsGen . fst
      addQuals u (mq (env, allPotentialScrutinees env tass))
processConstraint c@(WellFormedPredicate env sorts p) = addConstraint c
processConstraint c = error $ show $ text "processConstraint: not a simple constraint" <+> pretty c

-- | 'allScalars' @env@ : logic terms for all scalar symbols in @env@
allScalars :: Environment -> TypeSubstitution -> [Formula]
allScalars env subst = catMaybes $ map toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (_, ForallT _ _) = Nothing
    toFormula (x, Monotype t@(ScalarT (TypeVarT a) _)) | a `Map.member` subst = toFormula (x, Monotype $ typeSubstitute subst t)
    toFormula (_, Monotype (ScalarT IntT (Binary Eq _ (IntLit n)))) = Just $ IntLit n
    toFormula (x, Monotype (ScalarT b _)) = Just $ Var (toSort b) x
    
-- | 'allPotentialScrutinees' @env@ : logic terms for all scalar symbols in @env@
allPotentialScrutinees :: Environment -> TypeSubstitution -> [Formula]
allPotentialScrutinees env subst = catMaybes $ map toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (x, Monotype t@(ScalarT b@(DatatypeT _ _ _) _)) =
      if Set.member x (env ^. unfoldedVars) && not (Program (PSymbol x) t `elem` (env ^. usedScrutinees))
        then Just $ Var (toSort b) x
        else Nothing
    toFormula _ = Nothing

{- Utility -}

addQuals :: Monad s => Id -> QSpace -> Explorer s ()
addQuals name quals = do
  solv <- asks snd
  quals' <- lift . lift . lift $ csPruneQuals solv quals
  qualifierMap %= Map.insert name quals'

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: Monad s => String -> Explorer s String
freshId prefix = do
  i <- uses idCount (Map.findWithDefault 0 prefix)
  idCount %= Map.insert prefix (i + 1)
  return $ prefix ++ show i

-- | Replace all type variables with fresh identifiers
instantiate :: Monad s => Environment -> RSchema -> Formula -> Explorer s RType
instantiate env sch fml = writeLog 1 (text "INSTANTIATE" <+> pretty sch) >> instantiate' Map.empty Map.empty sch
  where
    instantiate' subst pSubst (ForallT a sch) = do
      a' <- freshId "a"
      addConstraint $ WellFormed env (vart a' ftrue)
      instantiate' (Map.insert a (vart a' fml) subst) pSubst sch
    instantiate' subst pSubst (ForallP p argSorts sch) = do
      p' <- freshId "P"
      let argSorts' = map (sortSubstitute (asSortSubst subst)) argSorts
      addConstraint $ WellFormedPredicate env argSorts' p'
      instantiate' subst (Map.insert p (Pred p' (zipWith Var argSorts deBrujns)) pSubst) sch
    instantiate' subst pSubst (Monotype t) = go subst pSubst t
    go subst pSubst (FunctionT x tArg tRes) = do
      x' <- freshId "x"
      liftM2 (FunctionT x') (go subst pSubst tArg) (go subst pSubst (renameVar x x' tArg tRes))
    go subst pSubst t = return $ typeSubstitutePred pSubst . typeSubstitute subst $ t

-- | 'fresh @t@ : a type with the same shape as @t@ but fresh type variables and fresh unknowns as refinements
fresh :: Monad s => Environment -> RType -> Explorer s RType
fresh env (ScalarT (TypeVarT a) _)
  | not (isBound a env) = do
  a' <- freshId "a"
  return $ ScalarT (TypeVarT a') ftrue
fresh env (ScalarT (DatatypeT name tArgs pArgs) _) = do
  k <- freshId "u"
  tArgs' <- mapM (fresh env) tArgs
  pArgs' <- mapM freshPred pArgs  
  return $ ScalarT (DatatypeT name tArgs' pArgs') (Unknown Map.empty k)
fresh env (ScalarT baseT _) = do
  k <- freshId "u"
  return $ ScalarT baseT (Unknown Map.empty k)
fresh env (FunctionT x tArg tFun) = do
  liftM2 (FunctionT x) (fresh env tArg) (fresh env tFun)
  
freshPred fml = do
  p' <- freshId "P"  
  let args = Set.toList $ varsOf fml -- ToDo: relying on the fact that we always use deBrujns and they will be ordered properly: is that true?
  return $ Pred p' args
  
symbolType env x (ScalarT b@(DatatypeT dtName _ _) fml)
  | x `elem` ((env ^. datatypes) Map.! dtName) ^. constructors = ScalarT b (fml |&| (Var (toSort b) valueVarName) |=| Cons (toSort b) x [])
symbolType env x t@(ScalarT b _)
  | Set.member x (env ^. constants) = t -- x is a constant, use it's type (it must be very precise)
  | otherwise                       = ScalarT b (varRefinement x (toSort b)) -- x is a scalar variable, use _v = x
symbolType env x t = case lastType t of
  (ScalarT b@(DatatypeT dtName _ _) fml) -> if x `elem` ((env ^. datatypes) Map.! dtName) ^. constructors
                                              then addRefinementToLast t ((Var (toSort b) valueVarName) |=| Cons (toSort b) x (allArgs t))
                                              else t
  _ -> t  

matchConsType (ScalarT (DatatypeT d vars pVars) _) (ScalarT (DatatypeT d' args pArgs) _) | d == d' 
  = do
      zipWithM_ (\(ScalarT (TypeVarT a) (BoolLit True)) t -> addTypeAssignment a t) vars args
      zipWithM_ (\(Pred p _) fml -> addPredAssignment p fml) pVars pArgs
      -- pass' <- use predAssignment
      -- writeLog 1 (text "Pred assignment" $+$ vMapDoc text pretty pass')        
matchConsType _ _ = mzero
      
instantiateConsAxioms :: Environment -> Formula -> Set Formula      
instantiateConsAxioms env fml = let inst = instantiateConsAxioms env in
  case fml of
    Cons (DataS dtName _) ctor args -> constructorAxioms args [] ctor (toMonotype $ allSymbols env Map.! ctor)
    Measure m _ arg -> inst arg
    Unary op e -> inst e
    Binary op e1 e2 -> inst e1 `Set.union` inst e2
    -- SetLit s elems -> ?
    Pred p args -> Set.unions $ map inst args
    -- All x e -> ?
    _ -> Set.empty  
  where
    constructorAxioms args vars ctor (ScalarT baseT fml) = let subst = Map.fromList $ (valueVarName, (Cons (toSort baseT) ctor args)) : zip vars args
      in conjunctsOf (substitute subst fml)
    constructorAxioms args vars ctor (FunctionT x tArg tRes) = constructorAxioms args (vars ++ [x]) ctor tRes

writeLog level msg = do
  maxLevel <- asks $ _explorerLogLevel . fst
  if level <= maxLevel then traceShow msg $ return () else return ()
