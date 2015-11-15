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
type QualsGen = [Formula] -> QSpace

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
  _candidates :: [Candidate],                   -- ^ Current set of candidate liquid assignments to unknowns
  _auxGoals :: [Goal],                          -- ^ Subterms to be synthesized independently
  _symbolUseCount :: Map Id Int                 -- ^ Number of times each symbol has been used in the program so far
} deriving Show

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
  csRefine :: [Formula] -> QMap -> RProgram -> [Candidate] -> s [Candidate],  -- ^ Refine current list of candidates to satisfy new constraints
  csPruneQuals :: QSpace -> s QSpace,                                         -- ^ Prune redundant qualifiers
  csCheckConsistency :: [Formula] -> [Candidate] -> s [Candidate],            -- ^ Check consistency of formulas under candidates
  csClearMemo :: s (),                                                        -- ^ Clear the memoization store
  csGetMemo :: s Memo,                                                        -- ^ Retrieve the memoization store
  csPutMemo :: Memo -> s()                                                    -- ^ Store the momization store
}

-- | Impose typing constraint @c@ on the programs
addConstraint c = typingConstraints %= (c :)
addTypeAssignment tv t = typeAssignment %= Map.insert tv t
addHornClause fml = hornClauses %= (fml :)
addConsistencyCheck fml = consistencyChecks %= (fml :)

-- | Computations that explore programs, parametrized by the the constraint solver and the backtracking monad
type Explorer s = StateT ExplorerState (ReaderT (ExplorerParams, ConstraintSolver s) (LogicT s))

-- | 'explore' @params env typ@ : explore all programs that have type @typ@ in the environment @env@;
-- exploration is driven by @params@
explore :: Monad s => ExplorerParams -> ConstraintSolver s -> Goal -> s [RProgram]
explore params solver goal = observeManyT 1 $ do
    initCand <- lift $ csInit solver
    runReaderT (evalStateT go (ExplorerState Map.empty [] Map.empty [] [] Map.empty [initCand] [] Map.empty)) (params, solver)
  where
    go :: Monad s => Explorer s RProgram
    go = do
      pMain <- generateTopLevel goal
      p <- generateAuxGoals pMain
      tass <- use typeAssignment
      sol <- uses candidates (solution . head)
      return $ programApplySolution sol $ programSubstituteTypes tass p

    generateAuxGoals p = do
      goals <- use auxGoals
      case goals of
        [] -> return p
        (Goal name env (Monotype spec)) : gs -> do
          auxGoals .= gs
          subterm <- generateI env spec
          generateAuxGoals $ programSubstituteSymbol name subterm p

{- AST exploration -}

-- | 'generateTopLevel' @env t@ : explore all terms that have refined type schema @sch@ in environment @env@
generateTopLevel :: Monad s => Goal -> Explorer s RProgram
generateTopLevel (Goal funName env (Forall a sch)) = generateTopLevel (Goal funName (addTypeVar a env) sch)
generateTopLevel (Goal funName env (Monotype t@(FunctionT _ _ _))) = generateFix
  where
    generateFix = do
      recCalls <- recursiveCalls t
      polymorphic <- asks $ _polyRecursion . fst
      let tvs = env ^. boundTypeVars
      let env' = if polymorphic && not (null tvs)
                    then foldr (\(f, t') -> addPolyVariable f (foldr Forall (Monotype t') tvs) . (shapeConstraints %~ Map.insert f (shape t))) env recCalls -- polymorphic recursion enabled: generalize on all bound variables
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
    terminationRefinement argName (ScalarT dt@(DatatypeT name tArgs) fml) = case env ^. datatypes . to (Map.! name) . wfMetric of
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
generateI env t@(ScalarT _ _) = do
  deadBranch <- isEnvironmentInconsistent env
  if deadBranch
    then return $ Program (PSymbol "error") t
    else ifM (asks $ _abduceScrutinees . fst)
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
      a <- freshId "a"
      (env', pScrutinee) <- local (
                                    over _1 (\params -> set eGuessDepth (view scrutineeDepth params) params)
                                  . over (_1 . context) (. \p -> Program (PMatch p []) t))
                                  $ generateE env (vartAll a) -- Generate a scrutinee of an arbitrary type

      case typeOf pScrutinee of
        (ScalarT (DatatypeT scrDT _) _) -> do -- Type of the scrutinee is a datatype
          let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors

          let scrutineeSymbols = symbolList pScrutinee
          let isGoodScrutinee = (not $ pScrutinee `elem` (env ^. usedScrutinees)) &&              -- We only need this in case the hiding flag is off
                                (not $ head scrutineeSymbols `elem` ctors) &&                     -- Is not a value
                                (any (not . flip Set.member (env ^. constants)) scrutineeSymbols) -- Has variables (not just constants)
          guard isGoodScrutinee

          (env'', x) <- toSymbol pScrutinee (addScrutinee pScrutinee env')
          pCases <- mapM (once . generateCase env'' x pScrutinee t) ctors              -- Generate a case for each constructor of the datatype
          return $ Program (PMatch pScrutinee pCases) t

        _ -> mzero -- Type of the scrutinee is not a datatype: it cannot be used in a match


-- | Generate the @consName@ case of a match term with scrutinee variable @scrName@ and scrutinee type @scrType@
generateCase env scrName pScrutinee t consName = do
  case Map.lookup consName (allSymbols env) of
    Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env
    Just consSch -> do
      consT <- freshTypeVars consSch ftrue
      matchConsType (lastType consT) (typeOf pScrutinee)
      let ScalarT baseT _ = (typeOf pScrutinee)
      (args, caseEnv) <- addCaseSymbols env (Var (toSort baseT) scrName) consT -- Add bindings for constructor arguments and refine the scrutinee type in the environment
      pCaseExpr <- local (
                           over (_1 . matchDepth) (-1 +)
                         . over (_1 . context) (. \p -> Program (PMatch pScrutinee [Case consName args p]) t))
                        $ generateI caseEnv t
      return $ Case consName args pCaseExpr
  where
    -- | 'addCaseSymbols' @env x tX case@ : extension of @env@ that assumes that scrutinee @x@ of type @tX@.
    addCaseSymbols env x (ScalarT _ fml) = let subst = substitute (Map.singleton valueVarName x) in
      return $ ([], addAssumption (subst fml) env) -- here disallowed unless no other choice
    addCaseSymbols env x (FunctionT y tArg tRes) = do
      argName <- freshId "x"
      (args, env') <- addCaseSymbols (addVariable argName tArg env) x (renameVar y argName tArg tRes)
      return (argName : args, env')

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
      let scrT@(ScalarT (DatatypeT scrDT _) _) = toMonotype $ symbolsOfArity 0 env Map.! x
      let pScrutinee = Program (PSymbol x) scrT
      let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors
      pBaseCase' <- once $ local (over (_1 . context) (. \p -> Program (PMatch pScrutinee [Case (head ctors) [] p]) t)) $
                            generateMatchesFor (addScrutinee pScrutinee . addAssumption matchCond $ env) rest pBaseCase t -- TODO: if matchCond contains only a subset of case conjuncts, we should add the rest
      generateKnownMatch env matchVar pBaseCase' t

    generateKnownMatch :: Monad s => Environment -> Formula -> RProgram -> RType -> Explorer s RProgram
    generateKnownMatch env var@(Var s x) pBaseCase t = do
      let scrT@(ScalarT (DatatypeT scrDT _) _) = toMonotype $ symbolsOfArity 0 env Map.! x
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
  generateEUpTo env typ d

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
      addConstraint $ Subtype env (removeDependentRefinements (allArgs (typeOf p)) (lastType (typeOf p))) (lastType typ) False
      ifM (asks $ _consistencyChecking . fst) (addConstraint $ Subtype env (typeOf p) typ True) (return ()) -- add constraint that t and tFun be consistent (i.e. not provably disjoint)
  solveConstraints p  
  where
    removeDependentRefinements argNames (ScalarT (DatatypeT name typeArgs) fml) = ScalarT (DatatypeT name $ map (removeDependentRefinements argNames) typeArgs) (if varsOf fml `disjoint` argNames then fml else ffalse)
    removeDependentRefinements argNames (ScalarT baseT fml) = ScalarT baseT (if varsOf fml `disjoint` argNames then fml else ffalse)        

enumerateAt :: Monad s => Environment -> RType -> Int -> Explorer s (Environment, RProgram)    
enumerateAt env typ 0 = do
  case soleConstructor (lastType typ) of
    Just (name, sch) -> do -- @typ@ is a datatype with only on constructor, so all terms must start with that constructor
      guard $ arity (toMonotype sch) == arity typ
      t <- instantiate sch
      pickSymbol (name, t)

    Nothing -> do
      symbols <- Map.toList <$> T.mapM instantiate (symbolsOfArity (arity typ) env)
      useCounts <- use symbolUseCount
      let symbols' = if arity typ == 0
                        then sortBy (mappedCompare (\(x, _) -> (Set.member x (env ^. constants), Map.findWithDefault 0 x useCounts))) symbols
                        else sortBy (mappedCompare (\(x, _) -> (not $ Set.member x (env ^. constants), Map.findWithDefault 0 x useCounts))) symbols

      msum $ map pickSymbol symbols'

  where
    pickSymbol (name, t) = let p = Program (PSymbol name) (symbolType name t) in
      do
        ifM (asks $ _hideScrutinees . fst) (guard $ not $ elem p (env ^. usedScrutinees)) (return ())
        symbolUseCount %= Map.insertWith (+) name 1
        case Map.lookup name (env ^. shapeConstraints) of
          Nothing -> return ()
          Just sh -> addConstraint $ Subtype env (refineBot $ shape t) (refineTop sh) False -- It's a polymorphic recursive call and has additional shape constraints
        return (env, p)
        
    symbolType x t@(ScalarT b _)
      | Set.member x (env ^. constants) = t -- x is a constant, use it's type (it must be very precise)
      | otherwise                       = ScalarT b (varRefinement x (toSort b)) -- x is a scalar variable, use _v = x
    symbolType _ t = t        

    instantiate sch = if arity (toMonotype sch) == 0
      then freshTypeVars sch ffalse -- This is a nullary constructor of a polymorphic type: it's safe to instantiate it with bottom refinements
      else freshTypeVars sch ftrue

    soleConstructor (ScalarT (DatatypeT name args) _) = let ctors = _constructors ((env ^. datatypes) Map.! name)
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
      cands' <- lift . lift . lift $ csRefine solv clauses qmap (programSubstituteTypes tass p) cands
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

isEnvironmentInconsistent env = do
  tass <- use typeAssignment
  let fml = conjunction $ embedding env tass
  solv <- asks snd
  cands <- use candidates
  cands' <- lift . lift . lift $ csCheckConsistency solv [fml] cands
  return $ null cands'

simplifyConstraint :: Monad s => Constraint -> Explorer s ()
simplifyConstraint c = do
  tass <- use typeAssignment
  simplifyConstraint' tass c

-- -- Type variable with known assignment: substitute
simplifyConstraint' tass (Subtype env tv@(ScalarT (TypeVarT a) _) t consistent) | a `Map.member` tass
  = simplifyConstraint (Subtype env (typeSubstitute tass tv) t consistent)
simplifyConstraint' tass (Subtype env t tv@(ScalarT (TypeVarT a) _) consistent) | a `Map.member` tass
  = simplifyConstraint (Subtype env t (typeSubstitute tass tv) consistent)
-- Two unknown free variables: nothing can be done for now
simplifyConstraint' _ c@(Subtype env (ScalarT (TypeVarT a) _) (ScalarT (TypeVarT b) _) _)
  | not (isBound a env) && not (isBound b env)
  = if a == b
      then writeLog 1 "simplifyConstraint: equal type variables on both sides"
      else addConstraint c
-- Unknown free variable and a type: extend type assignment
simplifyConstraint' _ c@(Subtype env (ScalarT (TypeVarT a) _) t _)
  | not (isBound a env) = unify c env a t
simplifyConstraint' _ c@(Subtype env t (ScalarT (TypeVarT a) _) _)
  | not (isBound a env) = unify c env a t

-- Compound types: decompose
simplifyConstraint' _ (Subtype env (ScalarT (DatatypeT name (tArg:tArgs)) fml) (ScalarT (DatatypeT name' (tArg':tArgs')) fml') consistent)
  = do
      simplifyConstraint (Subtype env tArg tArg' consistent)
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name tArgs) fml) (ScalarT (DatatypeT name' tArgs') fml') consistent)
simplifyConstraint' _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) False)
  = do -- TODO: rename type vars
      simplifyConstraint (Subtype env tArg2 tArg1 False)
      -- writeLog 1 (text "RENAME VAR" <+> text x <+> text y <+> text "IN" <+> pretty tRes1)
      simplifyConstraint (Subtype (addVariable y tArg2 env) (renameVar x y tArg2 tRes1) tRes2 False)
simplifyConstraint' _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) True) -- This is a hack: we assume that arg in t2 is a free tv with no refinements
  = do -- TODO: rename type vars
      -- simplifyConstraint (Subtype env tArg2 tArg1 False)
      -- writeLog 1 (text "RENAME VAR" <+> text x <+> text y <+> text "IN" <+> pretty tRes1)
      simplifyConstraint (Subtype (addGhost y tArg1 env) (renameVar x y tArg2 tRes1) tRes2 True)
simplifyConstraint' _ (WellFormed env (ScalarT (DatatypeT name (tArg:tArgs)) fml))
  = do
      simplifyConstraint (WellFormed env tArg)
      simplifyConstraint (WellFormed env (ScalarT (DatatypeT name tArgs) fml))
simplifyConstraint' _ (WellFormed env (FunctionT x tArg tRes))
  = do
      simplifyConstraint (WellFormed env tArg)
      simplifyConstraint (WellFormed (addVariable x tArg env) tRes)

-- Simple constraint: add back
simplifyConstraint' _ c@(Subtype env (ScalarT baseT _) (ScalarT baseT' _) _) | baseT == baseT' = addConstraint c
simplifyConstraint' _ c@(WellFormed env (ScalarT baseT _)) = addConstraint c
simplifyConstraint' _ c@(WellFormedCond env _) = addConstraint c
simplifyConstraint' _ c@(WellFormedMatchCond env _) = addConstraint c
-- Otherwise (shape mismatch): fail
simplifyConstraint' _ _ = writeLog 1 (text "FAIL: shape mismatch") >> mzero

unify c env a t = if a `Set.member` typeVarsOf t
  then writeLog 1 (text "simplifyConstraint: type variable occurs in the other type") >> mzero
  else do
    t' <- fresh env t
    writeLog 1 (text "UNIFY" <+> text a <+> text "WITH" <+> pretty t <+> text "PRODUCING" <+> pretty t')
    addConstraint $ WellFormed env t'
    addTypeAssignment a t'
    simplifyConstraint c


-- | Convert simple constraint to horn clauses and qualifier maps
processConstraint :: Monad s => Constraint -> Explorer s ()
processConstraint c@(Subtype env (ScalarT (TypeVarT a) _) (ScalarT (TypeVarT b) _) _)
  | not (isBound a env) && not (isBound b env) = addConstraint c
processConstraint (Subtype env (ScalarT baseT fml) (ScalarT baseT' fml') False) | baseT == baseT'
  = if fml == ffalse || fml' == ftrue
      then return ()
      else do
        tass <- use typeAssignment
        let sortSubstFml = sortSubstituteFml (asSortSubst tass)
        let lhss = embedding env tass `Set.union` Set.fromList [sortSubstFml fml] -- (sortSubstFml fml : allMeasurePostconditions baseT env)
        addHornClause $ conjunction lhss |=>| sortSubstFml fml'
processConstraint (Subtype env (ScalarT baseT fml) (ScalarT baseT' fml') True) | baseT == baseT'
  = do
      tass <- use typeAssignment
      let sortSubstFml = sortSubstituteFml (asSortSubst tass)
      addConsistencyCheck (conjunction (
                            Set.insert (sortSubstFml fml) $
                            Set.insert (sortSubstFml fml') $
                            embedding env tass))
processConstraint (WellFormed env (ScalarT baseT fml))
  = case fml of
      Unknown _ u -> do
        tass <- use typeAssignment
        tq <- asks $ _typeQualsGen . fst
        addQuals u (tq $ Var (toSort baseT) valueVarName : allScalars env tass)
      _ -> return ()
processConstraint (WellFormedCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      cq <- asks $ _condQualsGen . fst
      addQuals u (cq $ allScalars env tass)
processConstraint (WellFormedMatchCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      mq <- asks $ _matchQualsGen . fst
      addQuals u (mq $ allPotentialScrutinees env tass)
processConstraint c = error $ show $ text "processConstraint: not a simple constraint" <+> pretty c

-- | 'allScalars' @env@ : logic terms for all scalar symbols in @env@
allScalars :: Environment -> TypeSubstitution -> [Formula]
allScalars env subst = catMaybes $ map toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (_, Forall _ _) = Nothing
    toFormula (x, Monotype t@(ScalarT (TypeVarT a) _)) | a `Map.member` subst = toFormula (x, Monotype $ typeSubstitute subst t)
    toFormula (_, Monotype (ScalarT IntT (Binary Eq _ (IntLit n)))) = Just $ IntLit n
    toFormula (x, Monotype (ScalarT b _)) = Just $ Var (toSort b) x

-- | 'allPotentialScrutinees' @env@ : logic terms for all scalar symbols in @env@
allPotentialScrutinees :: Environment -> TypeSubstitution -> [Formula]
allPotentialScrutinees env subst = catMaybes $ map toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (x, Monotype t@(ScalarT b@(DatatypeT _ _) _)) =
      if Set.member x (env ^. unfoldedVars) && not (Program (PSymbol x) t `elem` (env ^. usedScrutinees))
        then Just $ Var (toSort b) x
        else Nothing
    toFormula _ = Nothing

{- Utility -}

addQuals :: Monad s => Id -> QSpace -> Explorer s ()
addQuals name quals = do
  solv <- asks snd
  quals' <- lift . lift . lift . csPruneQuals solv $ quals
  qualifierMap %= Map.insert name quals'

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: Monad s => String -> Explorer s String
freshId prefix = do
  i <- uses idCount (Map.findWithDefault 0 prefix)
  idCount %= Map.insert prefix (i + 1)
  return $ prefix ++ show i

-- | Replace all type variables with fresh identifiers
freshTypeVars :: Monad s => RSchema -> Formula -> Explorer s RType
freshTypeVars sch fml = freshTypeVars' Map.empty sch
  where
    freshTypeVars' subst (Forall a sch) = do
      a' <- freshId "a"
      freshTypeVars' (Map.insert a (vart a' fml) subst) sch
    freshTypeVars' subst (Monotype t) = go subst t
    go subst (FunctionT x tArg tRes) = do
      x' <- freshId "x"
      liftM2 (FunctionT x') (go subst tArg) (go subst (renameVar x x' tArg tRes))
    go subst t = return $ typeSubstitute subst t

-- | 'fresh @t@ : a type with the same shape as @t@ but fresh type variables and fresh unknowns as refinements
fresh :: Monad s => Environment -> RType -> Explorer s RType
fresh env (ScalarT (TypeVarT a) _)
  | not (isBound a env) = do
  a' <- freshId "a"
  return $ ScalarT (TypeVarT a') ftrue
fresh env (ScalarT (DatatypeT name tArgs) _) = do
  k <- freshId "u"
  tArgs' <- mapM (fresh env) tArgs
  return $ ScalarT (DatatypeT name tArgs') (Unknown Map.empty k)
fresh env (ScalarT baseT _) = do
  k <- freshId "u"
  return $ ScalarT baseT (Unknown Map.empty k)
fresh env (FunctionT x tArg tFun) = do
  liftM2 (FunctionT x) (fresh env tArg) (fresh env tFun)

matchConsType (ScalarT (DatatypeT d vars) _) (ScalarT (DatatypeT d' args) _) | d == d' = zipWithM_ (\(ScalarT (TypeVarT a) (BoolLit True)) t -> addTypeAssignment a t) vars args
matchConsType _ _ = mzero

fmlToProgram :: Formula -> RProgram
fmlToProgram (BoolLit b) = Program (PSymbol $ show b) (ScalarT BoolT $ valBool |=| BoolLit b)
fmlToProgram (IntLit i) = Program (PSymbol $ show i) (ScalarT IntT $ valBool |=| IntLit i)
fmlToProgram (Var s x) = Program (PSymbol x) (addRefinement (fromSort s) (varRefinement x s))
fmlToProgram fml@(Unary op e) = let 
    s = fromJust $ sortOf fml 
    p = fmlToProgram e
    fun = Program (PSymbol (show $ parens (pretty op))) (FunctionT "x" (typeOf p) opRes)
  in Program (PApp fun p) (addRefinement (fromSort s) (Var s valueVarName |=| fml))
  where    
    opRes 
      | op == Not = bool $ valBool |=| fnot (intVar "x")
      | otherwise = int $ valInt |=| Unary op (intVar "x")    
fmlToProgram fml@(Binary op e1 e2) = let 
    s = fromJust $ sortOf fml 
    p1 = fmlToProgram e1
    p2 = fmlToProgram e2
    fun1 = Program (PSymbol (show $ parens (pretty op))) (FunctionT "x" (typeOf p1) (FunctionT "y" (typeOf p2) opRes))
    fun2 = Program (PApp fun1 p1) (FunctionT "y" (typeOf p2) opRes)
  in Program (PApp fun2 p2) (addRefinement (fromSort s) (Var s valueVarName |=| fml))
  where
    opRes 
      | op == Times || op == Times || op == Times = int $ valInt |=| Binary op (intVar "x") (intVar "y")
      | otherwise                                 = bool $ valBool |=| Binary op (intVar "x") (intVar "y")

writeLog level msg = do
  maxLevel <- asks $ _explorerLogLevel . fst
  if level <= maxLevel then traceShow msg $ return () else return ()
