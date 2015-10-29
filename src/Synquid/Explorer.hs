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
import Control.Monad.Logic
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
  
-- | Choices for the order of e-term enumeration  
data PickSymbolStrategy = PickDepthFirst | PickInterleave

-- | Parameters of program exploration
data ExplorerParams = ExplorerParams {
  _eGuessDepth :: Int,                    -- ^ Maximum depth of application trees
  _scrutineeDepth :: Int,                 -- ^ Maximum depth of application trees inside match scrutinees
  _matchDepth :: Int,                     -- ^ Maximum nesting level of matches
  _condDepth :: Int,                      -- ^ Maximum nesting level of conditionals
  _combineSymbols :: PickSymbolStrategy,  -- ^ How to pick leaves in e-terms?
  _fixStrategy :: FixpointStrategy,       -- ^ How to generate terminating fixpoints
  _polyRecursion :: Bool,                 -- ^ Enable polymorphic recursion?
  _incrementalSolving :: Bool,            -- ^ Solve constraints as they appear (as opposed to all at once)?
  _condQualsGen :: QualsGen,              -- ^ Qualifier generator for conditionals
  _typeQualsGen :: QualsGen,              -- ^ Qualifier generator for types
  _context :: RProgram -> RProgram        -- ^ Context in which subterm is currently being generated (used only for logging)
}

makeLenses ''ExplorerParams

-- | Synthesis goal
data Goal = Goal {
  gName :: Id, 
  gEnvironment :: Environment, 
  gSpec :: RSchema,
  gParams :: ExplorerParams
}

-- | State of program exploration
data ExplorerState = ExplorerState {
  _idCount :: Int,                              -- ^ Number of unique identifiers issued so far
  _typingConstraints :: [Constraint],           -- ^ Typing constraints yet to be converted to horn clauses
  _qualifierMap :: QMap,                        -- ^ State spaces for all the unknowns generated from well-formedness constraints
  _hornClauses :: [Formula],                    -- ^ Horn clauses generated from subtyping constraints since the last liquid assignment refinement
  _typeAssignment :: TypeSubstitution,          -- ^ Current assignment to free type variables
  _candidates :: [Candidate],                   -- ^ Current set of candidate liquid assignments to unknowns
  _auxGoals :: [Goal],                          -- ^ Subterms to be synthesized independently
  _symbolUseCount :: Map Id Int                 -- ^ Number of times each symbol has been used in the program so far
}

makeLenses ''ExplorerState

-- | Impose typing constraint @c@ on the programs
addConstraint c = typingConstraints %= (c :)
addTypeAssignment tv t = typeAssignment %= Map.insert tv t
addHornClause lhs rhs = hornClauses %= ((lhs |=>| rhs) :)

-- | Computations that explore programs, parametrized by the the constraint solver and the backtracking monad
type Explorer s = StateT ExplorerState (ReaderT (ExplorerParams, ConstraintSolver s) (LogicT s))

-- | 'explore' @params env typ@ : explore all programs that have type @typ@ in the environment @env@;
-- exploration is driven by @params@
explore :: Monad s => Goal -> ConstraintSolver s -> LogicT s RProgram
explore goal solver = do
    initCand <- lift $ csInit solver
    runReaderT (evalStateT go (ExplorerState 0 [] Map.empty [] Map.empty [initCand] [] Map.empty)) (gParams goal, solver) 
  where
    go :: Monad s => Explorer s RProgram
    go = do
      pMain <- generateTopLevel (gEnvironment goal) (gSpec goal)
      p <- generateAuxGoals pMain
      ifM (asks $ _incrementalSolving . fst) (return ()) (solveConstraints p)
      tass <- use typeAssignment
      sol <- uses candidates (solution . head)
      return $ programApplySolution sol $ programSubstituteTypes tass p
      
    generateAuxGoals p = do
      goals <- use auxGoals
      case goals of
        [] -> return p
        (Goal name env (Monotype spec) params) : gs -> local (set _1 params) $ do
          auxGoals .= gs
          subterm <- generateI env spec
          generateAuxGoals $ programSubstituteSymbol name subterm p

{- AST exploration -}
    
-- | 'generateTopLevel' @env t@ : explore all terms that have refined type schema @sch@ in environment @env@    
generateTopLevel :: Monad s => Environment -> RSchema -> Explorer s RProgram
generateTopLevel env (Forall a sch) = generateTopLevel (addTypeVar a env) sch
generateTopLevel env (Monotype t@(FunctionT _ _ _)) = generateFix
  where
    generateFix = do
      recCalls <- recursiveCalls t
      polymorphic <- asks $ _polyRecursion . fst
      let env' = if polymorphic
                    then let tvs = env ^. boundTypeVars in 
                      foldr (\(f, t') -> addPolyVariable f (foldr Forall (Monotype t') tvs) . (shapeConstraints %~ Map.insert f (shape t))) env recCalls -- polymorphic recursion enabled: generalize on all bound variables
                    else foldr (\(f, t') -> addVariable f t') env recCalls  -- do not generalize
      let ctx = \p -> if null recCalls then p else Program (PFix (map fst recCalls) p) t
      p <- local (over (_1 . context) (. ctx)) $ generateI env' t
      return $ ctx p

    -- | 'recursiveCalls' @t@: name-type pairs for recursive calls to a function with type @t@;
    -- (when using lexicographic termination metrics, different calls differ in the component they decrease; otherwise at most one call). 
    -- recursiveCalls (FunctionT x1 tArg1 (FunctionT x2 tArg2 tRes)) = do      
      -- y1 <- freshId "x"
      -- y2 <- freshId "x"
      -- f <- freshId "f"
      -- let (ScalarT dt@(DatatypeT d) tArgs _) = tArg1
      -- let (Just metric) = env ^. datatypes . to (Map.! d) . wfMetric
      -- let ds = toSort dt
      -- let tArg1' = ScalarT dt tArgs (metric (Var ds valueVarName) |<=| metric (Var ds x1))
      -- let tArg2' = ScalarT dt tArgs (metric (Var ds y1) |<| metric (Var ds x1) ||| metric (Var ds valueVarName) |<| metric (Var ds x2))
      -- return $ [(f, FunctionT y1 tArg1' (FunctionT y2 tArg2' (renameVar x1 y1 tArg1 (renameVar x2 y2 tArg2 tRes))))]      
      
    recursiveCalls (FunctionT x tArg tRes) = do
      y <- freshId "x"
      calls' <- recursiveCalls tRes
      case recursiveTArg x tArg of
        Nothing -> return $ map (\(f, tRes') -> (f, FunctionT y tArg (renameVar x y tArg tRes'))) calls'
        Just (tArgLt, tArgEq) -> do
          f <- freshId "f"
          fixStrategy <- asks $ _fixStrategy . fst
          case fixStrategy of
            AllArguments -> return $ (f, FunctionT y tArgLt (renameVar x y tArg tRes)) : map (\(f, tRes') -> (f, FunctionT y tArgEq (renameVar x y tArg tRes'))) calls'
            FirstArgument -> return [(f, FunctionT y tArgLt (renameVar x y tArg tRes))]
            DisableFixpoint -> return []
    recursiveCalls _ = return []
        
    -- | 'recursiveTArg' @argName t@ : type of the argument of a recursive call,
    -- inside the body of the recursive function where its argument has name @argName@ and type @t@
    -- (@t@ strengthened with a termination condition)    
    recursiveTArg argName (ScalarT IntT _ fml) = Just $ (int (fml  `andClean`  (valInt |>=| IntLit 0  |&|  valInt |<| intVar argName)), int (fml  `andClean`  (valInt |=| intVar argName)))
    recursiveTArg argName (ScalarT dt@(DatatypeT name) tArgs fml) = case env ^. datatypes . to (Map.! name) . wfMetric of
      Nothing -> Nothing
      Just metric -> let ds = toSort dt in 
        Just $ (ScalarT (DatatypeT name) tArgs (fml `andClean` (metric (Var ds valueVarName) |<| metric (Var ds argName))), 
          ScalarT (DatatypeT name) tArgs (fml `andClean` (metric (Var ds valueVarName) |=| metric (Var ds argName))))      
    recursiveTArg _ _ = Nothing
    
generateTopLevel env (Monotype t) = generateI env t    

-- | 'generateI' @env t@ : explore all terms that have refined type @t@ in environment @env@
-- (top-down phase of bidirectional typechecking)  
generateI :: Monad s => Environment -> RType -> Explorer s RProgram  
generateI env t@(FunctionT x tArg tRes) = do
  let ctx = \p -> Program (PFun x p) t    
  pBody <- local (over (_1 . context) (. ctx)) $ generateI (addVariable x tArg $ env) tRes
  return $ ctx pBody            
generateI env t@(ScalarT _ _ _) = ifM (asks $ _incrementalSolving . fst) 
                                    (generateMaybeIf env t `mplus` generateMatch env t)
                                    (guessE env t `mplus` generateMatch env t `mplus` generateIf env t)
                                    
-- | Guess an E-term and and check that is has type @t@ in the environment @env@
guessE env t = do
  (env', res) <- generateE env t
  addConstraint $ Subtype env' (typeOf res) t
  ifM (asks $ _incrementalSolving . fst) (solveConstraints res) (return ())
  return res
  
-- | Generate a (possibly generate) conditional term type @t@
generateMaybeIf env t = do
  cond <- Unknown Map.empty <$> freshId "c"
  addConstraint $ WellFormedCond env cond
  pThen <- once $ guessE (addAssumption cond env) t
  condVal <- uses candidates (conjunction . flip valuation cond . solution . head) -- TODO: what to do with other solutions?
  case condVal of
    BoolLit True -> return pThen -- @pThen@ is valid under no assumptions: return it
    _ -> do -- @pThen@ is valid under a nontrivial assumption, proceed to look for the solution for the rest of the inputs
      pElse <- local (over (_1 . context) (. \p -> Program (PIf condVal pThen p) t)) $
                  generateMaybeIf (addAssumption (fnot condVal) env) t
      return $ Program (PIf condVal pThen pElse) t  
  
-- | Generate a match term of type @t@
generateMatch env t = do
  d <- asks $ _matchDepth . fst
  if d == 0
    then mzero
    else do
      a <- freshId "_a"
      (env', pScrutinee) <- local (
                                    over _1 (\params -> set eGuessDepth (view scrutineeDepth params) params)
                                  . over (_1 . context) (. \p -> Program (PMatch p []) t)) 
                                  $ generateE env (vartAll a) -- Generate a scrutinee of an arbitrary type
                                  
      case typeOf pScrutinee of
        (ScalarT (DatatypeT scrDT) _ _) -> do -- Type of the scrutinee is a datatype
          let ctors = ((env ^. datatypes) Map.! scrDT) ^. constructors
          
          let scrutineeSymbols = symbolList pScrutinee
          let isGoodScrutinee = (not $ pScrutinee `elem` (env ^. usedScrutinees)) &&              -- Has not been used before
                                (not $ head scrutineeSymbols `elem` ctors) &&                     -- Is not a value
                                (any (not . flip Set.member (env ^. constants)) scrutineeSymbols) -- Has variables (not just constants)
          guard isGoodScrutinee
          
          (env'', x) <- (addGhost pScrutinee) . (addScrutinee pScrutinee) $ env'
          backtrackCase <- ifM (asks $ _incrementalSolving . fst) (return once) (return id)   -- When incremental solving is enabled, once a solution for a case is found, it's final and we don't need to backtrack past it
          pCases <- mapM (backtrackCase . generateCase env'' x pScrutinee) ctors              -- Generate a case for each constructor of the datatype
          return $ Program (PMatch pScrutinee pCases) t
                    
        _ -> mzero -- Type of the scrutinee is not a datatype: it cannot be used in a match
                                        
  where      
    -- | Generate the @consName@ case of a match term with scrutinee variable @scrName@ and scrutinee type @scrType@
    generateCase env scrName pScrutinee consName = do
      case Map.lookup consName (allSymbols env) of
        Nothing -> error $ show $ text "Datatype constructor" <+> text consName <+> text "not found in the environment" <+> pretty env 
        Just consSch -> do
          consT <- freshTypeVars consSch
          matchConsType (lastType consT) (typeOf pScrutinee)
          let ScalarT baseT _ _ = (typeOf pScrutinee)          
          (args, caseEnv) <- addCaseSymbols env (Var (toSort baseT) scrName) consT -- Add bindings for constructor arguments and refine the scrutinee type in the environment          
          pCaseExpr <- local (
                               over (_1 . matchDepth) (-1 +)
                             . over (_1 . context) (. \p -> Program (PMatch pScrutinee [Case consName args p]) t))
                            $ generateI caseEnv t
          return $ Case consName args pCaseExpr
      
    -- | 'addCaseSymbols' @env x tX case@ : extension of @env@ that assumes that scrutinee @x@ of type @tX@.
    addCaseSymbols env x (ScalarT _ _ fml) = let subst = substitute (Map.singleton valueVarName x) in 
      -- return $ ([], addNegAssumption (fnot $ subst fml) env) -- here vacuous cases are allowed
      return $ ([], addAssumption (subst fml) env) -- here disallowed unless no other choice
    addCaseSymbols env x (FunctionT y tArg tRes) = do
      argName <- freshId "z"
      (args, env') <- addCaseSymbols (addVariable argName tArg env) x (renameVar y argName tArg tRes)
      return (argName : args, env')          

-- | Generate a conditional term of type @t@
generateIf env t = do
  d <- asks $ _condDepth . fst
  if d == 0
    then mzero
    else do    
      cond <- Unknown Map.empty <$> freshId "c"
      addConstraint $ WellFormedCond env cond
      pThen <- local (
                  over (_1 . condDepth) (-1 +) 
                . over (_1 . context) (. \p -> Program (PIf cond p (hole t)) t)) 
                $ generateI (addAssumption cond env) t
      pElse <- local (
                  over (_1 . condDepth) (-1 +)
                . over (_1 . context) (. \p -> Program (PIf cond pThen p) t)) 
                $ generateI (addNegAssumption cond env) t          
      return $ Program (PIf cond pThen pElse) t
                
-- | 'generateE' @env typ@ : explore all elimination terms of type shape @shape typ@ in environment @env@
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

generateEAt env typ 0 = do
  symbols <- Map.toList <$> T.mapM freshTypeVars (symbolsOfArity (arity typ) env)
  useCounts <- use symbolUseCount
  let symbols' = sortBy (mappedCompare (\(x, _) -> Map.findWithDefault 0 x useCounts)) symbols
  
  combine <- asks $ _combineSymbols . fst
  case combine of
    PickDepthFirst -> msum $ map pickSymbol symbols'
    PickInterleave -> foldl interleave mzero $ map pickSymbol symbols'
  
  where
    pickSymbol (name, t) = let p = Program (PSymbol name) (symbolType name t) in
      do
        symbolUseCount %= Map.insertWith (+) name 1
        case Map.lookup name (env ^. shapeConstraints) of
          Nothing -> return ()
          Just sh -> do
            addConstraint $ Subtype env (refineBot $ shape t) (refineTop sh) -- It's a plymorphic recursive call and has additional shape constraints
            ifM (asks $ _incrementalSolving . fst) (solveConstraints p) (return ())
        return (env, p)

    symbolType x t@(ScalarT b args _)
      | Set.member x (env ^. constants) = t -- x is a constant, use it's type (it must be very precise)
      | otherwise                       = ScalarT b args (varRefinement x b) -- x is a scalar variable, use _v = x
    symbolType _ t = t
        
generateEAt env typ d = do    
  let maxArity = fst $ Map.findMax (env ^. symbols)
  guard $ arity typ < maxArity
  generateApp (\e t -> generateEUpTo e t d) (\e t -> generateEAt e t (d - 1)) `mplus`
    generateApp (\e t -> generateEAt e t d) (\e t -> generateEUpTo e t (d - 2)) 
  where
    generateApp genFun genArg = do
      a <- freshId "_a"
      x <- freshId "x"    
      (env', fun) <- local (over (_1 . context) (. \p -> Program (PApp p (hole $ vartAll a)) typ)) 
                            $ generateFun genFun env (FunctionT x (vartAll a) typ) -- Find all functions that unify with (? -> typ)
      let FunctionT x tArg tRes = typeOf fun
              
      if isFunctionType tArg
        then do -- Higher-order argument: its value is not required for the function type, return a placeholder and enqueue an auxiliary goal
          arg <- enqueueGoal env' tArg
          return (env', Program (PApp fun arg) tRes)
        else do -- First-order argument: generate now         
          (env'', arg) <- local (
                                  over (_1 . eGuessDepth) (-1 +)
                                . over (_1 . context) (. \p -> Program (PApp fun p) tRes)) 
                                $ generateArg genArg env' tArg
          (env''', y) <- addGhost arg env''
          return (env''', Program (PApp fun arg) (renameVar x y tArg tRes))
          
    generateFun genFun env tFun = do
      (env', fun) <- genFun env tFun
      let t = typeOf fun
      -- The following performs early filtering of incomplete application terms
      -- by comparing their result type with the spec's result type, 
      -- after replacing all refinements that depend on yet undefined variables with false.
      addConstraint $ Subtype env' (removeDependentRefinements (allArgs t) (lastType t)) (lastType tFun)
      ifM (asks $ _incrementalSolving . fst) (solveConstraints fun) (return ())
      return (env', fun)
      
    removeDependentRefinements argNames (ScalarT baseT typeArgs fml) = ScalarT baseT (map (removeDependentRefinements argNames) typeArgs) (if varsOf fml `disjoint` argNames then fml else ffalse)
          
    generateArg genArg env tArg = do
      (env', arg) <- genArg env tArg
      addConstraint $ Subtype env' (typeOf arg) tArg
      ifM (asks $ _incrementalSolving . fst) (solveConstraints arg) (return ())
      return (env', arg)
      
enqueueGoal env typ = do
  g <- freshId "g"
  params <- asks fst
  auxGoals %= ((Goal g env (Monotype typ) params) :)
  return $ Program (PSymbol g) typ      
   
addGhost :: Monad s => RProgram -> Environment -> Explorer s (Environment, Id)   
addGhost (Program (PSymbol name) _) env | not (Set.member name (env ^. constants)) = return (env, name)
addGhost p env = do
  g <- freshId "g" 
  return (over ghosts (Map.insert g (typeOf p)) env, g)          
    
{- Constraint solving -}

-- | Solve all currently unsolved constraints
-- (program @p@ is only used for debug information)
solveConstraints :: Monad s => RProgram -> Explorer s ()
solveConstraints p = do
  ctx <- asks $ _context . fst
  debug 1 (text "Candidate Program" $+$ programDoc (const Synquid.Pretty.empty) (ctx p)) $ return ()

  simplifyAllConstraints
  processAllConstraints
  solveHornClauses
  where
    -- | Decompose and unify typing constraints
    simplifyAllConstraints = do
      cs <- use typingConstraints
      tass <- use typeAssignment      
      debug 1 (text "Typing Constraints" $+$ (vsep $ map pretty cs)) $ return ()
      
      typingConstraints .= []
      mapM_ simplifyConstraint cs
      tass' <- use typeAssignment
      debug 1 (text "Type assignment" $+$ vMapDoc text pretty tass') $ return ()
      -- if type assignment has changed, we might be able to process more constraints:
      if Map.size tass' > Map.size tass
        then simplifyAllConstraints
        else debug 1 (text "With Shapes" $+$ programDoc (\typ -> option (not $ Set.null $ unknownsOfType typ) (pretty typ)) (programSubstituteTypes tass p)) $ return ()
        
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
      cands' <- lift . lift .lift $ csRefine solv clauses qmap (programSubstituteTypes tass p) cands
      when (null cands') $ debug 1 (text "FAIL: horn clauses have no solutions") mzero
      candidates .= cands'
      hornClauses .= []
    
    
simplifyConstraint :: Monad s => Constraint -> Explorer s ()
simplifyConstraint c = do
  tass <- use typeAssignment
  simplifyConstraint' tass c

-- -- Type variable with known assignment: substitute
simplifyConstraint' tass (Subtype env tv@(ScalarT (TypeVarT a) [] _) t) | a `Map.member` tass
  = simplifyConstraint (Subtype env (typeSubstitute tass tv) t)
simplifyConstraint' tass (Subtype env t tv@(ScalarT (TypeVarT a) [] _)) | a `Map.member` tass
  = simplifyConstraint (Subtype env t (typeSubstitute tass tv))
-- Two unknown free variables: nothing can be done for now
simplifyConstraint' _ c@(Subtype env (ScalarT (TypeVarT a) [] _) (ScalarT (TypeVarT b) [] _)) 
  | not (isBound a env) && not (isBound b env)
  = if a == b
      then debug 1 "simplifyConstraint: equal type variables on both sides" $ return ()
      else addConstraint c
-- Unknown free variable and a type: extend type assignment      
simplifyConstraint' _ c@(Subtype env (ScalarT (TypeVarT a) [] _) t) 
  | not (isBound a env) = unify c env a t
simplifyConstraint' _ c@(Subtype env t (ScalarT (TypeVarT a) [] _)) 
  | not (isBound a env) = unify c env a t        

-- Compound types: decompose
simplifyConstraint' _ (Subtype env (ScalarT baseT (tArg:tArgs) fml) (ScalarT baseT' (tArg':tArgs') fml')) 
  = do
      simplifyConstraint (Subtype env tArg tArg') -- assuming covariance
      simplifyConstraint (Subtype env (ScalarT baseT tArgs fml) (ScalarT baseT' tArgs' fml')) 
simplifyConstraint' _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2))
  = do -- TODO: rename type vars
      simplifyConstraint (Subtype env tArg2 tArg1)
      -- debug 1 (text "RENAME VAR" <+> text x <+> text y <+> text "IN" <+> pretty tRes1) $ return ()
      simplifyConstraint (Subtype (addVariable y tArg2 env) (renameVar x y tArg2 tRes1) tRes2)
simplifyConstraint' _ (WellFormed env (ScalarT baseT (tArg:tArgs) fml))
  = do
      simplifyConstraint (WellFormed env tArg)
      simplifyConstraint (WellFormed env (ScalarT baseT tArgs fml))
simplifyConstraint' _ (WellFormed env (FunctionT x tArg tRes))
  = do
      simplifyConstraint (WellFormed env tArg)
      simplifyConstraint (WellFormed (addVariable x tArg env) tRes)
      
-- Simple constraint: add back      
simplifyConstraint' _ c@(Subtype env (ScalarT baseT [] _) (ScalarT baseT' [] _)) | baseT == baseT' = addConstraint c
simplifyConstraint' _ c@(WellFormed env (ScalarT baseT [] _)) = addConstraint c
simplifyConstraint' _ c@(WellFormedCond env _) = addConstraint c      
-- Otherwise (shape mismatch): fail      
simplifyConstraint' _ _ = debug 1 (text "FAIL: shape mismatch") mzero

unify c env a t = if a `Set.member` typeVarsOf t
  then debug 1 (text "simplifyConstraint: type variable occurs in the other type") mzero
  else do    
    t' <- fresh env t
    debug 1 (text "UNIFY" <+> text a <+> text "WITH" <+> pretty t <+> text "PRODUCING" <+> pretty t') $ return ()
    addConstraint $ WellFormed env t'
    addTypeAssignment a t'
    simplifyConstraint c
      
  
-- | Convert simple constraint to horn clauses and qualifier maps
processConstraint :: Monad s => Constraint -> Explorer s ()
processConstraint c@(Subtype env (ScalarT (TypeVarT a) [] _) (ScalarT (TypeVarT b) [] _)) 
  | not (isBound a env) && not (isBound b env) = addConstraint c
processConstraint (Subtype env (ScalarT baseT [] fml) (ScalarT baseT' [] fml')) | baseT == baseT' 
  = if fml == ffalse || fml' == ftrue
      then return ()
      else do
        tass <- use typeAssignment
        let (poss, negs) = embedding env tass
        addHornClause (conjunction (Set.insert (typeSubstituteFML tass fml) poss)) (disjunction (Set.insert (typeSubstituteFML tass fml') negs))
processConstraint (WellFormed env (ScalarT baseT [] fml))
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
processConstraint c = error $ show $ text "processConstraint: not a simple constraint" <+> pretty c
          
{- Utility -}

addQuals :: Monad s => Id -> QSpace -> Explorer s ()
addQuals name quals = do
  solv <- asks snd
  quals' <- lift . lift . lift . csPruneQuals solv $ quals
  qualifierMap %= Map.insert name quals'

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: Monad s => String -> Explorer s String
freshId prefix = do
  i <- use idCount
  idCount .= i + 1
  return $ prefix ++ show i
      
-- | Replace all type variables with fresh identifiers    
freshTypeVars :: Monad s => RSchema -> Explorer s RType    
freshTypeVars sch = freshTypeVars' Map.empty sch
  where
    freshTypeVars' subst (Forall a sch) = do
      a' <- freshId "a"      
      freshTypeVars' (Map.insert a (vartAll a') subst) sch
    freshTypeVars' subst (Monotype t) = return $ typeSubstitute subst t

-- | 'fresh @t@ : a type with the same shape as @t@ but fresh type variables and fresh unknowns as refinements
fresh :: Monad s => Environment -> RType -> Explorer s RType
fresh env (ScalarT (TypeVarT a) [] _)
  | not (isBound a env) = do
  a' <- freshId "a"
  return $ ScalarT (TypeVarT a') [] ftrue
fresh env (ScalarT base args _) = do
  k <- freshId "u"
  args' <- mapM (fresh env) args
  return $ ScalarT base args' (Unknown Map.empty k)
fresh env (FunctionT x tArg tFun) = do
  liftM2 (FunctionT x) (fresh env tArg) (fresh env tFun)
  
matchConsType (ScalarT (DatatypeT d) vars _) (ScalarT (DatatypeT d') args _) | d == d' = zipWithM_ (\(ScalarT (TypeVarT a) [] (BoolLit True)) t -> addTypeAssignment a t) vars args
matchConsType _ _ = mzero
