{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

-- | Incremental solving of subtyping and well-formedness constraints
module Synquid.TypeConstraintSolver (
  ErrorMessage,
  TypingParams (..),
  TypingState,
  typingConstraints,
  typeAssignment,
  qualifierMap,
  hornClauses,
  candidates,
  errorContext,
  isFinal,
  TCSolver,
  runTCSolver,
  initTypingState,
  addTypingConstraint,
  addFixedUnknown,
  setUnknownRecheck,
  solveTypeConstraints,
  checkTypeConstraints,  
  simplifyAllConstraints,
  getViolatingLabels,  
  solveAllCandidates,
  matchConsType,
  hasPotentialScrutinees,
  freshId,
  freshVar,
  currentAssignment,
  finalizeType,
  finalizeProgram,
  initEnv,
  allScalars,
  condQualsGen
) where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.SolverMonad
import Synquid.Util
import Synquid.Resolver (addAllVariables)

import Data.Function (on)
import Data.Ord (comparing)
import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Applicative hiding (empty)
import Control.Lens hiding (both)
import Debug.Trace

{- Interface -}

-- | Parameters of type constraint solving
data TypingParams = TypingParams {
  _condQualsGen :: Environment -> [Formula] -> QSpace,              -- ^ Qualifier generator for conditionals
  _matchQualsGen :: Environment -> [Formula] -> QSpace,             -- ^ Qualifier generator for match scrutinees
  _typeQualsGen :: Environment -> Formula -> [Formula] -> QSpace,   -- ^ Qualifier generator for types
  _predQualsGen :: Environment -> [Formula] -> [Formula] -> QSpace, -- ^ Qualifier generator for bound predicates
  _tcSolverUnfolding :: Bool, -- ^ Enable Prolog-style unfolding instead of predicate abstraction
  _tcSolverSplitMeasures :: Bool,
  _tcSolverLogLevel :: Int    -- ^ How verbose logging is  
}

makeLenses ''TypingParams

-- | State of type constraint solving
data TypingState = TypingState {
  -- Persistent state:
  _typingConstraints :: [Constraint],           -- ^ Typing constraints yet to be converted to horn clauses
  _typeAssignment :: TypeSubstitution,          -- ^ Current assignment to free type variables
  _predAssignment :: Substitution,              -- ^ Current assignment to free predicate variables  _qualifierMap :: QMap,
  _qualifierMap :: QMap,                        -- ^ Current state space for predicate unknowns
  _candidates :: [Candidate],                   -- ^ Current set of candidate liquid assignments to unknowns
  _initEnv :: Environment,                      -- ^ Initial environment
  _idCount :: Map String Int,                   -- ^ Number of unique identifiers issued so far
  _isFinal :: Bool,                             -- ^ Has the entire program been seen?
  -- Temporary state:
  _simpleConstraints :: [Constraint],           -- ^ Typing constraints that cannot be simplified anymore and can be converted to horn clauses or qualifier maps
  _hornClauses :: [(Formula, Id)],              -- ^ Horn clauses generated from subtyping constraints
  _consistencyChecks :: [Formula],              -- ^ Formulas generated from type consistency constraints
  _errorContext :: (SourcePos, Doc)             -- ^ Information to be added to all type errors
}

makeLenses ''TypingState

-- | Computations that solve type constraints, parametrized by the the horn solver @s@
type TCSolver s = StateT TypingState (ReaderT TypingParams (ExceptT ErrorMessage s))

-- | 'runTCSolver' @params st go@ : execute a typing computation @go@ with typing parameters @params@ in a typing state @st@
runTCSolver :: TypingParams -> TypingState -> TCSolver s a -> s (Either ErrorMessage (a, TypingState))
runTCSolver params st go = runExceptT $ runReaderT (runStateT go st) params  

-- | Initial typing state in the initial environment @env@
initTypingState :: MonadHorn s => Environment -> s TypingState
initTypingState env = do
  initCand <- initHornSolver env
  return $ TypingState {
    _typingConstraints = [],
    _typeAssignment = Map.empty,
    _predAssignment = Map.empty,
    _qualifierMap = Map.empty,
    _candidates = [initCand],
    _initEnv = env,
    _idCount = Map.empty,
    _isFinal = False,
    _simpleConstraints = [],
    _hornClauses = [],
    _consistencyChecks = [],
    _errorContext = (noPos, empty)
  }

-- | Impose typing constraint @c@ on the programs
addTypingConstraint c = over typingConstraints (nub . (c :))

-- | Solve @typingConstraints@: either strengthen the current candidates and return shapeless type constraints or fail
solveTypeConstraints :: MonadHorn s => TCSolver s ()
solveTypeConstraints = do
  simplifyAllConstraints
  
  scs <- use simpleConstraints
  writeLog 3 (text "Simple Constraints" $+$ (vsep $ map pretty scs))  
  
  processAllPredicates
  processAllConstraints
  generateAllHornClauses
  
  solveHornClauses
  checkTypeConsistency  
    
  hornClauses .= []
  consistencyChecks .= []
  
checkTypeConstraints :: MonadHorn s => TCSolver s ()
checkTypeConstraints = do
  simplifyAllConstraints
  
  scs <- use simpleConstraints
  writeLog 3 (text "Simple Constraints" $+$ (vsep $ map pretty scs))  
  
  processAllPredicates
  processAllConstraints
  generateAllHornClauses
  
  clauses <- use hornClauses
  env <- use initEnv
  qmap <- use qualifierMap
  cands <- lift . lift . lift $ checkCandidates False (map fst clauses) (instantiateConsAxioms env Nothing) [initialCandidate {solution = topSolution qmap}]
    
  hornClauses .= []
  consistencyChecks .= []
  
  when (null cands) (throwError $ text "Checking failed")
  
  
{- Repair-specific interface -}

getViolatingLabels :: MonadHorn s => TCSolver s (Set Id)
getViolatingLabels = do
  scs <- use simpleConstraints
  writeLog 2 (text "Simple Constraints" $+$ (vsep $ map pretty scs))

  processAllPredicates  
  processAllConstraints
  generateAllHornClauses
  
  clauses <- use hornClauses
  writeLog 2 (nest 2 $ text "All Horn clauses" $+$ vsep (map (\(fml, l) -> text l <> text ":" <+> pretty fml) clauses))        
  
  unfoldingEnabled <- asks _tcSolverUnfolding
  if unfoldingEnabled
    then do
      -- First try to solve as many clauses as possible syntactically via unfolding:
      stripTrivialClauses -- Remove clauses with head U, which does not occur in any bodies
      removeCyclic        -- Set solution for cyclic unknowns to true: dangerous!
      unfoldClauses       -- Prolog-style unfolding
    else return ()

  clauses' <- use hornClauses
  let (nontermClauses, termClauses) = partition isNonTerminal clauses'
  qmap <- use qualifierMap
  cands <- use candidates
  env <- use initEnv
  
  writeLog 2 (vsep [
    nest 2 $ text "Terminal Horn clauses" $+$ vsep (map (\(fml, l) -> text l <> text ":" <+> pretty fml) termClauses), 
    nest 2 $ text "Nonterminal Horn clauses" $+$ vsep (map (\(fml, l) -> text l <> text ":" <+> pretty fml) nontermClauses), 
    nest 2 $ text "QMap" $+$ pretty qmap])        
  
  (newCand:[]) <- lift . lift . lift $ refineCandidates (map fst nontermClauses) qmap (instantiateConsAxioms env Nothing) cands    
  candidates .= [newCand]
    
  invalidTerminals <- filterM (isInvalid newCand (instantiateConsAxioms env Nothing)) termClauses
  writeLog 2 (vsep [
    nest 2 $ text "Checking TERMINALS" $+$ vsep (map (\(fml, l) -> text l <> text ":" <+> pretty fml) termClauses), 
    nest 2 $ text "against solution" $+$ pretty newCand,
    nest 2 $ text "Invalid TERMINALS" $+$ vsep (map (\(fml, l) -> text l <> text ":" <+> pretty fml) invalidTerminals)
    ])
  
  hornClauses .= []
  
  return $ Set.fromList $ map snd invalidTerminals
  where
    isNonTerminal (Binary Implies _ (Unknown _ _), _) = True
    isNonTerminal _ = False
    
    isInvalid cand extractAssumptions (fml,_) = do
      cands' <- lift . lift . lift $ checkCandidates False [fml] extractAssumptions [cand]
      return $ null cands'
      
-- | Remove clauses with head U, which does not occur in any bodies
-- | or clauses where U occurs in the body but does not occur in any heads
stripTrivialClauses :: MonadHorn s => TCSolver s ()
stripTrivialClauses = do
  clauses <- use hornClauses
  
  -- Strip clauses with trivial heads
  let (trivialHeads, nontrivialHeads) = strip isTrivialHead [] clauses
  let topUnknowns = map (Set.findMax . posUnknowns . fst) trivialHeads
  setSolution $ Map.fromList (zip topUnknowns (repeat Set.empty))  
  
  -- Strip clauses with trivial bodies
  let (trivialBodies, nontrivial) = strip isTrivialBody [] nontrivialHeads
  let botUnknowns = Set.toList $ Set.unions $ map (negUnknowns . fst) trivialBodies
  setSolution $ Map.fromList (zip botUnknowns (repeat $ Set.singleton ffalse))  
  
  let trivial = trivialHeads ++ trivialBodies
  hornClauses .= nontrivial
  writeLog 2 (nest 2 $ text "Stripped trivial clauses" $+$ vsep (map (\(fml, l) -> text l <> text ":" <+> pretty fml) trivial))        
  
  where
    -- | Does `c' has an unknown in its head that is disjoint from all unknowns in bodies?
    isTrivialHead cs c = 
      let 
        heads = posUnknowns (fst c) 
        allNegUnknowns = Set.unions $ map (negUnknowns . fst) cs
      in not (Set.null heads) && (heads `disjoint` allNegUnknowns)
    -- | Does `c' has an unknown in its body that is disjoint from all unknowns in heads?
    isTrivialBody cs c =
      let
        bodyUs = Set.toList $ negUnknowns (fst c)
        allPosUnknowns = Set.unions $ map (posUnknowns . fst) cs
      in not $ all (`Set.member` allPosUnknowns) bodyUs
    strip isTrivial triv nontriv = 
      let (triv', nontriv') = partition (isTrivial nontriv) nontriv in
      if null triv'
        then (triv, nontriv) -- Fixpoint reached
        else strip isTrivial (triv ++ triv') nontriv'
        
-- | Set the solution for all cyclic variables to True
removeCyclic :: MonadHorn s => TCSolver s ()
removeCyclic = do
  clauses <- use hornClauses
  let cyclicUnknowns = Set.toList $ Set.unions $ map (findCyclic clauses) clauses
  let sol = Map.fromList (zip cyclicUnknowns (repeat Set.empty))      
  let clauses' = over (mapped._1) (applySolution sol) clauses
  hornClauses .= clauses'
  setSolution sol           -- Set solution to unfolded unknowns  
  writeLog 2 (nest 2 $ text "Removed cyclic unknowns" <+> pretty cyclicUnknowns)        
  
  where
    -- | All cyclic unknowns in the head of a clause
    findCyclic cs c = 
      let 
        us = heads c
        allDeps = findDeps cs Set.empty us
      in us `Set.intersection` allDeps
      
    findDeps cs acc us = 
      if Set.null us 
        then acc
        else let 
              depClauses = filter (\c -> not $ disjoint us (heads c)) cs
              newDeps = Set.unions (map (negUnknowns . fst) depClauses) Set.\\ acc
             in findDeps cs (newDeps `Set.union` acc) newDeps
        
    heads c = posUnknowns (fst c)
    

unfoldClauses :: MonadHorn s => TCSolver s ()
unfoldClauses = do
  clauses <- use hornClauses  
  
  let (toUnfold, rest) = partition canUnfold (groupHeads clauses)
  case toUnfold of
    [] -> return () -- No clauses to unfold anymore
    groups -> do -- Found clauses to unfold      
      sol <- Map.fromList <$> mapM unfoldGroup groups
      
      writeLog 2 (nest 2 $ vsep [
        text "Unfolded clauses" $+$ vsep (map (\(fml, l) -> text l <> text ":" <+> pretty fml) (concat groups)),
        text "Solution" $+$ pretty sol])              
      
      let clauses' = over (mapped._1) (applyToClause sol) (concat rest) -- Substitute unfolded unknowns
      hornClauses .= clauses'
      setSolution sol           -- Set solution to unfolded unknowns
      unfoldClauses
  where
    groupHeads cs =
      let heads c = posUnknowns $ rightHandSide $ fst c in
      groupBy ((==) `on` heads) $ sortBy (comparing heads) cs
  
    -- | Can a clause group be unfolded? Yes, if it's non-terminal and all LHS are fixed
    canUnfold cs@((Binary Implies _ (Unknown _ _), _):_) = all (\lhs -> Set.null $ posUnknowns lhs) (map (leftHandSide . fst) cs)
    canUnfold _ = False
    
    unfoldGroup cs = do
      disjuncts <- mapM (unfold . fst) cs
      if length disjuncts == 1
        then return $ head disjuncts
        else 
          let (common, disjucts') = extractCommonConjuncts (map snd disjuncts)
          in return (fst (head disjuncts), Set.insert (disjunction $ Set.fromList (map conjunction disjucts')) common)
    
    unfold (Binary Implies lhs rhs@(Unknown subst u)) = do
      quals <- use qualifierMap
      let uVars = (quals Map.! u) ^. variables -- Scope variables of `u`
      let rhsVars = Set.map (substitute subst) uVars -- Variables of the RHS, i.e. variables of `u` renamed according to `subst`
      let elimVars = varsOf lhs Set.\\ rhsVars -- Variables that have to be eliminated from LHS
      -- writeLog 2 (text "UVARS" <+> pretty uVars)
      let reverseSubst = Set.fold (\uvar rsub -> maybe rsub (\(Var _ name) -> Map.insert name uvar rsub) (Map.lookup (varName uvar) subst)) Map.empty uVars
      
      let lhsConjuncts = conjunctsOf $ substitute reverseSubst lhs      
      let (lhsConjuncts', elimVars') = Set.fold eliminate (lhsConjuncts, elimVars) elimVars -- Try to eliminate the existentials
      
      let (plainConjuncts, existentialConjuncts) = Set.partition (\c -> varsOf c `disjoint` elimVars') lhsConjuncts'
      let freshElimVars = Map.fromList $ map (\(Var s name) -> (name, Var s ("EE" ++ name))) (Set.toList elimVars')
      let existential = foldr (Quant Exists) (substitute freshElimVars $ conjunction existentialConjuncts) (Map.elems freshElimVars) -- Existentially quantify them away
      
      -- Add equalities implied by the substitution:
      let varPairs = [(v, v') | v <- Set.toList uVars, varName v `Map.member` subst, v' <- [subst Map.! varName v], v' `Set.member` uVars]
      let val = (if Set.null existentialConjuncts then id else Set.insert existential)
                  plainConjuncts `Set.union` (Set.fromList $ map (uncurry (|=|)) varPairs)
      
      return (u, val)
      
    eliminate :: Formula -> (Set Formula, Set Formula) -> (Set Formula, Set Formula)
    eliminate var (conjuncts, vars) = 
      case findDef var (map negationNF $ Set.toList conjuncts) of
        Nothing -> (conjuncts, vars)
        Just (c, def, Var _ _) -> (Set.map (substitute $ Map.singleton (varName var) def) (Set.delete c conjuncts), Set.delete var vars)
        Just (c, def, pred) -> (Set.map (substitutePredApp pred def) (Set.delete c conjuncts), Set.delete var vars)
        
    findDef :: Formula -> [Formula] -> Maybe (Formula, Formula, Formula)
    findDef _ [] = Nothing
    -- findDef var (c@(Binary Eq var' fml) : cs) | var == var' = Just (c, fml, var)
    -- findDef var (c@(Binary Eq fml var') : cs) | var == var' = Just (c, fml, var)
    findDef var (c@(Var BoolS _) : cs) | var == c = Just (c, ftrue, var)
    findDef var (c@(Unary Not v@(Var BoolS _)) : cs) | var == v = Just (c, ffalse, var)
    
    findDef var (c@(Binary Eq p fml) : cs) | isNestedPredApp var p  = Just (c, fml, p)
    findDef var (c@(Binary Eq fml p) : cs) | isNestedPredApp var p = Just (c, fml, p)
    
    findDef var (c : cs) = findDef var cs
    
    isNestedPredApp var var'@(Var _ _)      = var' == var
    isNestedPredApp var (Pred _ name [arg]) = isOnlyPred name && isNestedPredApp var arg
    isNestedPredApp _ _                   = False
    isOnlyPred name = name == "content" || name == "just"
        
    extractCommonConjuncts :: [Set Formula] -> (Set Formula, [Set Formula])
    extractCommonConjuncts disjuncts = 
      let d = head disjuncts in
      Set.fold (\c (cs, ds) -> if all (Set.member c) ds then (Set.insert c cs, map (Set.delete c) ds) else (cs, ds)) (Set.empty, disjuncts) d
      
    applyToClause sol (Binary Implies lhs rhs) =
      let lhs' = conjunction $ conjunctsOf $ applySolution sol lhs -- nub conjuncts
      in Binary Implies lhs' rhs      
            
    substitutePredApp from to fml = case fml of
      SetLit b elems -> SetLit b $ map (substitutePredApp from to) elems
      MapSel m k -> MapSel (substitutePredApp from to m) (substitutePredApp from to k)
      MapUpd m k v -> MapUpd (substitutePredApp from to m) (substitutePredApp from to k) (substitutePredApp from to v)
      Unary op e -> Unary op (substitutePredApp from to e)
      Binary op e1 e2 -> Binary op (substitutePredApp from to e1) (substitutePredApp from to e2)
      Ite e0 e1 e2 -> Ite (substitutePredApp from to e0) (substitutePredApp from to e1) (substitutePredApp from to e2)
      Pred b name args -> if fml == from then to else Pred b name $ map (substitutePredApp from to) args
      Cons b name args -> Cons b name $ map (substitutePredApp from to) args  
      Quant q v@(Var _ x) e -> if v `Set.member` varsOf from
                                then error $ unwords ["Scoped variable clashes with substitution variable", x]
                                else Quant q v (substitutePredApp from to e)
      otherwise -> fml
      
      
-- | Reset the solution for a subset of unknowns to `sol' in the current (sole) candidate      
setSolution :: MonadHorn s => Solution -> TCSolver s ()
setSolution sol = do
  cand <- head <$> use candidates
  candidates .= [cand {solution = sol `Map.union` solution cand}]  
      
{- Implementation -}      
      
-- | Decompose and unify typing constraints; 
-- return shapeless type constraints: constraints involving only free type variables, which impose no restrictions yet, but might in the future
simplifyAllConstraints :: MonadHorn s => TCSolver s () 
simplifyAllConstraints = do
  tcs <- use typingConstraints
  writeLog 3 (text "Typing Constraints" $+$ (vsep $ map pretty tcs))
  typingConstraints .= []
  tass <- use typeAssignment
  mapM_ simplifyConstraint tcs
    
  -- If type assignment has changed, we might be able to process more shapeless constraints:  
  tass' <- use typeAssignment
  writeLog 3 (text "Type assignment" $+$ vMapDoc text pretty tass')
  
  when (Map.size tass' > Map.size tass) simplifyAllConstraints
  
-- | Assign unknowns to all free predicate variables  
processAllPredicates :: MonadHorn s => TCSolver s ()
processAllPredicates = do
  tcs <- use typingConstraints
  typingConstraints .= []
  mapM_ processPredicate tcs
  
  pass <- use predAssignment
  writeLog 3 (text "Pred assignment" $+$ vMapDoc text pretty pass)
      
-- | Eliminate type and predicate variables, generate qualifier maps
processAllConstraints :: MonadHorn s => TCSolver s ()
processAllConstraints = do  
  tcs <- use simpleConstraints
  simpleConstraints .= []
  mapM_ processConstraint tcs
    
-- | Convert simple subtyping constraints into horn clauses
generateAllHornClauses :: MonadHorn s => TCSolver s ()
generateAllHornClauses = do
  tcs <- use simpleConstraints
  simpleConstraints .= []
  mapM_ generateHornClauses tcs
  
-- | Signal type error  
throwError :: MonadHorn s => Doc -> TCSolver s ()  
throwError msg = do
  (pos, ec) <- use errorContext
  lift $ lift $ throwE $ ErrorMessage TypeError pos (msg $+$ ec)

-- | Refine the current liquid assignments using the horn clauses
solveHornClauses :: MonadHorn s => TCSolver s ()
solveHornClauses = do
  clauses <- use hornClauses
  qmap <- use qualifierMap
  cands <- use candidates
  env <- use initEnv
  cands' <- lift . lift . lift $ refineCandidates (map fst clauses) qmap (instantiateConsAxioms env Nothing) cands
    
  when (null cands') (throwError $ text "Cannot find sufficiently strong refinements")
  candidates .= cands'
  
solveAllCandidates :: MonadHorn s => TCSolver s ()  
solveAllCandidates = do
  cands <- use candidates
  cands' <- concat <$> mapM solveCandidate cands
  candidates .= cands'
  where
    solveCandidate c@(Candidate s valids invalids _) = 
      if Set.null invalids
        then return [c]
        else do
          qmap <- use qualifierMap
          env <- use initEnv        
          cands' <- lift . lift . lift $ refineCandidates [] qmap (instantiateConsAxioms env Nothing) [c]
          concat <$> mapM solveCandidate cands'

-- | Filter out liquid assignments that are too strong for current consistency checks  
checkTypeConsistency :: MonadHorn s => TCSolver s ()  
checkTypeConsistency = do
  clauses <- use consistencyChecks
  cands <- use candidates
  env <- use initEnv  
  cands' <- lift . lift . lift $ checkCandidates True clauses (instantiateConsAxioms env Nothing) cands
  when (null cands') (throwError $ text "Found inconsistent refinements")
  candidates .= cands'

-- | Simplify @c@ into a set of simple and shapeless constraints, possibly extended the current type assignment or predicate assignment
simplifyConstraint :: MonadHorn s => Constraint -> TCSolver s ()
simplifyConstraint c = do
  tass <- use typeAssignment
  pass <- use predAssignment
  simplifyConstraint' tass pass c

-- Any type: drop
simplifyConstraint' _ _ (Subtype _ _ AnyT _ _) = return ()
simplifyConstraint' _ _ c@(Subtype _ AnyT _ _ _) = return ()
simplifyConstraint' _ _ c@(WellFormed _ AnyT) = return ()
-- Any datatype: drop only if lhs is a datatype
simplifyConstraint' _ _ (Subtype _ (ScalarT (DatatypeT _ _ _) _) t _ _) | t == anyDatatype = return ()
-- Well-formedness of a known predicate drop  
simplifyConstraint' _ pass c@(WellFormedPredicate _ _ p) | p `Map.member` pass = return ()
  
-- Type variable with known assignment: substitute
simplifyConstraint' tass _ (Subtype env tv@(ScalarT (TypeVarT _ a) _) t consistent label) | a `Map.member` tass
  = simplifyConstraint (Subtype env (typeSubstitute tass tv) t consistent label)
simplifyConstraint' tass _ (Subtype env t tv@(ScalarT (TypeVarT _ a) _) consistent label) | a `Map.member` tass
  = simplifyConstraint (Subtype env t (typeSubstitute tass tv) consistent label)
simplifyConstraint' tass _ (WellFormed env tv@(ScalarT (TypeVarT _ a) _)) | a `Map.member` tass
  = simplifyConstraint (WellFormed env (typeSubstitute tass tv))
  
-- Two unknown free variables: nothing can be done for now
simplifyConstraint' _ _ c@(Subtype env (ScalarT (TypeVarT _ a) _) (ScalarT (TypeVarT _ b) _) _ _) | not (isBound env a) && not (isBound env b)
  = if a == b
      then error $ show $ text "simplifyConstraint: equal type variables on both sides"
      else ifM (use isFinal) 
            (do -- This is a final pass: assign an arbitrary type to one of the variables
              addTypeAssignment a intAll
              simplifyConstraint c) 
            (modify $ addTypingConstraint c)
simplifyConstraint' _ _ c@(WellFormed env (ScalarT (TypeVarT _ a) _)) | not (isBound env a) 
  = modify $ addTypingConstraint c
simplifyConstraint' _ _ c@(WellFormedPredicate _ _ _) = modify $ addTypingConstraint c

-- Let types: extend environment (has to be done before trying to extend the type assignment)
simplifyConstraint' _ _ (Subtype env (LetT x tDef tBody) t consistent label)
  = do
      y <- freshVar env x      
      simplifyConstraint (Subtype (addVariable y tDef env) (renameVar (isBound env) x y tDef tBody) t consistent label)
simplifyConstraint' _ _ (Subtype env t (LetT x tDef tBody) consistent label)
  = do
      y <- freshVar env x      
      simplifyConstraint (Subtype (addVariable y tDef env) t (renameVar (isBound env) x y tDef tBody) consistent label) -- ToDo: make x unique? 
  
-- Unknown free variable and a type: extend type assignment
simplifyConstraint' _ _ c@(Subtype env (ScalarT (TypeVarT _ a) _) t _ _) | not (isBound env a) 
  = unify env a t >> simplifyConstraint c
simplifyConstraint' _ _ c@(Subtype env t (ScalarT (TypeVarT _ a) _) _ _) | not (isBound env a) 
  = unify env a t >> simplifyConstraint c

-- Compound types: decompose
simplifyConstraint' _ _ (Subtype env (ScalarT (DatatypeT name (tArg:tArgs) pArgs) fml) (ScalarT (DatatypeT name' (tArg':tArgs') pArgs') fml') consistent label)
  = do
      simplifyConstraint (Subtype env tArg tArg' consistent label)
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name tArgs pArgs) fml) (ScalarT (DatatypeT name' tArgs' pArgs') fml') consistent label)
simplifyConstraint' _ _ (Subtype env (ScalarT (DatatypeT name [] (pArg:pArgs)) fml) (ScalarT (DatatypeT name' [] (pArg':pArgs')) fml') consistent label)
  = do
      let predParams = _predParams ((env ^. datatypes) Map.! name)
      let variance = snd $ predParams !! (length predParams - length pArgs - 1)
      case variance of
        Co -> simplifyConstraint (Subtype env (int $ pArg) (int $ pArg') consistent label)
        Contra -> simplifyConstraint (Subtype env (int $ pArg') (int $ pArg) consistent label)
        Inv -> do
                simplifyConstraint (Subtype env (int $ pArg) (int $ pArg') consistent label)
                simplifyConstraint (Subtype env (int $ pArg') (int $ pArg) consistent label)
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name [] pArgs) fml) (ScalarT (DatatypeT name' [] pArgs') fml') consistent label)      
simplifyConstraint' _ _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) False label)
  = do
      simplifyConstraint (Subtype env tArg2 tArg1 False label)
      if isScalarType tArg1
        then simplifyConstraint (Subtype (addVariable y tArg2 env) (renameVar (isBound env) x y tArg1 tRes1) tRes2 False label)
        else simplifyConstraint (Subtype env tRes1 tRes2 False label)
simplifyConstraint' _ _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) True label)
  = if isScalarType tArg1
      then simplifyConstraint (Subtype (addVariable x tArg1 env) tRes1 tRes2 True label)
      else simplifyConstraint (Subtype env tRes1 tRes2 True label)
simplifyConstraint' _ _ c@(WellFormed env (ScalarT (DatatypeT name tArgs _) fml))
  = do
      mapM_ (simplifyConstraint . WellFormed env) tArgs
      simpleConstraints %= (c :)
simplifyConstraint' _ _ (WellFormed env (FunctionT x tArg tRes))
  = do
      simplifyConstraint (WellFormed env tArg)
      simplifyConstraint (WellFormed (addVariable x tArg env) tRes)
simplifyConstraint' _ _ (WellFormed env (LetT x tDef tBody))
  = simplifyConstraint (WellFormed (addVariable x tDef env) tBody)

-- Simple constraint: return
simplifyConstraint' _ _ c@(Subtype _ (ScalarT baseT _) (ScalarT baseT' _) _ _) | baseT == baseT' = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormed _ (ScalarT baseT _)) = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormedCond _ _) = simpleConstraints %= (c :)
simplifyConstraint' _ _ c@(WellFormedMatchCond _ _) = simpleConstraints %= (c :)
-- Otherwise (shape mismatch): fail
simplifyConstraint' _ _ (Subtype _ t t' _ _) = 
  throwError $ text  "Cannot match shape" <+> squotes (pretty $ shape t) $+$ text "with shape" <+> squotes (pretty $ shape t')

-- | Unify type variable @a@ with type @t@ or fail if @a@ occurs in @t@
unify env a t = if a `Set.member` typeVarsOf t
  then error $ show $ text "simplifyConstraint: type variable occurs in the other type"
  else do
    t' <- fresh env t
    writeLog 3 (text "UNIFY" <+> text a <+> text "WITH" <+> pretty t <+> text "PRODUCING" <+> pretty t')
    addTypeAssignment a t'
    
-- Predicate well-formedness: shapeless or simple depending on type variables  
processPredicate c@(WellFormedPredicate env argSorts p) = do
  tass <- use typeAssignment
  let typeVars = Set.toList $ Set.unions $ map typeVarsOfSort argSorts
  if any (isFreeVariable tass) typeVars
    then do
      writeLog 3 $ text "WARNING: free vars in predicate" <+> pretty c
      modify $ addTypingConstraint c -- Still has type variables: cannot determine shape
    else do                 
      -- u <- freshId "U"
      let u = p
      addPredAssignment p (Unknown Map.empty u)
      let argSorts' = map (sortSubstitute $ asSortSubst tass) argSorts
      let args = zipWith Var argSorts' deBrujns
      let env' = typeSubstituteEnv tass env
      let vars = allScalars env'
      pq <- asks _predQualsGen
      addQuals u (pq (addAllVariables args env') args vars)
  where
    isFreeVariable tass a = not (isBound env a) && not (Map.member a tass)
processPredicate c = modify $ addTypingConstraint c

-- | Eliminate type and predicate variables from simple constraints, create qualifier maps, split measure-based subtyping constraints
processConstraint :: MonadHorn s => Constraint -> TCSolver s ()
processConstraint c@(Subtype env (ScalarT baseTL l) (ScalarT baseTR r) False label) | baseTL == baseTR
  = if l == ffalse || r == ftrue
      then return ()
      else do
        tass <- use typeAssignment
        pass <- use predAssignment
        let subst = sortSubstituteFml (asSortSubst tass) . substitutePredicate pass
        let l' = subst l
        let r' = subst r
        let c' = Subtype env (ScalarT baseTL l') (ScalarT baseTR r') False label
        if Set.null $ (predsOf l' `Set.union` predsOf r') Set.\\ (Map.keysSet $ allPredicates env)
            then case baseTL of -- Subtyping of datatypes: try splitting into individual constraints between measures
                  DatatypeT dtName _ _ -> do
                    let measures = Map.keysSet $ allMeasuresOf dtName env
                    let isAbstract = null $ ((env ^. datatypes) Map.! dtName) ^. constructors
                    let vals = filter (\v -> varName v == valueVarName) . Set.toList . varsOf $ r'
                    let rConjuncts = conjunctsOf r'
                    doSplit <- asks _tcSolverSplitMeasures
                    if not doSplit || isAbstract || null vals || (not . Set.null . unknownsOf) (l' |&| r') -- TODO: unknowns can be split if we know their potential valuations
                      then simpleConstraints %= (c' :) -- Constraint has unknowns (or RHS doesn't contain _v)
                      else case splitByPredicate measures (head vals) (Set.toList rConjuncts) of
                            Nothing -> simpleConstraints %= (c' :) -- RHS cannot be split, add whole thing
                            Just mr -> if rConjuncts `Set.isSubsetOf` (Set.unions $ Map.elems mr)
                                        then do
                                          let lConjuncts = conjunctsOf $ instantiateCons (head vals) l'
                                          case splitByPredicate measures (head vals) (Set.toList lConjuncts) of -- Every conjunct of RHS is about some `m _v` (where m in measures)
                                              Nothing -> simpleConstraints %= (c' :) -- LHS cannot be split, add whole thing for now
                                              Just ml -> mapM_ (addSplitConstraint ml) (toDisjointGroups mr)
                                        else simpleConstraints %= (c' :) -- Some conjuncts of RHS are no covered (that is, do not contains _v), add whole thing                       
                  _ -> simpleConstraints %= (c' :)
          else modify $ addTypingConstraint c -- Constraint contains free predicate: add back and wait until more type variables get unified, so predicate variables can be instantiated
  where
    instantiateCons val fml@(Binary Eq v (Cons _ _ _)) | v == val = conjunction $ instantiateConsAxioms env (Just val) fml
    instantiateCons _ fml = fml
    
    addSplitConstraint :: MonadHorn s => Map Id (Set Formula) -> (Set Id, Set Formula) -> TCSolver s ()
    addSplitConstraint ml (measures, rConjuncts) = do
      let rhs = conjunction rConjuncts
      let lhs = conjunction $ setConcatMap (\measure -> Map.findWithDefault Set.empty measure ml) measures
      let c' = Subtype env (ScalarT baseTL lhs) (ScalarT baseTR rhs) False label
      writeLog 3 $ text "addSplitConstraint" <+> pretty c'
      simpleConstraints %= (c' :)    
      
processConstraint (Subtype env (ScalarT baseTL l) (ScalarT baseTR r) True label) | baseTL == baseTR
  = do
      tass <- use typeAssignment
      pass <- use predAssignment
      let subst = sortSubstituteFml (asSortSubst tass) . substitutePredicate pass
      let l' = subst l
      let r' = subst r
      if l' == ftrue || r' == ftrue
        then return ()
        else simpleConstraints %= (Subtype env (ScalarT baseTL l') (ScalarT baseTR r') True label :)
processConstraint (WellFormed env t@(ScalarT baseT fml)) 
  = case fml of
      Unknown _ u -> do
        qmap <- use qualifierMap
        tass <- use typeAssignment
        tq <- asks _typeQualsGen
        -- Only add qualifiers if it's a new variable; multiple well-formedness constraints could have been added for constructors
        let env' = typeSubstituteEnv tass env
        let env'' = addVariable valueVarName t env'
        when (not $ Map.member u qmap) $ addQuals u (tq env'' (Var (toSort baseT) valueVarName) (allScalars env'))
      _ -> return ()
processConstraint (WellFormedCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      cq <- asks _condQualsGen
      let env' = typeSubstituteEnv tass env
      addQuals u (cq env' (allScalars env'))
processConstraint (WellFormedMatchCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      mq <- asks _matchQualsGen
      let env' = typeSubstituteEnv tass env
      addQuals u (mq env' (allPotentialScrutinees env'))
processConstraint c = error $ show $ text "processConstraint: not a simple constraint" <+> pretty c

generateHornClauses :: MonadHorn s => Constraint -> TCSolver s ()
generateHornClauses c@(Subtype env (ScalarT baseTL l) (ScalarT baseTR r) False label) | baseTL == baseTR
  = do
      qmap <- use qualifierMap
      let relevantVars = potentialVars qmap (l |&| r)
      emb <- embedding env relevantVars True
      clauses <- lift . lift . lift $ preprocessConstraint (conjunction (Set.insert l emb) |=>| r)
      hornClauses %= (zip clauses (repeat label) ++)
generateHornClauses (Subtype env (ScalarT baseTL l) (ScalarT baseTR r) True _) | baseTL == baseTR
  = do
      qmap <- use qualifierMap
      let relevantVars = potentialVars qmap (l |&| r)
      emb <- embedding env relevantVars False
      let clause = conjunction (Set.insert l $ Set.insert r emb)
      consistencyChecks %= (clause :)
generateHornClauses c = error $ show $ text "generateHornClauses: not a simple subtyping constraint" <+> pretty c          

-- | 'allScalars' @env@ : logic terms for all scalar symbols in @env@
allScalars :: Environment -> [Formula]
allScalars env = catMaybes $ map toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (_, ForallT _ _) = Nothing
    toFormula (x, _) | x `Set.member` (env ^. letBound) = Nothing
    toFormula (x, Monotype t) = case t of
      ScalarT IntT  (Binary Eq _ (IntLit n)) -> Just $ IntLit n
      ScalarT BoolT (Var _ _) -> Just $ BoolLit True
      ScalarT BoolT (Unary Not (Var _ _)) -> Just $ BoolLit False
      ScalarT (DatatypeT dt [] []) (Binary Eq _ cons@(Cons _ name [])) | x == name -> Just cons
      ScalarT b _ -> Just $ Var (toSort b) x
      _ -> Nothing    
    
-- | 'allPotentialScrutinees' @env@ : logic terms for all scalar symbols in @env@
allPotentialScrutinees :: Environment -> [Formula]
allPotentialScrutinees env = catMaybes $ map toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (x, Monotype t) = case t of
      ScalarT b@(DatatypeT _ _ _) _ ->
        if Set.member x (env ^. unfoldedVars) && not (Program (PSymbol x) t `elem` (env ^. usedScrutinees))
          then Just $ Var (toSort b) x
          else Nothing
      _ -> Nothing 
    toFormula _ = Nothing
    
hasPotentialScrutinees :: Monad s => Environment -> TCSolver s Bool
hasPotentialScrutinees env = do
  tass <- use typeAssignment
  return $ not $ null $ allPotentialScrutinees (typeSubstituteEnv tass env)
  
-- | Assumptions encoded in an environment    
embedding :: Monad s => Environment -> Set Id -> Bool -> TCSolver s (Set Formula)
embedding env vars includeQuantified = do
    tass <- use typeAssignment
    pass <- use predAssignment
    qmap <- use qualifierMap
    let ass = Set.map (substitutePredicate pass) $ (env ^. assumptions)
    let allVars = vars `Set.union` potentialVars qmap (conjunction ass)
    return $ addBindings env tass pass qmap ass allVars    
  where
    addBindings env tass pass qmap fmls vars = 
      if Set.null vars
        then fmls
        else let (x, rest) = Set.deleteFindMin vars in
              case Map.lookup x (allSymbols env) of
                Nothing -> addBindings env tass pass qmap fmls rest -- Variable not found (useful to ignore value variables)
                Just (Monotype t) -> case typeSubstitute tass t of
                  ScalarT baseT fml -> 
                    let fmls' = Set.fromList $ map (substitute (Map.singleton valueVarName (Var (toSort baseT) x)) . substitutePredicate pass)
                                          (fml : allMeasurePostconditions includeQuantified baseT env) in
                    let newVars = Set.delete x $ setConcatMap (potentialVars qmap) fmls' in
                    addBindings env tass pass qmap (fmls `Set.union` fmls') (rest `Set.union` newVars)
                  LetT y tDef tBody -> addBindings (addVariable x tBody . addVariable y tDef . removeVariable x $ env) tass pass qmap fmls vars
                  AnyT -> Set.singleton ffalse
                  _ -> error $ unwords ["embedding: encountered non-scalar variable", x, "in 0-arity bucket"]
                Just sch -> addBindings env tass pass qmap fmls rest -- TODO: why did this work before?
    allSymbols env = symbolsOfArity 0 env

-- -- | 'potentialVars' @qmap fml@ : variables of @fml@ if all unknowns get strongest valuation according to @quals@    
potentialVars :: QMap -> Formula -> Set Id
-- potentialVars qmap fml = Set.map varName $ varsOf $ bottomValuation qmap fml
potentialVars qmap fml = Set.map varName $ setConcatMap varsOf $
                            bottomValuation qmap fml `Set.insert` Set.unions (map (lookupVarsSubst qmap) unknowns)
  where
    unknowns = Set.toList $ unknownsOf fml
    bottomValuation qmap fml = applySolution bottomSolution fml
    bottomSolution = Map.fromList $ zip (map unknownName unknowns) (map (Set.fromList . lookupQualsSubst qmap) unknowns)

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: Monad s => String -> TCSolver s String
freshId prefix = do
  i <- uses idCount (Map.findWithDefault 0 prefix)
  idCount %= Map.insert prefix (i + 1)
  return $ prefix ++ show i
  
freshVar :: Monad s => Environment -> String -> TCSolver s String 
freshVar env prefix = do
  x <- freshId prefix
  if Map.member x (allSymbols env)
    then freshVar env prefix
    else return x

-- | 'fresh' @t@ : a type with the same shape as @t@ but fresh type variables, fresh predicate variables, and fresh unknowns as refinements
fresh :: Monad s => Environment -> RType -> TCSolver s RType
fresh env (ScalarT (TypeVarT vSubst a) _) | not (isBound env a) = do
  -- Free type variable: replace with fresh free type variable
  a' <- freshId "A"
  return $ ScalarT (TypeVarT vSubst a') ftrue
fresh env (ScalarT baseT _) = do
  baseT' <- freshBase baseT
  -- Replace refinement with fresh predicate unknown:
  k <- freshId "U"
  return $ ScalarT baseT' (Unknown Map.empty k)
  where
    freshBase (DatatypeT name tArgs _) = do
      -- Replace type arguments with fresh types:
      tArgs' <- mapM (fresh env) tArgs
      -- Replace predicate arguments with fresh predicate variables:
      let (DatatypeDef tParams pParams _ _) = (env ^. datatypes) Map.! name
      pArgs' <- mapM (\sig -> freshPred env . map (noncaptureSortSubst tParams (map (toSort . baseTypeOf) tArgs')) . predSigArgSorts . fst $ sig) pParams  
      return $ DatatypeT name tArgs' pArgs'
    freshBase baseT = return baseT
fresh env (FunctionT x tArg tFun) = do
  liftM2 (FunctionT x) (fresh env tArg) (fresh env tFun)
fresh env t = let (env', t') = embedContext env t in fresh env' t'
  
freshPred env sorts = do
  p' <- freshId "P"
  modify $ addTypingConstraint (WellFormedPredicate env sorts p')
  let args = zipWith Var sorts deBrujns 
  return $ Pred BoolS p' args  
  
addTypeAssignment tv t = typeAssignment %= Map.insert tv t
addPredAssignment p fml = predAssignment %= Map.insert p fml  
  
addQuals :: MonadHorn s => Id -> QSpace -> TCSolver s ()
addQuals name quals = do
  quals' <- lift . lift . lift $ pruneQualifiers quals
  qualifierMap %= Map.insert name quals'
  
-- | Add unknown @name@ with valuation @valuation@ to solutions of all candidates  
addFixedUnknown :: MonadHorn s => Id -> Set Formula -> TCSolver s ()  
addFixedUnknown name valuation = do
    let quals = Set.toList valuation
    addQuals name (toSpace Nothing (Set.unions $ map varsOf quals) quals)
    candidates %= map update
  where
    update cand = cand { solution = Map.insert name valuation (solution cand) }
    
-- | Set valuation of unknown @name@ to @valuation@
-- and re-check all potentially affected constraints in all candidates 
setUnknownRecheck :: MonadHorn s => Id -> Set Formula -> Set Id -> TCSolver s ()
setUnknownRecheck name valuation duals = do
  writeLog 3 $ text "Re-checking candidates after updating" <+> text name
  cands@(cand:_) <- use candidates
  let clauses = Set.filter (\fml -> name `Set.member` (Set.map unknownName (unknownsOf fml))) (validConstraints cand) -- First candidate cannot have invalid constraints
  let cands' = map (\c -> c { solution = Map.insert name valuation (solution c) }) cands
  env <- use initEnv
  cands'' <- lift . lift . lift $ checkCandidates False (Set.toList clauses) (instantiateConsAxioms env Nothing) cands'
    
  if null cands''
    then throwError $ text "Re-checking candidates failed"
    else do
      let liveClauses = Set.filter (\fml -> duals `disjoint` (Set.map unknownName (unknownsOf fml))) (validConstraints cand)
      candidates .= map (\c -> c { 
                                  validConstraints = Set.intersection liveClauses (validConstraints c), 
                                  invalidConstraints = Set.intersection liveClauses (invalidConstraints c) }) cands'' -- Remove Horn clauses produced by now eliminated code
  
-- | 'instantiateConsAxioms' @env fml@ : If @fml@ contains constructor applications, return the set of instantiations of constructor axioms for those applications in the environment @env@ 
instantiateConsAxioms :: Environment -> Maybe Formula -> Formula -> Set Formula  
instantiateConsAxioms env mVal fml = let inst = instantiateConsAxioms env mVal in
  case fml of
    Cons resS@(DataS dtName _) ctor args -> Set.unions $ Set.fromList (map (measureAxiom resS ctor args) (Map.elems $ allMeasuresOf dtName env)) : 
                                                         map (instantiateConsAxioms env Nothing) args
    Unary op e -> inst e
    Binary op e1 e2 -> inst e1 `Set.union` inst e2
    Ite e0 e1 e2 -> inst e0 `Set.union` inst e1 `Set.union` inst e2
    SetLit _ elems -> Set.unions (map inst elems)
    SetComp _ e -> inst e
    MapSel m k -> inst m `Set.union` inst k
    MapUpd m k v -> inst m `Set.union` inst k `Set.union` inst v
    Pred _ p args -> Set.unions $ map inst args
    -- Why was this here? It's unsound in the presence of disjunctions
    -- Quant Exists v e -> Set.singleton (Quant Exists v (conjunction (Set.insert e $ inst e)))
    _ -> Set.empty  
  where
    measureAxiom resS ctor args (MeasureDef inSort _ defs _) = 
      let 
        MeasureCase _ vars body = head $ filter (\(MeasureCase c _ _) -> c == ctor) defs
        sParams = map varSortName (sortArgsOf inSort) -- sort parameters in the datatype declaration
        sArgs = sortArgsOf resS -- actual sort argument in the constructor application
        body' = noncaptureSortSubstFml sParams sArgs body -- measure definition with actual sorts for all subexpressions
        newValue = case mVal of
                      Nothing -> Cons resS ctor args
                      Just val -> val
        subst = Map.fromList $ (valueVarName, newValue) : zip vars args -- substitute formals for actuals and constructor application or provided value for _v    
      in substitute subst body'
    
-- | 'matchConsType' @formal@ @actual@ : unify constructor return type @formal@ with @actual@
matchConsType formal@(ScalarT (DatatypeT d vars pVars) _) actual@(ScalarT (DatatypeT d' args pArgs) _) | d == d' 
  = do
      writeLog 3 $ text "Matching constructor type" $+$ pretty formal $+$ text "with scrutinee" $+$ pretty actual
      zipWithM_ (\(ScalarT (TypeVarT _ a) (BoolLit True)) t -> addTypeAssignment a t) vars args
      zipWithM_ (\(Pred BoolS p _) fml -> addPredAssignment p fml) pVars pArgs
matchConsType t t' = error $ show $ text "matchConsType: cannot match" <+> pretty t <+> text "against" <+> pretty t'
    
currentAssignment :: Monad s => RType -> TCSolver s RType
currentAssignment t = do
  tass <- use typeAssignment
  pass <- use predAssignment
  return $ (typeSubstitutePred pass . typeSubstitute tass) t
    
-- | Substitute type variables, predicate variables, and predicate unknowns in @t@
-- using current type assignment, predicate assignment, and liquid assignment
finalizeType :: Monad s => RType -> TCSolver s RType
finalizeType t = do
  tass <- use typeAssignment
  pass <- use predAssignment
  sol <- uses candidates (solution . head)
  return $ (typeApplySolution sol . typeSubstitutePred pass . typeSubstitute tass) t
    
-- | Substitute type variables, predicate variables, and predicate unknowns in @p@
-- using current type assignment, predicate assignment, and liquid assignment
finalizeProgram :: Monad s => RProgram -> TCSolver s RProgram
finalizeProgram p = do
  tass <- use typeAssignment
  pass <- use predAssignment
  sol <- uses candidates (solution . head)
  return $ fmap (typeApplySolution sol . typeSubstitutePred pass . typeSubstitute tass) p
  
instance Eq TypingState where
  (==) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (_idCount st1) == restrictDomain (Set.fromList ["a", "u"]) (_idCount st2)) &&
                  _typeAssignment st1 == _typeAssignment st2 &&
                  _candidates st1 == _candidates st2

instance Ord TypingState where
  (<=) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (_idCount st1) <= restrictDomain (Set.fromList ["a", "u"]) (_idCount st2)) &&
                _typeAssignment st1 <= _typeAssignment st2 &&
                _candidates st1 <= _candidates st2  
  
writeLog level msg = do
  maxLevel <- asks _tcSolverLogLevel
  if level <= maxLevel then traceShow (plain msg) $ return () else return ()
  
