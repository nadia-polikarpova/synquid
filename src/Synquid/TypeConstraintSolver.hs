{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

-- | Incremental solving of subtyping and well-formedness constraints
module Synquid.TypeConstraintSolver (
  QualsGen,
  emptyGen,
  TypingParams (..),
  TypingState (..),
  typeAssignment,
  candidates,
  TCSolver,
  runTCSolver,
  initTypingState,
  solveTypeConstraints,
  matchConsType,
  isEnvironmentInconsistent,
  freshId  
) where

import Synquid.Logic
import Synquid.Program
import Synquid.Pretty
import Synquid.SolverMonad
import Synquid.Util

import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Applicative
import Control.Lens hiding (both)
import Debug.Trace

{- Interface -}

-- | State space generator (returns a state space for a list of symbols in scope)
type QualsGen = (Environment, [Formula]) -> QSpace

-- | Empty state space generator
emptyGen = const emptyQSpace

data TypingParams = TypingParams {
  _condQualsGen :: QualsGen,              -- ^ Qualifier generator for conditionals
  _matchQualsGen :: QualsGen,             -- ^ Qualifier generator for match scrutinees
  _typeQualsGen :: QualsGen,              -- ^ Qualifier generator for types
  _tcSolverLogLevel :: Int                -- ^ How verbose logging is  
}

makeLenses ''TypingParams

data TypingState = TypingState {
  _typeAssignment :: TypeSubstitution,
  _predAssignment :: Substitution,
  _qualifierMap :: QMap,
  _candidates :: [Candidate],
  _initEnv :: Environment,
  _idCount :: Map String Int                   -- ^ Number of unique identifiers issued so far
}

makeLenses ''TypingState

type TCSolver s = StateT TypingState (ReaderT TypingParams (MaybeT s))

runTCSolver :: TypingParams -> TypingState -> TCSolver s a -> s (Maybe (a, TypingState))
runTCSolver params st go = runMaybeT $ runReaderT (runStateT go st) params  

initTypingState :: MonadHorn s => Environment -> s TypingState
initTypingState env = do
  initCand <- initHornSolver
  return $ TypingState {
    _typeAssignment = Map.empty,
    _predAssignment = Map.empty,
    _qualifierMap = Map.empty,
    _candidates = [initCand],
    _initEnv = env,
    _idCount = Map.empty
  }

-- | Solve @typeConstraints@: either strengthen the current candidates and return shapeless type constraints or fail
solveTypeConstraints :: MonadHorn s => [Constraint] -> TCSolver s [Constraint]
solveTypeConstraints typeConstraints = do
  writeLog 1 (text "Typing Constraints" $+$ (vsep $ map pretty typeConstraints))
  (simple, shapeless) <- simplifyAllConstraints typeConstraints
        
  tass <- use typeAssignment
  writeLog 1 (text "Type assignment" $+$ vMapDoc text pretty tass)        
  pass <- use predAssignment
  writeLog 1 (text "Pred assignment" $+$ vMapDoc text pretty pass)        
  
  (hornClauses, consistencyChecks) <- processAllConstraints simple
  solveHornClauses hornClauses
  checkTypeConsistency consistencyChecks
  return shapeless
      
{- Implementation -}      
      
-- | Decompose and unify typing constraints; 
-- return shapeless type constraints: constraints involving only free type variables, which impose no restrictions yet, but might in the future
simplifyAllConstraints :: MonadHorn s => [Constraint] -> TCSolver s ([Constraint], [Constraint]) 
simplifyAllConstraints tcs = do
  tass <- use typeAssignment
  (simple, shapeless) <- both concat . unzip <$> mapM simplifyConstraint tcs  
  
  -- If type assignment has changed, we might be able to process more shapeless constraints:
  tass' <- use typeAssignment
  (simple', shapeless') <- if Map.size tass' > Map.size tass
    then simplifyAllConstraints shapeless
    else return ([], [])
    
  return (simple' ++ simple, shapeless' ++ shapeless)
    
-- | Convert simple typing constraints into horn clauses and qualifier maps
processAllConstraints :: MonadHorn s => [Constraint] -> TCSolver s ([Formula], [Formula]) 
processAllConstraints tcs = both concat . unzip <$> mapM processConstraint tcs

-- | Refine the current liquid assignments using the horn clauses
solveHornClauses clauses = do
  tass <- use typeAssignment
  qmap <- use qualifierMap
  cands <- use candidates
  env <- use initEnv
  cands' <- lift . lift . lift $ refine clauses qmap (instantiateConsAxioms env) cands
  when (null cands') $ writeLog 1 (text "FAIL: horn clauses have no solutions") >> fail ""
  candidates .= cands'

checkTypeConsistency clauses = do
  cands <- use candidates
  cands' <- lift . lift . lift $ checkConsistency clauses cands
  when (null cands') $ writeLog 1 (text "FAIL: inconsistent types") >> fail ""
  candidates .= cands'

simplifyConstraint :: MonadHorn s => Constraint -> TCSolver s ([Constraint], [Constraint])
simplifyConstraint c = do
  tass <- use typeAssignment
  pass <- use predAssignment
  simplifyConstraint' tass pass c

-- Dummy type variable: drop
simplifyConstraint' _ _ (Subtype env t tv@(ScalarT (TypeVarT a) _) consistent) | a == dontCare
  = return ([], [])
-- Well-formedness of a known predicate drop  
simplifyConstraint' _ pass c@(WellFormedPredicate _ _ p) | p `Map.member` pass 
  = return ([], [])
  
-- Type variable with known assignment: substitute
simplifyConstraint' tass _ (Subtype env tv@(ScalarT (TypeVarT a) _) t consistent) | a `Map.member` tass
  = simplifyConstraint (Subtype env (typeSubstitute tass tv) t consistent)
simplifyConstraint' tass _ (Subtype env t tv@(ScalarT (TypeVarT a) _) consistent) | a `Map.member` tass
  = simplifyConstraint (Subtype env t (typeSubstitute tass tv) consistent)
simplifyConstraint' tass _ (WellFormed env tv@(ScalarT (TypeVarT a) _)) | a `Map.member` tass
  = simplifyConstraint (WellFormed env (typeSubstitute tass tv))
  
-- Two unknown free variables: nothing can be done for now
simplifyConstraint' _ _ c@(Subtype env (ScalarT (TypeVarT a) _) (ScalarT (TypeVarT b) _) _) | not (isBound a env) && not (isBound b env)
  = if a == b
      then writeLog 1 "simplifyConstraint: equal type variables on both sides" >> fail ""
      else return ([], [c])
simplifyConstraint' _ _ c@(WellFormed env (ScalarT (TypeVarT a) _)) | not (isBound a env) 
  = return ([], [c])
  
-- Predicate well-formedness: shapeless or simple depending on type variables  
simplifyConstraint' tass _ c@(WellFormedPredicate env sorts p) =
  let typeVars = Set.toList $ Set.unions $ map (typeVarsOf . fromSort) sorts
  in if any (isFreeVariable tass) typeVars
    then do
      writeLog 1 $ text "WARNING: free vars in predicate" <+> pretty c
      return ([], [c]) -- Still has type variables: cannot determine shape
    else  do                 
      u <- freshId "u"
      addPredAssignment p (Unknown Map.empty u)
      let sorts' = map (sortSubstitute $ asSortSubst tass) sorts
      let vars = zipWith Var sorts' deBrujns
      tq <- asks _typeQualsGen
      addQuals u (tq (env, last vars : (init vars ++ allScalars env tass)))
      return ([], [])
  where
    isFreeVariable tass a = not (isBound a env) && not (Map.member a tass)
  
-- Unknown free variable and a type: extend type assignment
simplifyConstraint' _ _ c@(Subtype env (ScalarT (TypeVarT a) _) t _) | not (isBound a env) 
  = unify env a t >> simplifyConstraint c
simplifyConstraint' _ _ c@(Subtype env t (ScalarT (TypeVarT a) _) _) | not (isBound a env) 
  = unify env a t >> simplifyConstraint c

-- Compound types: decompose
simplifyConstraint' _ _ (Subtype env (ScalarT (DatatypeT name (tArg:tArgs) pArgs) fml) (ScalarT (DatatypeT name' (tArg':tArgs') pArgs') fml') consistent)
  = do
      simplifyConstraint (Subtype env tArg tArg' consistent)
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name tArgs pArgs) fml) (ScalarT (DatatypeT name' tArgs' pArgs') fml') consistent)
simplifyConstraint' _ _ (Subtype env (ScalarT (DatatypeT name [] (pArg:pArgs)) fml) (ScalarT (DatatypeT name' [] (pArg':pArgs')) fml') consistent)
  = do
      -- simplifyConstraint (Subtype emptyEnv (int $ pArg) (int $ pArg') consistent) -- Is this a cheat?
      simplifyConstraint (Subtype env (int $ pArg) (int $ pArg') consistent) -- Is this a cheat?
      simplifyConstraint (Subtype env (ScalarT (DatatypeT name [] pArgs) fml) (ScalarT (DatatypeT name' [] pArgs') fml') consistent)      
simplifyConstraint' _ _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) False)
  = do -- TODO: rename type vars
      simplifyConstraint (Subtype env tArg2 tArg1 False)
      simplifyConstraint (Subtype (addVariable y tArg2 env) (renameVar x y tArg2 tRes1) tRes2 False)
simplifyConstraint' _ _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) True) -- This is a hack: we assume that arg in t2 is a free tv with no refinements
  = do -- TODO: rename type vars
      -- simplifyConstraint (Subtype env tArg2 tArg1 False)
      simplifyConstraint (Subtype (addGhost y tArg1 env) (renameVar x y tArg1 tRes1) tRes2 True)
simplifyConstraint' _ _ (WellFormed env (ScalarT (DatatypeT name (tArg:tArgs) pArgs) fml))
  = do
      simplifyConstraint (WellFormed env tArg)
      simplifyConstraint (WellFormed env (ScalarT (DatatypeT name tArgs pArgs) fml))
simplifyConstraint' _ _ (WellFormed env (FunctionT x tArg tRes))
  = do
      simplifyConstraint (WellFormed env tArg)
      simplifyConstraint (WellFormed (addVariable x tArg env) tRes)

-- Simple constraint: return
simplifyConstraint' _ _ c@(Subtype _ (ScalarT baseT _) (ScalarT baseT' _) _) | baseT == baseT' = return ([c], [])
simplifyConstraint' _ _ c@(WellFormed _ (ScalarT baseT _)) = return ([c], [])
simplifyConstraint' _ _ c@(WellFormedCond _ _) = return ([c], [])
simplifyConstraint' _ _ c@(WellFormedMatchCond _ _) = return ([c], [])
-- Otherwise (shape mismatch): fail
simplifyConstraint' _ _ _ = writeLog 1 (text "FAIL: shape mismatch") >> fail ""

-- | Unify type variable @a@ with type @t@ or fail if @a@ occurs in @t@
unify env a t = if a `Set.member` typeVarsOf t
  then writeLog 1 (text "simplifyConstraint: type variable occurs in the other type") >> fail ""
  else do
    t' <- fresh env t
    writeLog 1 (text "UNIFY" <+> text a <+> text "WITH" <+> pretty t <+> text "PRODUCING" <+> pretty t')
    addTypeAssignment a t'    

-- | Convert simple constraint to horn clauses and consistency checks, and update qualifier maps
processConstraint :: MonadHorn s => Constraint -> TCSolver s ([Formula], [Formula])
processConstraint c@(Subtype env (ScalarT baseTL l) (ScalarT baseTR r) False) | baseTL == baseTR
  = if l == ffalse || r == ftrue
      then return ([], [])
      else do
        tass <- use typeAssignment
        pass <- use predAssignment
        let l' = substitutePredicate pass $ sortSubstituteFml (asSortSubst tass) l
        let r' = substitutePredicate pass $ sortSubstituteFml (asSortSubst tass) r
        if Set.null $ (predsOf l' `Set.union` predsOf r') Set.\\ (Map.keysSet $ env ^. boundPredicates)
          then do
            let lhss = embedding env tass pass `Set.union` Set.fromList [l'] -- (sortSubstFml l : allMeasurePostconditions baseT env)
            return ([conjunction lhss |=>| r'], [])
          else -- One of the sides contains free predicates: fail (WHY?)
            fail ""
processConstraint (Subtype env (ScalarT baseTL l) (ScalarT baseTR r) True) | baseTL == baseTR
  = do -- TODO: abs ref here
      tass <- use typeAssignment
      pass <- use predAssignment
      let l' = substitutePredicate pass $ sortSubstituteFml (asSortSubst tass) l
      let r' = substitutePredicate pass $ sortSubstituteFml (asSortSubst tass) r      
      return ([], [conjunction (Set.insert l' $ Set.insert r' $ embedding env tass pass)])
processConstraint (WellFormed env (ScalarT baseT fml)) 
  = case fml of
      Unknown _ u -> do
        tass <- use typeAssignment
        tq <- asks _typeQualsGen
        addQuals u (tq (env, Var (toSort baseT) valueVarName : allScalars env tass))
        return ([], [])
      _ -> return ([], [])
processConstraint (WellFormedCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      cq <- asks _condQualsGen
      addQuals u (cq (env, allScalars env tass))
      return ([], [])
processConstraint (WellFormedMatchCond env (Unknown _ u))
  = do
      tass <- use typeAssignment
      mq <- asks _matchQualsGen
      addQuals u (mq (env, allPotentialScrutinees env tass))
      return ([], [])
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

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: Monad s => String -> TCSolver s String
freshId prefix = do
  i <- uses idCount (Map.findWithDefault 0 prefix)
  idCount %= Map.insert prefix (i + 1)
  return $ prefix ++ show i

-- | 'fresh @t@ : a type with the same shape as @t@ but fresh type variables and fresh unknowns as refinements
fresh :: Monad s => Environment -> RType -> TCSolver s RType
fresh env (ScalarT (TypeVarT a) _) | not (isBound a env) = do
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
  
addTypeAssignment tv t = typeAssignment %= Map.insert tv t
addPredAssignment p fml = predAssignment %= Map.insert p fml  
  
addQuals :: MonadHorn s => Id -> QSpace -> TCSolver s ()
addQuals name quals = do
  quals' <- lift . lift . lift $ pruneQualifiers quals
  qualifierMap %= Map.insert name quals'  
  
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
    
matchConsType (ScalarT (DatatypeT d vars pVars) _) (ScalarT (DatatypeT d' args pArgs) _) | d == d' 
  = do
      zipWithM_ (\(ScalarT (TypeVarT a) (BoolLit True)) t -> addTypeAssignment a t) vars args
      zipWithM_ (\(Pred p _) fml -> addPredAssignment p fml) pVars pArgs
      -- pass' <- use predAssignment
      -- writeLog 1 (text "Pred assignment" $+$ vMapDoc text pretty pass')        
matchConsType _ _ = mzero    

isEnvironmentInconsistent env env' t = do
  cUnknown <- Unknown Map.empty <$> freshId "u"
  [] <- solveTypeConstraints [WellFormedCond env cUnknown]
  
  tass <- use typeAssignment
  pass <- use predAssignment
  qmap <- use qualifierMap
  let fml = conjunction $ embedding env tass pass
  let fml' = conjunction $ embedding env' tass pass
  cands <- use candidates
  cands' <- lift . lift . lift $ refine [(cUnknown |&| fml) |=>| fnot fml'] qmap (instantiateConsAxioms env) cands
  
  if null cands'
    then return Nothing
    else return $ Just $ (conjunction . flip valuation cUnknown . solution . head) cands'
  
-- writeLog :: (MonadHorn s, Show m) => Int -> m -> TCSolver s ()
writeLog level msg = do
  maxLevel <- asks _tcSolverLogLevel
  if level <= maxLevel then traceShow msg $ return () else return ()
  