-- | Refinement type reconstruction for programs with holes
module Synquid.TypeChecker where

import Synquid.Logic
import Synquid.Program
import Synquid.SolverMonad
import Synquid.TypeConstraintSolver hiding (freshId)
import Synquid.Explorer
import Synquid.Util
import Synquid.Pretty

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Control.Lens

reconstruct :: MonadHorn s => ExplorerParams -> TypingParams -> Goal -> s [RProgram]
reconstruct eParams tParams goal = do
    initTS <- initTypingState $ gEnvironment goal
    runExplorer eParams tParams initTS (reconstructTopLevel goal)
    
reconstructTopLevel :: MonadHorn s => Goal -> Explorer s RProgram
reconstructTopLevel (Goal funName env (ForallT a sch) impl) = reconstructTopLevel (Goal funName (addTypeVar a env) sch impl)
reconstructTopLevel (Goal funName env (ForallP pName pSorts sch) impl) = reconstructTopLevel (Goal funName (addPredicate pName pSorts env) sch impl)
reconstructTopLevel (Goal funName env (Monotype t@(FunctionT _ _ _)) impl) = reconstructFix
  where
    reconstructFix = do    
      recCalls <- recursiveCalls t
      polymorphic <- asks $ _polyRecursion . fst
      let tvs = env ^. boundTypeVars
      let env' = if polymorphic && not (null tvs)
                    then foldr (\(f, t') -> addPolyVariable f (foldr ForallT (Monotype t') tvs) . (shapeConstraints %~ Map.insert f (shape t))) env recCalls -- polymorphic recursion enabled: generalize on all bound variables
                    else foldr (\(f, t') -> addVariable f t') env recCalls  -- do not generalize
      let ctx = \p -> if null recCalls then p else Program (PFix (map fst recCalls) p) t
      p <- local (over (_1 . context) (. ctx)) $ reconstructI env' t impl
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

reconstructTopLevel (Goal _ env (Monotype t) impl) = reconstructI env t impl

reconstructI :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s RProgram
reconstructI env t (Program PHole _) = generateI env t
reconstructI env t (Program (PLet x iDef iBody) _) = do
  (_, pDef) <- reconstructE env (vartAll dontCare) iDef
  pBody <- reconstructI (addVariable x (typeOf pDef) env) t iBody
  return $ Program (PLet x pDef pBody) t
reconstructI env t@(FunctionT x tArg tRes) (Program (PFun y impl) _) = do
  let ctx = \p -> Program (PFun y p) t
  pBody <- local (over (_1 . context) (. ctx)) $ 
    reconstructI (unfoldAllVariables $ addVariable y tArg $ env) (renameVar x y tArg tRes) impl
  return $ ctx pBody
reconstructI env t@(ScalarT _ _) impl = case content impl of
  PIf iCond iThen iElse -> do
    (_, pCond) <- reconstructE env (ScalarT BoolT ftrue) iCond
    let ScalarT BoolT cond = typeOf pCond
    pThen <- once $ reconstructI (addAssumption cond env) t iThen -- ToDo: add context
    pElse <- once $ reconstructI (addAssumption (fnot cond) env) t iElse -- ToDo: add context
    return $ Program (PIf pCond pThen pElse) t
  _ -> snd <$> reconstructE env t impl
reconstructI _ _ _ = mzero -- TODO: error reporting, check not only beta-normal, eta-long form

reconstructE :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s (Environment, RProgram)
reconstructE env typ (Program PHole _) = generateE env typ
reconstructE env typ (Program (PSymbol name) _) = do
  case Map.lookup name (symbolsOfArity (arity typ) env) of
    Nothing -> mzero
    Just sch -> do
      t <- freshInstance sch
      let p = Program (PSymbol name) (symbolType env name t)
      symbolUseCount %= Map.insertWith (+) name 1
      case Map.lookup name (env ^. shapeConstraints) of
        Nothing -> return ()
        Just sch -> solveLocally $ Subtype env (refineBot $ shape t) (refineTop sch) False
      checkE env typ p
      return (env, p)
  where    
    freshInstance sch = if arity (toMonotype sch) == 0
      then instantiate env sch ffalse -- This is a nullary constructor of a polymorphic type: it's safe to instantiate it with bottom refinements
      else instantiate env sch ftrue
reconstructE env typ (Program (PApp iFun iArg) _) = do
  x <- freshId "x"
  (env', pFun) <- reconstructE env (FunctionT x (vartAll dontCare) typ) iFun
  let FunctionT x tArg tRes = typeOf pFun

  (envfinal, pApp) <- if isFunctionType tArg
    then do -- Higher-order argument: its value is not required for the function type, return a placeholder and enqueue an auxiliary goal
      pArg <- reconstructI env' tArg iArg
      return (env', Program (PApp pFun pArg) tRes)
    else do -- First-order argument: generate now
      (env'', pArg) <- reconstructE env' tArg iArg
      (env''', y) <- toSymbol pArg env''
      return (env''', Program (PApp pFun pArg) (renameVar x y tArg tRes))
  checkE envfinal typ pApp
  return (envfinal, pApp)
  
  
  
    
