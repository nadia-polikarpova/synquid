-- | Refinement type reconstruction for programs with holes
module Synquid.TypeChecker where

import Synquid.Logic
import Synquid.Program
import Synquid.SolverMonad
import Synquid.TypeConstraintSolver hiding (freshId)
import Synquid.Explorer
import Synquid.Util
import Synquid.Pretty
import Synquid.Resolver

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Foldable as F
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative hiding (empty)
import Control.Lens

-- | 'reconstruct' @eParams tParams goal@ : reconstruct missing types and terms in the body of @goal@ so that it represents a valid type judgment;
-- return a type error if that is impossible
reconstruct :: MonadHorn s => ExplorerParams -> TypingParams -> Goal -> s (Either TypeError RProgram)
reconstruct eParams tParams goal = do
    initTS <- initTypingState $ gEnvironment goal
    runExplorer eParams tParams initTS go
  where
    go = do
      pMain <- reconstructTopLevel goal { gDepth = _auxDepth eParams }
      pAuxs <- reconstructAuxGoals
      let p = foldr (\(x, e1) e2 -> Program (PLet x e1 e2) (typeOf e2)) pMain pAuxs
      runInSolver $ finalizeProgram p      

    reconstructAuxGoals = do
      goals <- use auxGoals
      writeLog 2 $ text "Auxiliary goals are:" $+$ vsep (map pretty goals)
      case goals of
        [] -> return []
        (g : gs) -> if isUnusedGoal g
            then if all isUnusedGoal gs -- g doesn't have a spec yet
                  then return [] -- all remaining goals are unused, nothing more to reconstruct
                  else do
                    auxGoals .= gs ++ [g] -- leave the unused goal for later
                    reconstructAuxGoals
            else do -- g has a proper spec: reconstruct
              auxGoals .= gs
              spec' <- runInSolver $ finalizeType (toMonotype $ gSpec g)
              let g' = g {
                          gSpec = Monotype spec',
                          gEnvironment = removeVariable (gName goal) (gEnvironment g)  -- remove recursive calls of the main goal
                         }
              writeLog 1 $ text "PICK AUXILIARY GOAL" <+> pretty g'
              p <- reconstructTopLevel g'
              rest <- reconstructAuxGoals
              return $ (gName g, p) : rest
    
    isUnusedGoal g = case toMonotype $ gSpec g of
                        AnyT -> True
                        _ -> False
    
reconstructTopLevel :: MonadHorn s => Goal -> Explorer s RProgram
reconstructTopLevel (Goal funName env (ForallT a sch) impl depth) = reconstructTopLevel (Goal funName (addTypeVar a env) sch impl depth)
reconstructTopLevel (Goal funName env (ForallP pName pSorts sch) impl depth) = reconstructTopLevel (Goal funName (addBoundPredicate pName pSorts env) sch impl depth)
reconstructTopLevel (Goal funName env (Monotype typ@(FunctionT _ _ _)) impl depth) = local (set (_1 . auxDepth) depth) $ reconstructFix
  where
    reconstructFix = do
      let typ' = renameAsImpl impl typ
      recCalls <- recursiveCalls typ'
      polymorphic <- asks $ _polyRecursion . fst
      predPolymorphic <- asks $ _predPolyRecursion . fst
      let tvs = env ^. boundTypeVars
      let pvs = env ^. boundPredicates      
      let predGeneralized sch = if predPolymorphic then foldr (uncurry ForallP) sch (Map.toList pvs) else sch -- Version of @t'@ generalized in bound predicate variables of the enclosing function
      let typeGeneralized sch = if polymorphic then foldr ForallT sch tvs else sch -- Version of @t'@ generalized in bound type variables of the enclosing function
      
      let env' = foldr (\(f, t) -> addPolyVariable f (typeGeneralized . predGeneralized . Monotype $ t) . (shapeConstraints %~ Map.insert f (shape typ'))) env recCalls
      let ctx = \p -> if null recCalls then p else Program (PFix (map fst recCalls) p) typ'
      p <- inContext ctx  $ reconstructI env' typ' impl
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
                        metric x = Pred outSort mName [x]
                    in Just ( metric (Var inSort valueVarName) |>=| IntLit 0  |&| metric (Var inSort valueVarName) |<| metric (Var inSort argName),
                              metric (Var inSort valueVarName) |>=| IntLit 0  |&| metric (Var inSort valueVarName) |<=| metric (Var inSort argName))
    terminationRefinement _ _ = Nothing

reconstructTopLevel (Goal _ env (Monotype t) impl depth) = local (set (_1 . auxDepth) depth) $ reconstructI env t impl

-- | 'reconstructI' @env t impl@ :: reconstruct unknown types and terms in a judgment @env@ |- @impl@ :: @t@ where @impl@ is a (possibly) introduction term
-- (top-down phase of bidirectional reconstruction)
reconstructI :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s RProgram
reconstructI env t (Program p AnyT) = reconstructI' env t p
reconstructI env t (Program p t') = do
  t'' <- checkAnnotation env t t' p
  reconstructI' env t'' p

reconstructI' env t PHole = generateI env t
reconstructI' env t@(FunctionT x tArg tRes) impl = case impl of 
  PFun y impl -> do
    let ctx = \p -> Program (PFun y p) t
    pBody <- inContext ctx $ reconstructI (unfoldAllVariables $ addVariable y tArg $ env) (renameVar x y tArg tRes) impl
    return $ ctx pBody
  PSymbol _ -> do
    args <- replicateM (arity t) (freshId "x")
    let body = foldl (\e1 e2 -> untyped $ PApp e1 e2) (untyped impl) (map (untyped . PSymbol) args)
    let fun = foldr (\x p -> untyped $ PFun x p) body args
    reconstructI' env t $ content fun
  PLet x iDef@(Program (PFun _ _) _) iBody -> do
    auxGoals %= ((Goal x env (Monotype AnyT) iDef 0) :)
    reconstructI env t iBody    
  _ -> throwError $ errorText "Cannot assign function type" </> squotes (pretty t) </>
                    errorText "to non-lambda term" </> squotes (pretty $ untyped impl)
reconstructI' env t@(ScalarT _ _) impl = case impl of
  PFun _ _ -> throwError $ errorText "Cannot assign non-function type" </> squotes (pretty t) </>
                           errorText "to lambda term" </> squotes (pretty $ untyped impl)
                           
  PLet x iDef iBody -> 
    case content iDef of
      PFun _ _ -> do -- lambda-let: create auxiliary goal with unknown type (to be filled on use)
        auxGoals %= ((Goal x env (Monotype AnyT) iDef 0) :)
        reconstructI env t iBody
      _ -> do -- E-term let
        (env', pathCond, pDef) <- inContext (\p -> Program (PLet x p (Program PHole t)) t) $ reconstructECond env AnyT iDef
        pBody <- inContext (\p -> Program (PLet x pDef p) t) $ reconstructI (addVariable x (typeOf pDef) env') t iBody
        wrapInConditional env pathCond (Program (PLet x pDef pBody) t) t    
  
  PIf (Program PHole AnyT) iThen iElse -> do
    cUnknown <- Unknown Map.empty <$> freshId "u"
    addConstraint $ WellFormedCond env cUnknown
    pThen <- inContext (\p -> Program (PIf (Program PHole boolAll) p (Program PHole t)) t) $ reconstructI (addAssumption cUnknown env) t iThen
    cond <- conjunction <$> currentValuation cUnknown
    pCond <- inContext (\p -> Program (PIf p uHole uHole) t) $ generateCondition env cond
    pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond pThen p) t) $ reconstructI (addAssumption (fnot cond) env) t iElse 
    return $ Program (PIf pCond pThen pElse) t
  
  PIf iCond iThen iElse -> do
    (env', pathCond, pCond) <- inContext (\p -> Program (PIf p (Program PHole t) (Program PHole t)) t) $ reconstructECond env (ScalarT BoolT ftrue) iCond
    let ScalarT BoolT cond = typeOf pCond
    pThen <- inContext (\p -> Program (PIf pCond p (Program PHole t)) t) $ reconstructI (addAssumption (substitute (Map.singleton valueVarName ftrue) cond) $ env') t iThen
    pElse <- inContext (\p -> Program (PIf pCond pThen p) t) $ reconstructI (addAssumption (substitute (Map.singleton valueVarName ffalse) cond) $ env') t iElse
    wrapInConditional env pathCond (Program (PIf pCond pThen pElse) t) t
    
  PMatch iScr iCases -> do
    (consNames, consTypes) <- unzip <$> checkCases Nothing iCases
    let scrT = refineTop $ shape $ lastType $ head consTypes
    
    (env', pathCond, pScrutinee) <- inContext (\p -> Program (PMatch p []) t) $ reconstructECond env scrT iScr
    let scrutineeSymbols = symbolList pScrutinee
    let isGoodScrutinee = (not $ head scrutineeSymbols `elem` consNames) &&                 -- Is not a value
                          (any (not . flip Set.member (env ^. constants)) scrutineeSymbols) -- Has variables (not just constants)
    when (not isGoodScrutinee) $ throwError $ errorText "Match scrutinee" </> squotes (pretty pScrutinee) </> errorText "is constant"
            
    (env'', x) <- toVar pScrutinee (addScrutinee pScrutinee env')
    pCases <- zipWithM (reconstructCase env'' x pScrutinee t) iCases consTypes    
    wrapInConditional env pathCond (Program (PMatch pScrutinee pCases) t) t
      
  _ -> do
    (_, pathCond, p) <- reconstructECond env t (untyped impl)
    wrapInConditional env pathCond p t
  
  where
    -- Check that all constructors are known and belong to the same datatype
    checkCases mName (Case consName args _ : cs) = case Map.lookup consName (allSymbols env) of
      Nothing -> throwError $ errorText "Not in scope: data constructor" </> squotes (text consName)
      Just consSch -> do
                        consT <- instantiate env consSch True
                        case lastType consT of
                          (ScalarT (DatatypeT dtName _ _) _) -> do
                            case mName of
                              Nothing -> return ()                            
                              Just name -> if dtName == name
                                             then return ()
                                             else throwError $ errorText "Expected constructor of datatype" </> squotes (text name) </> 
                                                               errorText "and got constructor" </> squotes (text consName) </> 
                                                               errorText "of datatype" </> squotes (text dtName)
                            if arity (toMonotype consSch) /= length args 
                              then throwError $ errorText "Constructor" </> squotes (text consName)
                                            </> errorText "expected" </> pretty (arity (toMonotype consSch)) </> errorText "binder(s) and got" <+> pretty (length args)
                              else ((consName, consT) :) <$> checkCases (Just dtName) cs
                          _ -> throwError $ errorText "Not in scope: data constructor" </> squotes (text consName)
    checkCases _ [] = return []
  
reconstructCase env scrVar pScrutinee t (Case consName args iBody) consT = do  
  scrType <- runInSolver $ currentAssignment (typeOf pScrutinee)
  runInSolver $ matchConsType (lastType consT) scrType
  let ScalarT baseT _ = scrType
  (syms, ass) <- caseSymbols scrVar args (symbolType env consName consT)
  deadUnknown <- Unknown Map.empty <$> freshId "u"
  solveLocally $ WellFormedCond env deadUnknown  -- TODO: we are not even looking for a condition here!
  let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
  pCaseExpr <- local (over (_1 . matchDepth) (-1 +)) $
               inContext (\p -> Program (PMatch pScrutinee [Case consName args p]) t) $ 
               reconstructI caseEnv t iBody
  return $ Case consName args pCaseExpr  
  
-- | 'reconstructECond' @env t impl@ :: conditionally reconstruct the judgment @env@ |- @impl@ :: @t@ where @impl@ is an elimination term
reconstructECond :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s (Environment, Formula, RProgram)
reconstructECond env typ impl = if hasUnknownAssumptions
  then do  -- @env@ already contains an unknown assumption to be abduced
    (env', p) <- reconstructE env typ impl
    return (env', ftrue, p)
  else do -- create a fresh unknown assumption to be abduced
    cUnknown <- Unknown Map.empty <$> freshId "u"
    addConstraint $ WellFormedCond env cUnknown
    (env', p) <- reconstructE (addAssumption cUnknown env) typ impl
    cond <- conjunction <$> currentValuation cUnknown
    let env'' = over assumptions (Set.delete cUnknown . Set.insert cond) env' -- Replace @cUnknown@ with its valuation: it's not allowed to be strngthened anymore
    return (env'', cond, p)
  where
    hasUnknownAssumptions = F.any (not . Set.null . unknownsOf) (env ^. assumptions)

-- | 'reconstructE' @env t impl@ :: reconstruct unknown types and terms in a judgment @env@ |- @impl@ :: @t@ where @impl@ is an elimination term
-- (bottom-up phase of bidirectional reconstruction)  
reconstructE :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s (Environment, RProgram)
reconstructE env t (Program p AnyT) = reconstructE' env t p
reconstructE env t (Program p t') = do
  t'' <- checkAnnotation env t t' p
  reconstructE' env t'' p  

reconstructE' env typ PHole = generateE env typ
reconstructE' env typ (PSymbol name) = do
  case lookupSymbol name (arity typ) env of
    Nothing -> throwError $ errorText "Not in scope:" </> text name
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
      then instantiate env sch False -- This is a nullary constructor of a polymorphic type: it's safe to instantiate it with bottom refinements
      else instantiate env sch True
reconstructE' env typ (PApp iFun iArg) = do
  x <- freshId "x"
  (env', pFun) <- inContext (\p -> Program (PApp p uHole) typ) $ reconstructE env (FunctionT x AnyT typ) iFun
  let FunctionT x tArg tRes = typeOf pFun

  (envfinal, pApp) <- if isFunctionType tArg
    then do -- Higher-order argument: its value is not required for the function type, return a placeholder and enqueue an auxiliary goal
      d <- asks $ _auxDepth . fst
      pArg <- enqueueGoal env' tArg iArg (d - 1)
      return (env', Program (PApp pFun pArg) tRes)
    else do -- First-order argument: generate now
      (env'', pArg) <- inContext (\p -> Program (PApp pFun p) typ) $ reconstructE env' tArg iArg
      (env''', y) <- toVar pArg env''
      return (env''', Program (PApp pFun pArg) (renameVarFml x y tRes))
  checkE envfinal typ pApp
  return (envfinal, pApp)
reconstructE' env typ impl = throwError $ errorText "Expected application term of type" </> squotes (pretty typ) </>
                                          errorText "and got" </> squotes (pretty $ untyped impl)
    
-- | 'checkAnnotation' @env t t' p@ : if user annotation @t'@ for program @p@ is a subtype of the goal type @t@,
-- return resolved @t'@, otherwise fail
checkAnnotation :: MonadHorn s => Environment -> RType -> RType -> BareProgram RType -> Explorer s RType  
checkAnnotation env t t' p = do
  tass <- use (typingState . typeAssignment)
  case resolveRefinedType (typeSubstituteEnv tass env) t' of
    Left err -> throwError $ errorText err
    Right t'' -> do
      ctx <- asks $ _context . fst
      writeLog 1 $ errorText "Checking consistency of type annotation" <+> pretty t'' <+> errorText "with" <+> pretty t <+> errorText "in" $+$ pretty (ctx (Program p t''))
      addConstraint $ Subtype env t'' t True
      
      fT <- runInSolver $ finalizeType t
      fT'' <- runInSolver $ finalizeType t''
      typingState . errorContext .= errorText "when checking consistency of type annotation" </> pretty fT'' </> errorText "with" </> pretty fT </> errorText "in" $+$ pretty (ctx (Program p t''))
      solveIncrementally
      typingState . errorContext .= empty
      
      tass' <- use (typingState . typeAssignment)
      return $ intersection t'' (typeSubstitute tass' t)
      
-- | 'wrapInConditional' @env cond p t@ : program that executes @p@ under @cond@ and is undefined otherwise
wrapInConditional :: MonadHorn s => Environment -> Formula -> RProgram -> RType -> Explorer s RProgram
wrapInConditional env cond p t = if cond == ftrue
  then return p
  else do
    pCond <- inContext (\p -> Program (PIf p uHole uHole) t) $ generateCondition env cond        
    let pElse = Program PHole t
    -- pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond p0 p) t) $ generateI (addAssumption (fnot cond) env) t
    return $ Program (PIf pCond p pElse) t
