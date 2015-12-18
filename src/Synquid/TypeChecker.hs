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
import Control.Monad.Logic
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Control.Lens

-- | 'reconstruct' @eParams tParams goal@ : reconstruct missing types and terms in the body of @goal@ so that it represents a valid type judgment;
-- return a type error if that is impossible
reconstruct :: MonadHorn s => ExplorerParams -> TypingParams -> Goal -> s (Either TypeError RProgram)
reconstruct eParams tParams goal = do
    initTS <- initTypingState $ gEnvironment goal
    runExplorer eParams tParams initTS go
  where
    go = do
      pMain <- reconstructTopLevel goal
      pAuxs <- reconstructAuxGoals
      let p = foldr (\(x, e1) e2 -> Program (PLet x e1 e2) (typeOf e2)) pMain pAuxs
      runInSolver $ finalize p      

    reconstructAuxGoals = do
      goals <- use auxGoals
      case goals of
        [] -> return []
        (g : gs) -> do
          auxGoals .= gs
          let g' = g { gEnvironment = removeVariable (gName goal) (gEnvironment g) } -- remove recursive calls of the main goal
          writeLog 1 $ text "AUXILIARY GOAL" <+> pretty g'          
          p <- reconstructTopLevel g'
          rest <- reconstructAuxGoals
          return $ (gName g, p) : rest    
    
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
      p <- inContext ctx  $ reconstructI env' t impl
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
  _ -> throwError $ text "Function type requires abstraction"
reconstructI' env t@(ScalarT _ _) impl = case impl of
  PFun _ _ -> throwError $ text "Abstraction of scalar type"
  
  PLet x iDef iBody -> do
    (env', pDef) <- inContext (\p -> Program (PLet x p (Program PHole t)) t) $ reconstructE env AnyT iDef
    pBody <- inContext (\p -> Program (PLet x pDef p) t) $ reconstructI (addVariable x (typeOf pDef) env') t iBody
    return $ Program (PLet x pDef pBody) t
  
  PIf (Program PHole AnyT) iThen iElse -> do
    cUnknown <- Unknown Map.empty <$> freshId "u"
    addConstraint $ WellFormedCond env cUnknown
    pThen <- inContext (\p -> Program (PIf (Program PHole boolAll) p (Program PHole t)) t) $ reconstructI (addAssumption cUnknown env) t iThen
    cond <- uses (typingState . candidates) (conjunction . flip valuation cUnknown . solution . head)
    pCond <- generateCondition env cond
    pElse <- optionalInPartial t $ inContext (\p -> Program (PIf pCond pThen p) t) $ reconstructI (addAssumption (fnot cond) env) t iElse 
    return $ Program (PIf pCond pThen pElse) t
  
  PIf iCond iThen iElse -> do
    (_, pCond) <- inContext (\p -> Program (PIf p (Program PHole t) (Program PHole t)) t) $ reconstructE env (ScalarT BoolT ftrue) iCond
    let ScalarT BoolT cond = typeOf pCond
    pThen <- inContext (\p -> Program (PIf pCond p (Program PHole t)) t) $ reconstructI (addAssumption cond env) t iThen
    pElse <- inContext (\p -> Program (PIf pCond pThen p) t) $ reconstructI (addAssumption (fnot cond) env) t iElse
    return $ Program (PIf pCond pThen pElse) t
    
  PMatch iScr iCases -> do
    (consNames, consTypes) <- unzip <$> checkCases Nothing iCases
    let scrT = refineTop $ shape $ lastType $ head consTypes
    
    (env', pScrutinee) <- inContext (\p -> Program (PMatch p []) t) $ reconstructE env scrT iScr
    let scrutineeSymbols = symbolList pScrutinee
    let isGoodScrutinee = (not $ head scrutineeSymbols `elem` consNames) &&                 -- Is not a value
                          (any (not . flip Set.member (env ^. constants)) scrutineeSymbols) -- Has variables (not just constants)
    when (not isGoodScrutinee) $ throwError $ text "Match scrutinee" <+> pretty pScrutinee <+> text "is constant"
    
    (env'', x) <- toSymbol pScrutinee env'
    pCases <- zipWithM (reconstructCase env'' x pScrutinee t) iCases consTypes
    return $ Program (PMatch pScrutinee pCases) t
      
  _ -> snd <$> reconstructE env t (untyped impl)
  
  where
    -- Check that all constructors are known and belong to the same datatype
    checkCases mName (Case consName args _ : cs) = case Map.lookup consName (allSymbols env) of
      Nothing -> throwError $ text "Datatype constructor" <+> text consName <+> text "undefined"
      Just consSch -> do
                        consT <- instantiate env consSch ftrue
                        case lastType consT of
                          (ScalarT (DatatypeT dtName _ _) _) -> do
                            case mName of
                              Nothing -> return ()                            
                              Just name -> if dtName == name
                                             then return ()
                                             else throwError $ text consName <+> text "is not a constructor of" <+> text name
                            if arity (toMonotype consSch) /= length args 
                              then throwError $ text "Datatype constructor" <+> text consName 
                                            <+> text "expected" <+> pretty (arity (toMonotype consSch)) <+> text "binders and got" <+> pretty (length args)
                              else ((consName, consT) :) <$> checkCases (Just dtName) cs
                          _ -> throwError $ text consName <+> text "is not a datatype constructor"
    checkCases _ [] = return []
  
reconstructCase env scrName pScrutinee t (Case consName args iBody) consT = do
  runInSolver $ matchConsType (lastType consT) (typeOf pScrutinee)
  let ScalarT baseT _ = (typeOf pScrutinee)
  (syms, ass) <- caseSymbols (Var (toSort baseT) scrName) args (symbolType env consName consT)
  let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
  pCaseExpr <- inContext (\p -> Program (PMatch pScrutinee [Case consName args p]) t) $ reconstructI caseEnv t iBody
  return $ Case consName args pCaseExpr

reconstructE :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s (Environment, RProgram)
reconstructE env t (Program p AnyT) = reconstructE' env t p
reconstructE env t (Program p t') = do
  t'' <- checkAnnotation env t t' p
  reconstructE' env t'' p  

reconstructE' env typ PHole = generateE env typ
reconstructE' env typ (PSymbol name) = do
  case Map.lookup name (symbolsOfArity (arity typ) env) of
    Nothing -> throwError $ text "Symbol" <+> text name <+> text "undefined"
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
reconstructE' env typ (PApp iFun iArg) = do
  x <- freshId "x"
  (env', pFun) <- inContext (\p -> Program (PApp p (Program PHole AnyT)) typ) $ reconstructE env (FunctionT x AnyT typ) iFun
  let FunctionT x tArg tRes = typeOf pFun

  (envfinal, pApp) <- if isFunctionType tArg
    then do -- Higher-order argument: its value is not required for the function type, return a placeholder and enqueue an auxiliary goal
      pArg <- enqueueGoal env' tArg iArg
      return (env', Program (PApp pFun pArg) tRes)
    else do -- First-order argument: generate now
      (env'', pArg) <- inContext (\p -> Program (PApp pFun p) typ) $ reconstructE env' tArg iArg
      (env''', y) <- toSymbol pArg env''
      return (env''', Program (PApp pFun pArg) (renameVar x y tArg tRes))
  checkE envfinal typ pApp
  return (envfinal, pApp)
reconstructE' env typ (PFormula fml) = do
  tass <- use (typingState . typeAssignment)
  case resolveRefinement (typeSubstituteEnv tass env) AnyS fml of
    Left err -> throwError $ text err
    Right fml' -> do
      let typ' = ScalarT BoolT fml'
      addConstraint $ Subtype env typ' typ False  
      solveIncrementally
      return (env, Program (PFormula fml') typ')
    
-- | 'checkAnnotation' @env t t' p@ : if user annotation @t'@ for program @p@ is a subtype of the goal type @t@,
-- return resolved @t'@, otherwise fail
checkAnnotation env t t' p = do
  tass <- use (typingState . typeAssignment)
  case resolveRefinedType (typeSubstituteEnv tass env) t' of
    Left err -> throwError $ text err
    Right t'' -> do
      ctx <- asks $ _context . fst
      writeLog 1 $ text "Checking type annotation" <+> pretty t'' <+> text "<:" <+> pretty t <+> text "in" $+$ pretty (ctx (Program p t''))
      addConstraint $ Subtype env t'' t False
      solveIncrementally
      return t''
    
