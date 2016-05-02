-- | Refinement type reconstruction for programs with holes
module Synquid.TypeChecker where

import Synquid.Logic
import Synquid.Program
import Synquid.SolverMonad
import Synquid.TypeConstraintSolver hiding (freshId, freshVar)
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
      -- let p = foldr (\(x, e1) e2 -> Program (PLet x e1 e2) (typeOf e2)) pMain pAuxs
      let p = foldr (\(x, e1) e2 -> insertAuxSolution x e1 e2) pMain pAuxs
      runInSolver $ finalizeProgram p      

    reconstructAuxGoals = do
      goals <- use auxGoals
      writeLog 2 $ text "Auxiliary goals are:" $+$ vsep (map pretty goals)
      case goals of
        [] -> return []
        (g : gs) -> do
            auxGoals .= gs
            let g' = g {
                          gEnvironment = removeVariable (gName goal) (gEnvironment g)  -- remove recursive calls of the main goal
                       }
            writeLog 1 $ text "PICK AUXILIARY GOAL" <+> pretty g'
            p <- reconstructTopLevel g'
            rest <- reconstructAuxGoals
            return $ (gName g, p) : rest    
    
reconstructTopLevel :: MonadHorn s => Goal -> Explorer s RProgram
reconstructTopLevel (Goal funName env (ForallT a sch) impl depth) = reconstructTopLevel (Goal funName (addTypeVar a env) sch impl depth)
reconstructTopLevel (Goal funName env (ForallP sig sch) impl depth) = reconstructTopLevel (Goal funName (addBoundPredicate sig env) sch impl depth)
reconstructTopLevel (Goal funName env (Monotype typ@(FunctionT _ _ _)) impl depth) = local (set (_1 . auxDepth) depth) $ reconstructFix
  where
    reconstructFix = do
      let typ' = renameAsImpl impl typ
      recCalls <- recursiveCalls typ'
      polymorphic <- asks $ _polyRecursion . fst
      predPolymorphic <- asks $ _predPolyRecursion . fst
      let tvs = env ^. boundTypeVars
      let pvs = env ^. boundPredicates      
      let predGeneralized sch = if predPolymorphic then foldr ForallP sch pvs else sch -- Version of @t'@ generalized in bound predicate variables of the enclosing function          
      let typeGeneralized sch = if polymorphic then foldr ForallT sch tvs else sch -- Version of @t'@ generalized in bound type variables of the enclosing function
      
      let env' = foldr (\(f, t) -> addPolyVariable f (typeGeneralized . predGeneralized . Monotype $ t) . (shapeConstraints %~ Map.insert f (shape typ'))) env recCalls
      let ctx = \p -> if null recCalls then p else Program (PFix (map fst recCalls) p) typ'
      p <- inContext ctx  $ reconstructI env' typ' impl
      return $ ctx p

    -- | 'recursiveCalls' @t@: name-type pairs for recursive calls to a function with type @t@ (0 or 1)
    recursiveCalls t = do
      fixStrategy <- asks $ _fixStrategy . fst
      case fixStrategy of
        AllArguments -> do recType <- fst <$> recursiveTypeTuple t ffalse; if recType == t then return [] else return [(funName, recType)]
        FirstArgument -> do recType <- recursiveTypeFirst t; if recType == t then return [] else return [(funName, recType)]
        DisableFixpoint -> return []
        Nonterminating -> return [(funName, t)]

    -- | 'recursiveTypeTuple' @t fml@: type of the recursive call to a function of type @t@ when a lexicographic tuple of all recursible arguments decreases;
    -- @fml@ denotes the disjunction @x1' < x1 || ... || xk' < xk@ of strict termination conditions on all previously seen recursible arguments to be added to the type of the last recursible argument;
    -- the function returns a tuple of the weakend type @t@ and a flag that indicates if the last recursible argument has already been encountered and modified
    recursiveTypeTuple (FunctionT x tArg tRes) fml = do
      case terminationRefinement x tArg of
        Nothing -> do
          (tRes', seenLast) <- recursiveTypeTuple tRes fml
          return (FunctionT x tArg tRes', seenLast)
        Just (argLt, argLe) -> do
          y <- freshVar env "x"
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
          y <- freshVar env "x"
          return $ FunctionT y (addRefinement tArg argLt) (renameVar x y tArg tRes)
    recursiveTypeFirst t = return t

    -- | If argument is recursible, return its strict and non-strict termination refinements, otherwise @Nothing@
    terminationRefinement argName (ScalarT IntT fml) = Just ( valInt |>=| IntLit 0  |&|  valInt |<| intVar argName,
                                                              valInt |>=| IntLit 0  |&|  valInt |<=| intVar argName)
    terminationRefinement argName (ScalarT dt@(DatatypeT name _ _) fml) = case env ^. datatypes . to (Map.! name) . wfMetric of
      Nothing -> Nothing
      Just mName -> let 
                      metric x = Pred IntS mName [x]
                      argSort = toSort dt
                    in Just ( metric (Var argSort valueVarName) |>=| IntLit 0  |&| metric (Var argSort valueVarName) |<| metric (Var argSort argName),
                              metric (Var argSort valueVarName) |>=| IntLit 0  |&| metric (Var argSort valueVarName) |<=| metric (Var argSort argName))
    terminationRefinement _ _ = Nothing

reconstructTopLevel (Goal _ env (Monotype t) impl depth) = local (set (_1 . auxDepth) depth) $ reconstructI env t impl

-- | 'reconstructI' @env t impl@ :: reconstruct unknown types and terms in a judgment @env@ |- @impl@ :: @t@ where @impl@ is a (possibly) introduction term
-- (top-down phase of bidirectional reconstruction)
reconstructI :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s RProgram
reconstructI env t (Program p AnyT) = reconstructI' env t p
reconstructI env t (Program p t') = do
  t'' <- checkAnnotation env t t' p
  reconstructI' env t'' p

reconstructI' env t PErr = generateError env
reconstructI' env t PHole = generateError env `mplus` generateI env t
reconstructI' env t (PLet x iDef@(Program (PFun _ _) _) iBody) = do -- lambda-let: remember and type-check on use
  lambdaLets %= Map.insert x (env, iDef)
  let ctx = \p -> Program (PLet x uHole p) t
  pBody <- inContext ctx $ reconstructI env t iBody
  return $ ctx pBody
reconstructI' env t@(FunctionT x tArg tRes) impl = case impl of 
  PFun y impl -> do
    let ctx = \p -> Program (PFun y p) t
    pBody <- inContext ctx $ reconstructI (unfoldAllVariables $ addVariable y tArg $ env) (renameVar x y tArg tRes) impl
    return $ ctx pBody
  PSymbol f -> do
    fun <- etaExpand t f
    reconstructI' env t $ content fun
  _ -> throwError $ errorText "Cannot assign function type" </> squotes (pretty t) </>
                    errorText "to non-lambda term" </> squotes (pretty $ untyped impl)
reconstructI' env t@(ScalarT _ _) impl = case impl of
  PFun _ _ -> throwError $ errorText "Cannot assign non-function type" </> squotes (pretty t) </>
                           errorText "to lambda term" </> squotes (pretty $ untyped impl)
                           
  PLet x iDef iBody -> do -- E-term let (since lambda-let was considered before)
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
                        consT <- renameAsImpl (foldr (\x p -> untyped $ PFun x p) uHole args) 
                                    <$> instantiate env consSch True -- Set argument names in constructor type to user-provided binders
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
  
reconstructCase env scrVar pScrutinee t (Case consName args iBody) consT = cut $ do  
  runInSolver $ matchConsType (lastType consT) (typeOf pScrutinee)
  consT' <- runInSolver $ currentAssignment consT
  (syms, ass) <- caseSymbols scrVar args consT'
  let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
  pCaseExpr <- local (over (_1 . matchDepth) (-1 +)) $
               inContext (\p -> Program (PMatch pScrutinee [Case consName args p]) t) $ 
               reconstructI caseEnv t iBody
  return $ Case consName args pCaseExpr  
  
-- | 'reconstructECond' @env t impl@ :: conditionally reconstruct the judgment @env@ |- @impl@ :: @t@ where @impl@ is an elimination term
reconstructECond :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s (Environment, Formula, RProgram)
reconstructECond env typ impl = if hasUnknownAssumptions
  then do  -- @env@ already contains an unknown assumption to be abduced
    (env', p) <- reconstructETopLevel env typ impl
    return (env', ftrue, p)
  else do -- create a fresh unknown assumption to be abduced
    cUnknown <- Unknown Map.empty <$> freshId "u"
    addConstraint $ WellFormedCond env cUnknown
    (env', p) <- reconstructETopLevel (addAssumption cUnknown env) typ impl
    cond <- conjunction <$> currentValuation cUnknown
    let env'' = over assumptions (Set.delete cUnknown . Set.insert cond) env' -- Replace @cUnknown@ with its valuation: it's not allowed to be strngthened anymore
    return (env'', cond, p)
  where
    hasUnknownAssumptions = F.any (not . Set.null . unknownsOf) (env ^. assumptions)

-- | 'reconstructE' @env t impl@ :: reconstruct unknown types and terms in a judgment @env@ |- @impl@ :: @t@ where @impl@ is an elimination term
-- (bottom-up phase of bidirectional reconstruction)    
reconstructETopLevel :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s (Environment, RProgram)    
reconstructETopLevel env t impl = do
  (finalEnv, Program pTerm pTyp) <- reconstructE env t impl
  pTyp' <- runInSolver $ solveTypeConstraints >> currentAssignment pTyp
  cleanupTypeVars
  return (finalEnv, Program pTerm pTyp')

reconstructE :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s (Environment, RProgram)
reconstructE env t (Program p AnyT) = reconstructE' env t p
reconstructE env t (Program p t') = do
  t'' <- checkAnnotation env t t' p
  reconstructE' env t'' p  

reconstructE' env typ PHole = do
  d <- asks $ _eGuessDepth . fst
  generateEUpTo env typ d
reconstructE' env typ (PSymbol name) = do
  case lookupSymbol name (arity typ) env of
    Nothing -> throwError $ errorText "Not in scope:" </> text name
    Just sch -> do
      t <- freshInstance sch
      let p = Program (PSymbol name) (symbolType env name t)
      symbolUseCount %= Map.insertWith (+) name 1
      case Map.lookup name (env ^. shapeConstraints) of
        Nothing -> return ()
        Just sc -> solveLocally $ Subtype env (refineBot $ shape t) (refineTop sc) False
      checkE env typ p Nothing
      return (env, p)
  where    
    freshInstance sch = if arity (toMonotype sch) == 0
      then instantiate env sch False -- This is a nullary constructor of a polymorphic type: it's safe to instantiate it with bottom refinements
      else instantiate env sch True
reconstructE' env typ (PApp iFun iArg) = do
  x <- freshVar env "x"
  (env', pFun) <- inContext (\p -> Program (PApp p uHole) typ) $ reconstructE env (FunctionT x AnyT typ) iFun
  let FunctionT x tArg tRes = typeOf pFun

  (envfinal, pApp) <- if isFunctionType tArg
    then do -- Higher-order argument: its value is not required for the function type, enqueue an auxiliary goal
      d <- asks $ _auxDepth . fst
      pArg <- generateHOArg env' (d - 1) tArg iArg
      return (env', Program (PApp pFun pArg) tRes)
    else do -- First-order argument: generate now
      (env'', pArg) <- inContext (\p -> Program (PApp pFun p) typ) $ reconstructE env' tArg iArg
      (env''', y) <- toVar pArg env''
      return (env''', Program (PApp pFun pArg) (substituteInType (Map.singleton x y) tRes))
  checkE envfinal typ pApp Nothing
  return (envfinal, pApp)
  where
    generateHOArg env d tArg iArg = case content iArg of
      PSymbol f -> do
        lets <- use lambdaLets
        case Map.lookup f lets of
          Nothing -> do -- This is a function from the environment, with a known type: add its eta-expansion as an aux goal
                      impl <- etaExpand tArg f
                      _ <- enqueueGoal env tArg impl d
                      return ()
          Just (env', def) -> auxGoals %= ((Goal f env' (Monotype tArg) def d ) :) -- This is a locally defined function: add an aux goal with its body
        return iArg
      _ -> enqueueGoal env tArg iArg d -- HO argument is an abstraction: enqueue a fresh goal              
      
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
    
-- | 'insertAuxSolution' @x pAux pMain@: insert solution @pAux@ to the auxiliary goal @x@ into @pMain@;
-- @pMain@ is assumed to contain either a "let x = ??" or "f x ..."
insertAuxSolution :: Id -> RProgram -> RProgram -> RProgram
insertAuxSolution x pAux prog@(Program body t) = flip Program t $ 
  case body of
    PLet y _ p -> if x == y 
                    then PLet x pAux p
                    else content $ ins prog
    PSymbol y -> if x == y
                    then content $ pAux
                    else body
    PApp p1 p2 -> PApp (ins p1) (ins p2)
    PFun y p -> PFun y (ins p)
    PIf c p1 p2 -> PIf (ins c) (ins p1) (ins p2)
    PMatch s cases -> PMatch (ins s) (map (\(Case c args p) -> Case c args (ins p)) cases)
    PFix ys p -> PFix ys (ins p)
    _ -> body  
  where
    ins = insertAuxSolution x pAux

etaExpand t f = do    
  args <- replicateM (arity t) (freshId "X")
  let body = foldl (\e1 e2 -> untyped $ PApp e1 e2) (untyped (PSymbol f)) (map (untyped . PSymbol) args)
  return $ foldr (\x p -> untyped $ PFun x p) body args
    
  
