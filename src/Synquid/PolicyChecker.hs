-- | Type-checker for programs without holes that collects errors
module Synquid.PolicyChecker (localize, repair, recheck) where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.SolverMonad
import Synquid.TypeConstraintSolver hiding (freshId, freshVar)
import Synquid.Explorer
import Synquid.TypeChecker
import Synquid.Util
import Synquid.Pretty
import Synquid.Resolver
import Synquid.Tokens

import Data.Char hiding (isSymbol)
import Data.Maybe
import Data.List
import Data.Function (on)
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

import Debug.Trace

-- | 'localize' @eParams tParams goal@ : reconstruct intermediate type annotations in @goal@
-- and return the resulting program in ANF together with a list of type-violating bindings
localize :: MonadHorn s => Bool -> ExplorerParams -> TypingParams -> Goal -> s (Either ErrorMessage (RProgram, Requirements))
localize isRecheck eParams tParams goal = do
    initTS <- initTypingState $ gEnvironment goal
    runExplorer (eParams { _sourcePos = gSourcePos goal }) tParams (Reconstructor reconstructTopLevel) initTS go
  where
    go = do
      writeLog 2 (pretty $ gImpl goal)      
      aImpl <- aNormalForm "T" (gImpl goal)
      writeLog 2 (text "A Normal Form" $+$ pretty aImpl)      
      
      p <- localizeTopLevel goal { gImpl = aImpl }
      labels <- runInSolver getViolatingLabels
      reqs <- Map.map (map stripRefinements) <$> (uses requiredTypes (restrictDomain labels) >>= (mapM (liftM nub . mapM (runInSolver . finalizeType))))
      finalP <- runInSolver $ finalizeProgram p
      if isRecheck
        then if Map.null reqs
              then return (deANF finalP, Map.empty)
              else throwErrorWithDescription $ 
                    hang 2 (text "Re-verification of inserted checks failed with violations:" $+$ vMapDoc text pretty reqs $+$
                      text "Probable causes: missing type qualifiers or policy incorrectly depends on another sensitive value"
                    ) $+$ text "when checking" $+$ pretty p
        else if Map.null reqs
              then return (deANF finalP, Map.empty)
              else return (finalP, reqs)
      
repair :: MonadHorn s => ExplorerParams -> TypingParams -> Goal -> Requirements -> s (Either ErrorMessage (RProgram, [Goal]))
repair eParams tParams goal violations = do
    initTS <- initTypingState $ gEnvironment goal
    runExplorer (eParams {  _sourcePos = gSourcePos goal, 
                            _eGuessDepth = 3,
                            _scrutineeDepth = 0,
                            _matchDepth = 0,
                            _auxDepth = 1,
                            _fixStrategy = DisableFixpoint
                            }) tParams (Reconstructor reconstructTopLevel) initTS go
  where
    go = do
      writeLog 1 $ text "Found" <+> pretty (length violations) <+> text "violation(s) in function" <+> text (gName goal)
      writeLog 2 $ (nest 2 (text "Violated requirements:" $+$ vMapDoc text pretty violations)) $+$ text "when checking" $+$ pretty (gImpl goal)
      requiredTypes .= violations
      replaceViolations (addBoundVars (gSpec goal) $ gEnvironment goal) (gImpl goal)
      
    addBoundVars (ForallT a sch) env = addTypeVar a $ addBoundVars sch env
    addBoundVars (ForallP sig sch) env = addBoundPredicate sig $ addBoundVars sch env
    addBoundVars (Monotype _) env = env
    
-- | Remove all non-policy refinements  
stripRefinements :: RType -> RType
stripRefinements (ScalarT (DatatypeT name tArgs pArgs) _) = ScalarT (DatatypeT name (map stripRefinements tArgs) pArgs) ftrue
stripRefinements (ScalarT IntT _) = ScalarT IntT ftrue
stripRefinements (ScalarT BoolT _) = ScalarT BoolT ftrue
stripRefinements (ScalarT tv@(TypeVarT _ a) _) = ScalarT tv ftrue
stripRefinements (FunctionT x tArg tFun) = FunctionT x (stripRefinements tArg) (stripRefinements tFun)
stripRefinements (LetT _ _ t) = stripRefinements t
stripRefinements AnyT = AnyT
    
    
recheck :: MonadHorn s => ExplorerParams -> TypingParams -> RProgram -> [Goal] -> s (Either ErrorMessage RProgram)
recheck eParams tParams p [] = return (Right (deANF p))
recheck eParams tParams p (goal : goals) = do
  initTS <- initTypingState $ gEnvironment goal
  res <- runExplorer (eParams { _sourcePos = gSourcePos goal }) tParams (Reconstructor reconstructTopLevel) initTS (go goal)
  case res of
    Left err -> return (Left err)
    Right () -> recheck eParams tParams p goals
  where
    go goal = do
      aImpl <- aNormalForm "TR" (gImpl goal)
      writeLog 2 (pretty aImpl)      
      
      p <- localizeTopLevel goal { gImpl = aImpl }
      labels <- runInSolver getViolatingLabels
      reqs <- uses requiredTypes (restrictDomain labels) >>= (mapM (liftM nub . mapM (runInSolver . finalizeType)))
      finalP <- runInSolver $ finalizeProgram p
      if Map.null reqs
              then return ()
              else throwErrorWithDescription $ 
                    text "Failed to verify patch" $+$ indent 2 (pretty $ deANF finalP) $+$
                      text "against type" <+> pretty (gSpec goal) $+$ 
                      text "Probable causes: patch has no default branch or causes leaky enforcement"
      
{- Standard Tagged library -}

getPrefix = "get"
isDBGetter name = take (length getPrefix) name == getPrefix
-- getterOf field = getPrefix ++ (toUpper (head field) : tail field)

mkTagged a policy = DatatypeT "TIO" [a] [policy, ffalse]

-- stringType = DatatypeT "String" [] []
-- worldType = DatatypeT "World" [] []

isTagged (ScalarT (DatatypeT dtName _ _) _) | dtName == "TIO" = True
isTagged t = False

stripTags t@(ScalarT (DatatypeT dtName [dtArg] _) _) 
  | isTagged t   = stripTags dtArg
stripTags (ScalarT (DatatypeT dtName tArgs pArgs) fml) = (ScalarT (DatatypeT dtName (map stripTags tArgs) pArgs) fml)   
stripTags (FunctionT x tArg tRes) = FunctionT x (stripTags tArg) (stripTags tRes)
stripTags t = t

stripTagsSchema (Monotype t) = Monotype $ stripTags t
stripTagsSchema (ForallT a sch) = ForallT a (stripTagsSchema sch)
stripTagsSchema (ForallP sig sch) = let 
                                      sch' = stripTagsSchema sch 
                                      freePreds = predsOfType $ toMonotype sch'
                                    in if predSigName sig `Set.member` freePreds 
                                       then ForallP sig sch' 
                                       else sch'
      
{- Localization -}
    
localizeTopLevel :: MonadHorn s => Goal -> Explorer s RProgram
localizeTopLevel (Goal funName env (ForallT a sch) impl depth pos) = localizeTopLevel (Goal funName (addTypeVar a env) sch impl depth pos)
localizeTopLevel (Goal funName env (ForallP sig sch) impl depth pos) = localizeTopLevel (Goal funName (addBoundPredicate sig env) sch impl depth pos)
localizeTopLevel (Goal funName env (Monotype typ@(FunctionT _ _ _)) impl depth _) = do
  let typ' = renameAsImpl (isBound env) impl typ
  recCalls <- runInSolver (currentAssignment typ') >>= recursiveCalls
  polymorphic <- asks . view $ _1 . polyRecursion
  predPolymorphic <- asks . view $ _1 . predPolyRecursion
  let tvs = env ^. boundTypeVars
  let pvs = env ^. boundPredicates      
  let predGeneralized sch = if predPolymorphic then foldr ForallP sch pvs else sch -- Version of @t'@ generalized in bound predicate variables of the enclosing function          
  let typeGeneralized sch = if polymorphic then foldr ForallT sch tvs else sch -- Version of @t'@ generalized in bound type variables of the enclosing function
  
  let env' = foldr (\(f, t) -> addPolyVariable f (typeGeneralized . predGeneralized . Monotype $ t) . (shapeConstraints %~ Map.insert f (shape typ'))) env recCalls
  let ctx = \p -> if null recCalls then p else Program (PFix (map fst recCalls) p) typ'
  p <- inContext ctx  $ localizeI env' typ' impl
  return $ ctx p

  where
    -- | 'recursiveCalls' @t@: name-type pairs for recursive calls to a function with type @t@ (0 or 1)
    recursiveCalls t = do
      fixStrategy <- asks . view $ _1 . fixStrategy
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
          (tRes', seenLast) <- recursiveTypeTuple (renameVar (isBound env) x y tArg tRes) (fml `orClean` substitute yForVal argLt)
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
          return $ FunctionT y (addRefinement tArg argLt) (renameVar (isBound env) x y tArg tRes)
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

localizeTopLevel (Goal _ env (Monotype t) impl depth _) = localizeI env t impl

-- | 'localizeI' @env t impl@ :: reconstruct unknown types and terms in a judgment @env@ |- @impl@ :: @t@ where @impl@ is a (possibly) introduction term
-- (top-down phase of bidirectional reconstruction)
localizeI :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s RProgram
localizeI env t (Program p _) = localizeI' env t p

localizeI' env t PErr = generateError env
localizeI' env t PHole = error "Holes not supported when checking policies"
-- localizeI' env t (PLet x iDef@(Program (PFun _ _) _) iBody) = do -- lambda-let: remember and type-check on use
  -- lambdaLets %= Map.insert x (env, iDef)
  -- pBody <- inContext (\p -> Program (PLet x uHole p) t) $ localizeI env t iBody
  -- (_, pDef) <- uses lambdaLets (Map.! x)
  -- return $ Program (PLet x pDef pBody) t
localizeI' env t@(FunctionT _ tArg tRes) impl = case impl of 
  PFix _ impl -> localizeI env t impl
  PFun y impl -> 
    case Map.lookup y (allSymbols env) of
      Just _ -> throwErrorWithDescription $ text "Variable" </> text y </>
                    text "shadows a variable with the same name in" </> squotes (pretty impl)
      Nothing -> do
        let ctx = \p -> Program (PFun y p) t
        pBody <- inContext ctx $ localizeI (unfoldAllVariables $ addVariable y tArg $ env) tRes impl
        return $ ctx pBody
  PSymbol f -> localizeETopLevel env t (untyped impl)
  _ -> throwErrorWithDescription $ text "Cannot assign function type" </> squotes (pretty t) </>
                    text "to non-lambda term" </> squotes (pretty $ untyped impl)
localizeI' env t impl = case impl of
  PFun _ _ -> throwErrorWithDescription $ text "Cannot assign non-function type" </> squotes (pretty t) </>
                           text "to lambda term" </> squotes (pretty $ untyped impl)
                           
  PLet x iDef iBody -> do -- E-term let (since lambda-let was considered before)
    pDef <- inContext (\p -> Program (PLet x p (Program PHole t)) t) $ localizeETopLevel env AnyT iDef
    pBody <- inContext (\p -> Program (PLet x pDef p) t) $ localizeI (addLetBound x (typeOf pDef) env) t iBody
    return $ Program (PLet x pDef pBody) t
    
  PIf iCond iThen iElse -> do
    pCond <- inContext (\p -> Program (PIf p (Program PHole t) (Program PHole t)) t) $ localizeETopLevel env (ScalarT BoolT ftrue) iCond
    let ScalarT BoolT cond = typeOf pCond
    pThen <- inContext (\p -> Program (PIf pCond p (Program PHole t)) t) $ localizeI (addAssumption (substitute (Map.singleton valueVarName ftrue) cond) env) t iThen
    pElse <- inContext (\p -> Program (PIf pCond pThen p) t) $ localizeI (addAssumption (substitute (Map.singleton valueVarName ffalse) cond) env) t iElse
    return $ Program (PIf pCond pThen pElse) t
    
  PMatch iScr iCases -> do
    (consNames, consTypes) <- unzip <$> checkCases Nothing iCases
    let scrT = refineTop env $ shape $ lastType $ head consTypes
    
    pScrutinee <- inContext (\p -> Program (PMatch p []) t) $ localizeETopLevel env scrT iScr            
    pCases <- zipWithM (localizeCase env pScrutinee t) iCases consTypes    
    return $ Program (PMatch pScrutinee pCases) t
      
  _ -> localizeETopLevel env t (untyped impl)
  
  where
    -- Check that all constructors are known and belong to the same datatype
    checkCases mName (Case consName args _ : cs) = case Map.lookup consName (allSymbols env) of
      Nothing -> throwErrorWithDescription $ text "Not in scope: data constructor" </> squotes (text consName)
      Just consSch -> do
                        let consT = toMonotype consSch
                        case lastType consT of
                          (ScalarT (DatatypeT dtName _ _) _) -> do
                            case mName of
                              Nothing -> return ()                            
                              Just name -> if dtName == name
                                             then return ()
                                             else throwErrorWithDescription $ text "Expected constructor of datatype" </> squotes (text name) </> 
                                                               text "and got constructor" </> squotes (text consName) </> 
                                                               text "of datatype" </> squotes (text dtName)
                            if arity consT /= length args 
                              then throwErrorWithDescription $ text "Constructor" </> squotes (text consName)
                                            </> text "expected" </> pretty (arity consT) </> text "binder(s) and got" <+> pretty (length args)
                              else do
                                    let DatatypeDef ts ps _ _ = (env ^. datatypes) Map.! dtName
                                    let consSch' = stripHiddenParams ts ps consSch -- Remove type and pred parameters that are not present in the data type to avoid instantiation
                                    consT' <- instantiate env consSch' True args -- Set argument names in constructor type to user-provided binders
                                    rest <- checkCases (Just dtName) cs
                                    return $ (consName, consT') : rest
                          _ -> throwErrorWithDescription $ text "Not in scope: data constructor" </> squotes (text consName)

    checkCases _ [] = return []
    
    stripHiddenParams (_:ts) ps (ForallT a sch) = ForallT a (stripHiddenParams ts ps sch)
    stripHiddenParams [] ps (ForallT _ sch) = stripHiddenParams [] ps sch
    stripHiddenParams [] (_:ps) (ForallP p sch) = ForallP p (stripHiddenParams [] ps sch)
    stripHiddenParams [] [] (ForallP p sch) = stripHiddenParams [] [] sch
    stripHiddenParams [] [] sch = sch
  
localizeCase env pScrutinee@(Program (PSymbol x) scrT) t (Case consName args iBody) consT = cut $ do  
  runInSolver $ matchConsType (lastType consT) scrT
  consT' <- runInSolver $ currentAssignment consT
  let hiddenTypeVars = Set.toList $ typeVarsOf consT' Set.\\ typeVarsOf scrT
  let hiddenPredVars = Set.toList $ predSigsOfType consT' Set.\\ predSigsOfType scrT
  (syms, ass) <- caseSymbols env (Var (toSort $ baseTypeOf scrT) x) args consT'
  let caseEnv = flip (foldr addTypeVar) hiddenTypeVars . 
                flip (foldr addBoundPredicate) hiddenPredVars . 
                flip (foldr (uncurry addVariable)) syms $ 
                addAssumption ass env
  pCaseExpr <- inContext (\p -> Program (PMatch pScrutinee [Case consName args p]) t) $ 
               localizeI caseEnv t iBody
  return $ Case consName args pCaseExpr  

-- | 'localizeE' @env t impl@ :: reconstruct unknown types and terms in a judgment @env@ |- @impl@ :: @t@ where @impl@ is an elimination term
-- (bottom-up phase of bidirectional reconstruction)    
localizeETopLevel :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s RProgram
localizeETopLevel env t impl = do
  (Program pTerm pTyp) <- localizeE env t impl  
  pTyp' <- runInSolver $ currentAssignment pTyp
  return $ Program pTerm pTyp'

localizeE :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s RProgram
localizeE env t (Program p _) = localizeE' env t p

localizeE' env typ PHole = error "Holes not supported when checking policies"
localizeE' env typ (PSymbol name) = case lookupSymbol name (arity typ) env of
  Nothing -> throwErrorWithDescription $ text "Not in scope:" </> text name
  Just sch -> do
    t <- symbolType env name sch
    let p = Program (PSymbol name) t
    case Map.lookup name (env ^. shapeConstraints) of
      Nothing -> return ()
      Just sc -> addConstraint $ Subtype env (refineBot env $ shape t) (refineTop env sc) False ""
    when (not $ hasAny typ) $ checkSymbol env typ p
    return p
localizeE' env typ (PApp iFun iArg) = do
  x <- freshVar env "x"
  pFun <- inContext (\p -> Program (PApp p uHole) typ) $ localizeE env (FunctionT x AnyT typ) iFun
  let FunctionT x tArg tRes = typeOf pFun
  let argCtx = \p -> Program (PApp pFun p) tRes
  if isFunctionType tArg
  then do -- Higher-order argument: its value is not required for the function type, enqueue an auxiliary goal
    pArg <- generateHOArg env argCtx tArg iArg
    return $ argCtx pArg
  else do -- First-order argument: generate now
    pArg <- inContext argCtx $ localizeE env tArg iArg
    return $ Program (PApp pFun pArg) (appType env pArg x tRes)
  where
    generateHOArg env ctx tArg iArg = case content iArg of
      PSymbol f -> localizeETopLevel env tArg iArg  -- This is a function from the environment, with a known type: check symbol against tArg                     
      -- do
        -- lets <- use lambdaLets
        -- case Map.lookup f lets of
          -- Nothing -> -- This is a function from the environment, with a known type: check symbol against tArg                      
            -- localizeETopLevel env tArg iArg 
          -- Just (env', def) -> do -- This is a locally defined function: check it against tArg as a fixpoint
            -- lambdaLets %= Map.delete f -- Remove from lambda-lets in case of recursive call
            -- writeLog 2 $ text "Checking lambda-let argument" <+> pretty iArg <+> text "::" <+> pretty tArg <+> text "in" $+$ pretty (ctx (untyped PHole))
            -- def' <- inContext ctx $ localizeTopLevel (Goal f env' (Monotype tArg) def 0 noPos)
            -- lambdaLets %= Map.insert f (env', def')
            -- return iArg
      _ -> do -- Lambda-abstraction: check against tArg
            let tArg' = renameAsImpl (isBound env) iArg tArg
            writeLog 2 $ text "Checking lambda argument" <+> pretty iArg <+> text "::" <+> pretty tArg' <+> text "in" $+$ pretty (ctx (untyped PHole))
            inContext ctx $ localizeI env tArg' iArg
localizeE' env AnyT (PFun y impl) = 
  case Map.lookup y (allSymbols env) of
      Just _ -> throwErrorWithDescription $ text "Variable" </> text y </>
                    text "shadows a variable with the same name in" </> squotes (pretty impl)
      Nothing -> do
        -- Since we don't have lambda-lets anymore
        f <- freshId "F"
        let tArg = vart f ftrue
        addConstraint $ WellFormed env tArg
        let ctx = \p -> untyped (PFun y p)
        pBody <- inContext ctx $ localizeE (unfoldAllVariables $ addVariable y tArg $ env) AnyT impl
        writeLog 2 $ text "Inferred function type" <+> pretty (FunctionT y tArg (typeOf pBody)) <+> text "for" <+> pretty (untyped (PFun y impl))
        return $ Program (PFun y pBody) (FunctionT y tArg (typeOf pBody))
localizeE' env typ impl = do
  -- If we expect an application term, but get an I-term instead, just check it against a fresh type variable
  g <- freshId "G"
  let newGoal = vart g ftrue
  addConstraint $ WellFormed env newGoal
  when (not $ hasAny typ) (addConstraint $ Subtype env newGoal typ False g)
  writeLog 2 $ text "Checking I-term" <+> pretty (untyped impl) <+> text "::" <+> pretty newGoal
  localizeI env newGoal (untyped impl)    
-- localizeE' env typ impl = do
  -- throwErrorWithDescription $ text "localizeE' got an unexpected term" </> squotes (pretty $ untyped impl)
                                          
checkSymbol :: MonadHorn s => Environment -> RType -> RProgram -> Explorer s ()
checkSymbol env typ p@(Program (PSymbol name) pTyp) = do
  ctx <- asks . view $ _1 . context
  writeLog 2 $ text "Checking" <+> pretty p <+> text "::" <+> pretty typ <+> text "in" $+$ pretty (ctx (untyped PHole))
  
  requiredTypes %= Map.insertWith (++) name [typ]
  addConstraint $ Subtype env pTyp typ False name
  runInSolver simplifyAllConstraints
  
{- Repair -}

replaceViolations :: MonadHorn s => Environment -> RProgram -> Explorer s (RProgram, [Goal])
replaceViolations env (Program (PFun x body) t@(FunctionT _ tArg _)) = do
  (body', gs) <- replaceViolations (addVariable x tArg env) body
  return (Program (PFun x body') t, gs)
replaceViolations env (Program (PIf cond thn els) t) = do
  let ScalarT BoolT fml = typeOf cond
  (thn', gs1) <- replaceViolations (addAssumption (substitute (Map.singleton valueVarName ftrue) fml) env) thn
  (els', gs2) <- replaceViolations (addAssumption (substitute (Map.singleton valueVarName ffalse) fml) env) els
  return $ (Program (PIf cond thn' els') t, gs1 ++ gs2)
replaceViolations env (Program (PMatch scr cases) t) = do
  (cases', gss) <- unzip <$> mapM replaceInCase cases
  return $ (Program (PMatch scr cases') t, concat gss)
  where
    replaceInCase (Case consName args body) = do
      let scrT = typeOf scr
      let consSch = allSymbols env Map.! consName
      consT <- instantiate env consSch True [] 
      runInSolver $ matchConsType (lastType consT) scrT
      consT' <- runInSolver $ currentAssignment consT
      (syms, ass) <- caseSymbols env (Var (toSort $ baseTypeOf scrT) (symbolName scr)) args consT'
      let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
      (body', gs) <- replaceViolations caseEnv body
      return (Case consName (map fst syms) body', gs)
replaceViolations env (Program (PFix xs body) t) = do
  body' <- replaceViolations env body
  return body'
replaceViolations env p@(Program (PLet x def body) t) = do
  reqs <- use requiredTypes
  (newDefs, def', gs1) <- case Map.lookup x reqs of
            Nothing -> do
                          (def', gs) <- replaceViolations env def
                          return ([], def', gs)
            Just [t] -> if isTagged t
                          then generateRepair env t def
                          else throwErrorWithDescription $ hang 2 $ 
                                  text "Binder" <+> squotes (text x) <+> text "violates functional specification:" $+$ pretty t
                                  $+$ text "when checking" $+$ pretty p                                  
            Just ts -> throwErrorWithDescription $ hang 2 $ 
                        text "Binder" <+> squotes (text x) <+> text "violates multiple requirements:" $+$ vsep (map pretty ts) $+$
                        text "Probable causes: binder flows into multiple sinks or is itself a sink with a self-denying policy" $+$
                        text "when checking" $+$ pretty p
                                
  (body', gs2) <- replaceViolations (addLetBound x (typeOf def') env) body
  return (foldDefs (newDefs ++ [(x, def')]) body' t, gs1 ++ gs2)
replaceViolations env (Program (PApp fun arg) t) = do
  (fun', gs1) <- replaceViolations env fun
  (arg', gs2) <- replaceViolations env arg
  return (Program (PApp fun' arg') t, gs1 ++ gs2)
replaceViolations _ p = return (p, [])

-- | Generate a patch for `p` so that it has type `typ`
generateRepair :: MonadHorn s => Environment -> RType -> RProgram -> Explorer s ([(Id, RProgram)], RProgram, [Goal])
generateRepair env typ p = do
  writeLog 2 $ text "Generating repair for" <+> pretty p <+> text "::" <+> pretty typ $+$ text "in environment" <+> pretty env  
  branches <- generateBranches env typ p
  (defs, body) <- generateGuards env typ (p : branches)
  let patch = foldDefs defs body (typeOf body)
  return (defs, body, [Goal "patch" env (Monotype typ) patch 0 noPos])
  
-- | Generate all possible terms with policies between that of `p` and `typ`, and a default value of type `typ`
generateBranches :: MonadHorn s => Environment -> RType -> RProgram -> Explorer s [RProgram]
generateBranches env typ p = do
    -- Generate all branches
    let pureGoal = stripTags typ
    
    pVar <- freshId "X"    
    let env' = addVariable pVar (stripTags $ typeOf p) strippedEnv     
    
    writeLog 3 $ text "Generating pure branches of type" <+> pretty pureGoal $+$ text "in environment" <+> vMapDoc text pretty (allSymbols env')
    branches <- local (over (_2 . condQualsGen) (const (\_ _ -> emptyQSpace)) 
                       . over (_1 . eGuessDepth) (const 2)
                       ) $ 
                (nubBy (bothConstant pVar)           -- Leave only one branch that does mention any variables (they are all constant)
                . sortBy (compare `on` relevance pVar) -- Sort branches by relevance (those with pVar first, those with other vars last)
                . filter (not . isSymbol pVar))       -- Remove the original term (we'll re-add it later) 
                <$> generateMany (generateCandidate env' pureGoal) -- Enumerate candidate pure branches 
    writeLog 3 $ text "Generated pure branches" $+$ vsep (map (\b -> pretty b <+> text "::" <+> pretty (typeOf b)) branches)
        
    anfBranches <- mapM (aNormalForm "TB") branches 
    writeLog 3 $ text "Generated ANF branches" $+$ vsep (map (\b -> pretty b <+> text "::" <+> pretty (typeOf b)) anfBranches)
    liftedBranches <- mapM (liftBranch pVar) anfBranches
    writeLog 3 $ text "Generated lifted branches" $+$ vsep (map (\b -> pretty b <+> text "::" <+> pretty (typeOf b)) liftedBranches)
    return $ liftedBranches    
  where    
    strippedEnv = over symbols (Map.map (Map.foldlWithKey updateSymbol Map.empty)) env
    
    isInputVariable name = not (isConstant name env) && not (name `Set.member` (env ^. letBound))
        
    bothConstant pVar b1 b2 = b1 == b2 || not (pVar `Set.member` symbolsOf b1 || pVar `Set.member` symbolsOf b2)
    
    -- More relevant if it has `pVar` but less relevant if it has other variables
    relevance pVar b = let freeVars = symbolsOf b in 
                        (not (pVar `Set.member` freeVars), Set.size $ Set.filter isInputVariable freeVars)
        
    updateSymbol :: Map Id RSchema -> Id -> RSchema -> Map Id RSchema
    updateSymbol m name sch = if isInputVariable name || name `Set.member` (env ^. redactions)
                                then Map.insert name (stripTagsSchema sch) m -- Variable or redaction function: strip tags and keep
                                else m -- Non-redaction constant or let-bound: skip

    generateCandidate env' t' = do
      cand <- generateE env' t'
      cand' <- flip insertAuxSolutions cand <$> use solvedAuxGoals
      solvedAuxGoals .= Map.empty
      runInSolver $ finalizeProgram cand'
    
    liftBranch pVar b = do
      let oldEnv = addVariable pVar (typeOf p) env 
      let newEnv = addVariable pVar (stripTags $ typeOf p) strippedEnv 
      (defs, body, _) <- liftTerm oldEnv newEnv b -- lift syntactically
      return $ eraseTypes $ deANF $ foldDefs ((pVar, p) : defs) body AnyT
  
-- | Generate a guard for each of `branches` so that they have type `typ`
generateGuards :: MonadHorn s => Environment -> RType -> [RProgram] -> Explorer s ([(Id, RProgram)], RProgram)  
generateGuards env typ branches = do
  guardedBranches <- catMaybes <$> mapM abduceCondition branches -- Abduce a guard for each branch (original term is the head, then simpler to more complex)
  writeLog 3 $ text "Generated guarded branches" $+$ vsep (map pretty guardedBranches)
  sortedBranches <- (snd . removeRedundantDisjuncts) <$> 
                    foldM insertBranch [head guardedBranches] (tail guardedBranches) -- Sort branches by their guards, from weakest to strongest
  writeLog 3 $ text "Generated sorted branches" $+$ vsep (map pretty sortedBranches)
  combineBranches env typ ([], fst $ head sortedBranches) (tail sortedBranches) -- Generate a program for each guard and combine into a conditional
  where
    abduceCondition branch = do
      writeLog 3 $ text "Abducing condition for branch" <+> pretty branch
      
      case typeOf branch of
        AnyT -> do -- One of the default branches
          branch' <- aNormalForm "TTT" branch >>= localizeI env typ
          labels <- runInSolver getViolatingLabels
          reqs <- Map.map (map stripRefinements) <$> (uses requiredTypes (restrictDomain labels) >>= (mapM (liftM nub . mapM (runInSolver . finalizeType))))
          writeLog 3 $ text "Violations:" $+$ vMapDoc text pretty reqs
          if Map.null reqs
            then do 
                  writeLog 3 $ text "Branch is secure unconditionally"
                  return $ Just (branch, [ftrue])
            else let (_, [r]) = head $ Map.toList reqs 
                 in abduceCondition' branch (typeOf $ head branches) r -- TODO: what if more than one?        
        _ -> abduceCondition' branch (typeOf branch) typ -- Original term
      
    abduceCondition' branch t req = do 
      cUnknown <- Unknown Map.empty <$> freshId "C"
      let isRelevantPred name _ = name `Set.member` (predsOfType typ `Set.union` predsOfType (typeOf $ head branches))
      let isRevelantSymb name _ = not (isConstant name env) || (name `Set.member` (env ^. guards)) -- Only constants allowed are guards
      let env' = over globalPredicates (Map.filterWithKey isRelevantPred) . 
                 over symbols (Map.map (Map.filterWithKey isRevelantSymb)) $ env
      addConstraint $ WellFormedCond env' cUnknown
      addConstraint $ Subtype (addAssumption cUnknown env) t req False ""
      ifte (runInSolver $ solveTypeConstraints)
        (const $ do -- Condition found
          disjuncts <- map conjunction <$> allCurrentValuations cUnknown
          writeLog 3 $ text "Abduced condition:" <+> pretty disjuncts
          return $ Just (branch, disjuncts))
        (do
          writeLog 0 $ hang 2 (
            text "WARNING: cannot abduce a condition for branch" $+$ pretty branch </> text "::" </> pretty req $+$ 
            text "Probable cause: missing condition qualifiers")
          return Nothing)
          
    insertBranch [] _ = return [] -- This guard is stronger than the original code, throw away
    insertBranch sorted@((b, ds):bs) (branch, disjuncts) = do
      let newCond = foldr1 orClean disjuncts
      let oldCond = foldr1 orClean ds
      newSubsumes <- implies newCond oldCond
      oldSubsumes <- implies oldCond newCond
      if newSubsumes -- New subsumes `b`
        then if oldSubsumes 
              then return sorted -- Equivalent to b: throw away
              else ((b, ds) :) <$> insertBranch bs (branch, disjuncts) -- Strictly stronger than b, insert later
        else -- Some of the disjuncts do not subsume `b`: insert here          
          return $ (branch, disjuncts) : sorted
        
    implies c c' = ifte 
      (do
        addConstraint $ Subtype env (int c) (int c') False ""
        runInSolver $ checkTypeConstraints) 
      (const $ return True) 
      (return False)

    removeRedundantDisjuncts :: [(RProgram, [Formula])] -> ([Formula], [(RProgram, [Formula])])
    removeRedundantDisjuncts [] = ([], [])
    removeRedundantDisjuncts ((b, disjuncts):bs) = 
      let 
        (ds, bs') = removeRedundantDisjuncts bs
        disjuncts' = disjuncts \\ ds
      in (ds ++ disjuncts', (b, disjuncts') : bs')
  
combineBranches :: MonadHorn s => Environment -> RType -> ([(Id, RProgram)], RProgram) -> [(RProgram, [Formula])] -> Explorer s ([(Id, RProgram)], RProgram)  
combineBranches _ _ acc [] = return acc
combineBranches env typ (defs, els) ((branch, disjuncts) : bs) = do
  writeLog 3 $ text "Generating guard for branch" <+> pretty branch -- <+> text "::" <+> pretty (typeOf branch)
  condANFs <- mapM generateDisjunct disjuncts
  let allDefs = defs ++ concatMap fst condANFs
  let allConds = map snd condANFs            
  (defs', els') <- mkCheck allDefs allConds branch els
  combineBranches env typ (defs', els') bs
  where
    -- | Synthesize a tagged Boolean program with value equivalent to @fml@
    generateDisjunct:: MonadHorn s => Formula -> Explorer s ([(Id, RProgram)], RProgram)
    generateDisjunct fml = do
      let strippedEnv = over symbols (Map.map (Map.foldlWithKey (updateSymbol fml) Map.empty)) env
      let allConjuncts = Set.toList $ conjunctsOf fml
      conjuncts <- mapM (genPureConjunct strippedEnv) allConjuncts
      writeLog 3 $ text "Generated pure disjunct for condition" <+> pretty fml <+> pretty conjuncts
      lifted <- mapM (liftTerm env strippedEnv) conjuncts
      writeLog 3 $ text "Generated lifted disjunct" <+> vsep (map (\(defs, p, _) -> pretty defs $+$ pretty p) lifted)
      let defs = concatMap (view _1) lifted
      let conjuncts' = map (view _2) lifted
      let conjoin p1 p2 = ((usym "liftM2" `uapp` usym "and") `uapp` p1) `uapp` p2
      let pCond = foldl1 conjoin conjuncts'
      (defs', xCond) <- anfE "TT" pCond False
      return (defs ++ defs', xCond)
              
    genPureConjunct strippedEnv c = let targetType = ScalarT BoolT $ valBool |<=>| c in 
      ifte 
        (local (over (_2 . condQualsGen) (const (\_ _ -> emptyQSpace))) $ cut (generateE strippedEnv targetType))
        (\pCond -> aNormalForm "TT" pCond)
        (throwErrorWithDescription $ hang 2 $ 
          text "Cannot synthesize guard of type" <+> pretty targetType $+$
          text "for branch" $+$ pretty branch </> text "::" </> pretty typ $+$
          text "Probable cause: missing components to implement guard")

    -- | Strip tagged database accessors of their tags; only leave a symbol in the environment if it:
    --    - is designated as guard
    --    - is a DB getter
    --    - is a local variable
    updateSymbol :: Formula -> Map Id RSchema -> Id -> RSchema -> Map Id RSchema
    updateSymbol targetRefinement m name (Monotype t) = 
      let 
        t' = stripTags t 
        targetVars = Set.map varName $ varsOf targetRefinement
        targetPreds = predsOf targetRefinement
        getterPreds = predsOfType $ lastType t'
      in
          if isConstant name env 
            then if name `Set.member` (env ^. guards) || 
                    (isDBGetter name && not (disjoint targetPreds getterPreds)) 
                    -- any (\pred -> name == getterOf pred) targetPreds
                   then Map.insert name (Monotype t') m -- Strip
                   else m
            else Map.insert name (Monotype t') m -- Strip                 
    updateSymbol _ m name sch =
      if name `Set.member` (env ^. guards)
          then Map.insert name sch m
          else m

    mkCheck defs conds pThen pElse = do
      cTmps <- replicateM (length conds) (freshVar env "g") -- Binder for each guard      
      let mkOr p1 p2 = untyped $ PApp (untyped $ PApp (untyped $ PSymbol (binOpTokens Map.! Or)) p1) p2
      let body = untyped $ PIf (foldr1 mkOr $ map (untyped . PSymbol) cTmps) pThen pElse -- Conditional with disjunction of all binders
      return (defs, foldr (\(x, arg) b -> mkBind arg x b) body (zip cTmps $ map mkDowngrade conds)) -- Bind all guards to the binders
      
-- | 'liftTerm' @env strippedEnv p@: turn a pure E-term @p@ into a tagged one, 
-- by binding all lets that have different types in @env@ and @strippedEnv@
liftTerm :: MonadHorn s => Environment -> Environment -> RProgram -> Explorer s ([(Id, RProgram)], RProgram, Set Id)  
liftTerm env strippedEnv p@(Program (PLet x def body) typ) = do
  p' <- case content def of
          PFun x b -> return p -- Lambda-let: leave as is 
          _ -> let args = tail $ symbolList def in liftArgs args -- Regular let: see if any variable arguments need lifting
  liftTerm' p'
  where
    liftTerm' p@(Program (PLet x def body) typ) = 
      case content def of
        PFun fx fBody -> do -- Lambda let: lift its body
                      let FunctionT _ tArg _ = typeOf def
                      let addFX = addVariable fx tArg
                      let addFXTagged = addVariable fx (ScalarT (mkTagged tArg ffalse) ftrue)
                      (fDefs, fBody', fArgsToLift) <- liftTerm (addFXTagged env) (addFX strippedEnv) fBody -- TODO: fix
                      let liftedFun = untyped $ PFun fx (foldDefs fDefs fBody' AnyT)
                      let addX = addLetBound x (typeOf def)
                      (defs', body', argsToLift') <- liftTerm (addX env) (addX strippedEnv) body
                      return ((x, liftedFun):defs', body', fArgsToLift `Set.union` argsToLift')
        _ -> do
              let (f : argVars) = symbolList def
              let arity = length (symbolList def) - 1
              let addX = addLetBound x (typeOf def)
              let realType = toMonotype $ case lookupSymbol f arity env of
                            Nothing -> error $ unwords ["liftTerm: cannot find", f, "in original environment"]
                            Just t -> t
              let strippedType = toMonotype $ case lookupSymbol f arity strippedEnv of
                                Nothing -> error $ unwords ["liftTerm: cannot find", f, "in stripped environment"]
                                Just t -> t
              let realArgs = allArgTypes $ realType
              let strippedArgs = allArgTypes $ strippedType
              let argsToLift = Set.fromList $ map fst $ filter (\(_, (t, t')) -> t /= t') (zip argVars $ (zip realArgs strippedArgs))
                                
              (defs', body', argsToLift') <- liftTerm (addX env) (addX strippedEnv) body
              let allArgsToLift = argsToLift `Set.union` argsToLift'
              if realType == strippedType || x `Set.member` argsToLift'
                then return ((x, def):defs', body', allArgsToLift) -- This definition hasn't been stripped: leave as is
                else if isSymbol x body
                      then return ([], def, argsToLift) -- This definition has been stripped, but skip the redundant bind
                      else do -- This definition has been stripped: turn into a bind
                        y <- freshVar env "x"
                        let body'' = programSubstituteSymbol x (untyped (PSymbol y)) (foldDefs defs' body' AnyT)
                        return ([(x, def)], mkBind (untyped (PSymbol x)) y body'', allArgsToLift)
          
    liftArgs (arg:args) = 
      if allSymbols env Map.! arg == allSymbols strippedEnv Map.! arg
        then liftArgs args
        else do
          y <- freshVar env "TT"
          p' <- liftArgs args
          let body' = programSubstituteSymbol arg (untyped (PSymbol y)) p'
          return $ Program (PLet y (untyped (PSymbol arg)) body') (typeOf body')
    liftArgs [] = return p
      
liftTerm env strippedEnv p@(Program (PSymbol name) _) = do
  let realType = case lookupSymbol name 0 env of
                Nothing -> error $ unwords ["liftTerm: cannot find", name, "in original environment"]
                Just t -> t
  let strippedType = case lookupSymbol name 0 strippedEnv of
                    Nothing -> error $ unwords ["liftTerm: cannot find", name, "in stripped environment"]
                    Just t -> t      
  if realType == strippedType
    then do
      tmp <- freshId "TT"
      return ([(tmp, mkReturn p)], untyped $ PSymbol tmp, Set.empty)
    else return $ ([], p, Set.empty)

mkReturn :: RProgram -> RProgram
mkReturn p = usym "return" `uapp` p  
  
mkBind :: RProgram -> Id -> RProgram -> RProgram
mkBind arg x body = 
  let fun = untyped (PFun x body)
  in (usym "bind" `uapp` arg) `uapp` fun    
  
mkDowngrade :: RProgram -> RProgram
mkDowngrade p = usym "downgrade" `uapp` p    

{- Misc -}  
                                            
-- | 'aNormalForm' @p@: program equivalent to @p@ where arguments and top-level e-terms do not contain applications
aNormalForm :: MonadHorn s => Id -> RProgram -> Explorer s RProgram
aNormalForm prefix (Program (PFun x body) t) = do
  aBody <- aNormalForm prefix body
  return $ Program (PFun x aBody) t
aNormalForm prefix (Program (PIf cond thn els) t) = do
  (defsCond, aCond) <- anfE prefix cond True
  aThn <- aNormalForm prefix thn
  aEls <- aNormalForm prefix els
  return $ foldDefs defsCond (Program (PIf aCond aThn aEls) t) t
aNormalForm prefix (Program (PMatch scr cases) t) = do
  (defsScr, aScr) <- anfE prefix scr True
  aCases <- mapM (\(Case ctor binders e) -> (Case ctor binders) <$> aNormalForm prefix e) cases
  return $ foldDefs defsScr (Program (PMatch aScr aCases) t) t
aNormalForm prefix (Program (PFix xs body) t) = do
  aBody <- aNormalForm prefix body
  return $ Program (PFix xs aBody) t
aNormalForm prefix (Program (PLet x def body) t) = do
  (defsX, aX) <- anfE prefix def False
  aBody <- aNormalForm prefix body
  return $ foldDefs defsX (Program (PLet x aX aBody) t) t
aNormalForm _ (Program PErr t) = return $ Program PErr t
aNormalForm _ (Program PHole t) = error "aNormalForm: got a hole"
aNormalForm prefix eTerm@(Program _ t) = do
  (defs, a) <- anfE prefix eTerm True
  return $ foldDefs defs a t
  
foldDefs defs body t = foldr (\(name, def) p -> Program (PLet name def p) t) body defs
  
-- | 'anfE' @prefix p varRequired@: convert E-term @p@ to a list of bindings and a variable (if @varRequired@) or a simple application (otherwise)
anfE :: MonadHorn s => Id -> RProgram -> Bool -> Explorer s ([(Id, RProgram)], RProgram)
anfE prefix p@(Program (PSymbol x) t) _ = return ([], p)
anfE prefix (Program (PApp pFun pArg) t) varRequired = do
  (defsFun, xFun) <- anfE prefix pFun False
  (defsArg, xArg) <- anfE prefix pArg True
  if varRequired
    then do
      tmp <- freshId prefix
      return (defsFun ++ defsArg ++ [(tmp, Program (PApp xFun xArg) t)], (Program (PSymbol tmp) t))
    else return (defsFun ++ defsArg, (Program (PApp xFun xArg) t))
anfE prefix p@(Program _ t) varRequired = do -- Non-application term
  p' <- aNormalForm prefix p
  if varRequired
    then do
      tmp <- freshId prefix
      return ([(tmp, p')], (Program (PSymbol tmp) t))
    else return ([], p')    

deANF :: RProgram -> RProgram
deANF p = deANF' Map.empty Map.empty p

deANF' :: Map Id RProgram -> Map RProgram Id -> RProgram -> RProgram
deANF' tmpDefs userDefs (Program (PFun x body) t) = 
  let body' = deANF' tmpDefs userDefs body
  in Program (PFun x body') t
deANF' tmpDefs userDefs (Program (PIf cond thn els) t) = 
  let
    cond' = deANF' tmpDefs userDefs cond
    thn' = deANF' tmpDefs userDefs thn
    els' = deANF' tmpDefs userDefs els
  in Program (PIf cond' thn' els') t
deANF' tmpDefs userDefs (Program (PMatch scr cases) t) = 
  let
    scr' = deANF' tmpDefs userDefs scr
    cases' = map (\(Case ctor binders e) -> Case ctor binders (deANF' tmpDefs userDefs e)) cases
  in Program (PMatch scr' cases') t
deANF' tmpDefs userDefs (Program (PFix xs body) t) = 
  let body' = deANF' tmpDefs userDefs body
  in Program (PFix xs body') t
deANF' tmpDefs userDefs (Program (PLet x def body) t) =   
  let def' = deANF' tmpDefs userDefs def 
  in if isIdentifier x
    then let body' = deANF' tmpDefs (Map.insert (eraseTypes def') x userDefs) body
         in Program (PLet x def' body') t
    else deANF' (newMap def') userDefs body
  where
    newMap def' = case Map.lookup (eraseTypes def') userDefs of
                    Nothing -> Map.insert x def' tmpDefs
                    Just y -> Map.insert x (Program (PSymbol y) (typeOf def')) tmpDefs
deANF' tmpDefs userDefs (Program (PApp pFun pArg) t) =
  let
    pFun' = deANF' tmpDefs userDefs pFun
    pArg' = deANF' tmpDefs userDefs pArg
  in (Program (PApp pFun' pArg') t)    
deANF' tmpDefs userDefs p@(Program (PSymbol name) t) =
  case Map.lookup name tmpDefs of
    Nothing -> p
    Just def -> def
deANF' _ _ (Program PErr t) = Program PErr t
deANF' _ _ (Program PHole t) = error "deANF': got a hole"

-- | Return all current valuations of @u@
allCurrentValuations :: MonadHorn s => Formula -> Explorer s [Valuation]
allCurrentValuations u = do
  runInSolver $ solveAllCandidates
  cands <- use (typingState . candidates)
  let candGroups = groupBy (\c1 c2 -> val c1 == val c2) $ sortBy (\c1 c2 -> setCompare (val c1) (val c2)) cands
  -- Reset Horn solver (TODO: fix this hack):
  (typingState . candidates) .= [initialCandidate]
  (typingState . qualifierMap) .= Map.empty
  return $ map (val. head) candGroups
  where
    val c = valuation (solution c) u    
