-- | Type-checker for programs without holes that collects errors
module Synquid.PolicyChecker (localize, repair) where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.SolverMonad
import Synquid.TypeConstraintSolver hiding (freshId, freshVar)
import Synquid.Explorer
import Synquid.Util
import Synquid.Pretty
import Synquid.Resolver

import Data.List
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

-- | 'localize' @eParams tParams goal@ : reconstruct intermediate type annotations in @goal@
-- and return the resulting program in ANF together with a list of type-violating bindings
localize :: MonadHorn s => ExplorerParams -> TypingParams -> Goal -> s (Either ErrorMessage (RProgram, Requirements))
localize eParams tParams goal = do
    initTS <- initTypingState $ gEnvironment goal
    runExplorer (eParams { _sourcePos = gSourcePos goal }) tParams initTS go
  where
    go = do
      aImpl <- aNormalForm (gImpl goal)
      writeLog 2 (pretty aImpl)      
      
      p <- localizeTopLevel goal { gImpl = aImpl, gDepth = _auxDepth eParams }      
      labels <- runInSolver getViolatingLabels
      reqs <- uses requiredTypes (restrictDomain labels) >>= (mapM (liftM nub . mapM (runInSolver . finalizeType)))
      finalP <- runInSolver $ finalizeProgram p
      
      return (finalP, reqs)
      
repair :: MonadHorn s => ExplorerParams -> TypingParams -> Environment -> RProgram -> Requirements -> s (Either ErrorMessage RProgram)
repair eParams tParams env p violations = do
    initTS <- initTypingState env
    runExplorer eParams tParams initTS go
  where
    go = do
      writeLog 1 $ (nest 2 (text "Violated requirements:" $+$ vMapDoc text pretty violations)) $+$ text "when checking" $+$ pretty p
      requiredTypes .= violations
      replaceViolations env p
      
{- Localization -}
    
localizeTopLevel :: MonadHorn s => Goal -> Explorer s RProgram
localizeTopLevel (Goal funName env (ForallT a sch) impl depth pos) = localizeTopLevel (Goal funName (addTypeVar a env) sch impl depth pos)
localizeTopLevel (Goal funName env (ForallP sig sch) impl depth pos) = localizeTopLevel (Goal funName (addBoundPredicate sig env) sch impl depth pos)
localizeTopLevel (Goal funName env (Monotype typ@(FunctionT _ _ _)) impl depth _) = local (set (_1 . auxDepth) depth) $ localizeFix
  where
    localizeFix = do
      let typ' = renameAsImpl (isBound env) impl typ
      recCalls <- runInSolver (currentAssignment typ') >>= recursiveCalls
      polymorphic <- asks $ _polyRecursion . fst
      predPolymorphic <- asks $ _predPolyRecursion . fst
      let tvs = env ^. boundTypeVars
      let pvs = env ^. boundPredicates      
      let predGeneralized sch = if predPolymorphic then foldr ForallP sch pvs else sch -- Version of @t'@ generalized in bound predicate variables of the enclosing function          
      let typeGeneralized sch = if polymorphic then foldr ForallT sch tvs else sch -- Version of @t'@ generalized in bound type variables of the enclosing function
      
      let env' = foldr (\(f, t) -> addPolyVariable f (typeGeneralized . predGeneralized . Monotype $ t) . (shapeConstraints %~ Map.insert f (shape typ'))) env recCalls
      let ctx = \p -> if null recCalls then p else Program (PFix (map fst recCalls) p) typ'
      p <- inContext ctx  $ localizeI env' typ' impl
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

localizeTopLevel (Goal _ env (Monotype t) impl depth _) = local (set (_1 . auxDepth) depth) $ localizeI env t impl

-- | 'localizeI' @env t impl@ :: reconstruct unknown types and terms in a judgment @env@ |- @impl@ :: @t@ where @impl@ is a (possibly) introduction term
-- (top-down phase of bidirectional reconstruction)
localizeI :: MonadHorn s => Environment -> RType -> UProgram -> Explorer s RProgram
localizeI env t (Program p AnyT) = localizeI' env t p

localizeI' env t PErr = generateError env
localizeI' env t PHole = error "Holes not supported when checking policies"
localizeI' env t (PLet x iDef@(Program (PFun _ _) _) iBody) = do -- lambda-let: remember and type-check on use
  lambdaLets %= Map.insert x (env, iDef)
  pBody <- inContext (\p -> Program (PLet x uHole p) t) $ localizeI env t iBody
  (_, pDef) <- uses lambdaLets (Map.! x)
  return $ Program (PLet x pDef pBody) t
localizeI' env t@(FunctionT _ tArg tRes) impl = case impl of 
  PFun y impl -> do
    let ctx = \p -> Program (PFun y p) t
    pBody <- inContext ctx $ localizeI (unfoldAllVariables $ addVariable y tArg $ env) tRes impl
    return $ ctx pBody
  PSymbol f -> localizeETopLevel env t (untyped impl)
  _ -> throwErrorWithDescription $ text "Cannot assign function type" </> squotes (pretty t) </>
                    text "to non-lambda term" </> squotes (pretty $ untyped impl)
localizeI' env t@(ScalarT _ _) impl = case impl of
  PFun _ _ -> throwErrorWithDescription $ text "Cannot assign non-function type" </> squotes (pretty t) </>
                           text "to lambda term" </> squotes (pretty $ untyped impl)
                           
  PLet x iDef iBody -> do -- E-term let (since lambda-let was considered before)
    pDef <- inContext (\p -> Program (PLet x p (Program PHole t)) t) $ localizeETopLevel env AnyT iDef
    pBody <- inContext (\p -> Program (PLet x pDef p) t) $ localizeI (addVariable x (typeOf pDef) env) t iBody
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
    let scrutineeSymbols = symbolList pScrutinee
    let isGoodScrutinee = (not $ head scrutineeSymbols `elem` consNames) &&                 -- Is not a value
                          (any (not . flip Set.member (env ^. constants)) scrutineeSymbols) -- Has variables (not just constants)
    when (not isGoodScrutinee) $ throwErrorWithDescription $ text "Match scrutinee" </> squotes (pretty pScrutinee) </> text "is constant"
            
    (env', x) <- toVar pScrutinee (addScrutinee pScrutinee env)
    pCases <- zipWithM (localizeCase env' x pScrutinee t) iCases consTypes    
    return $ Program (PMatch pScrutinee pCases) t
      
  _ -> localizeETopLevel env t (untyped impl)
  
  where
    -- Check that all constructors are known and belong to the same datatype
    checkCases mName (Case consName args _ : cs) = case Map.lookup consName (allSymbols env) of
      Nothing -> throwErrorWithDescription $ text "Not in scope: data constructor" </> squotes (text consName)
      Just consSch -> do
                        consT <- instantiate env consSch True args -- Set argument names in constructor type to user-provided binders
                        case lastType consT of
                          (ScalarT (DatatypeT dtName _ _) _) -> do
                            case mName of
                              Nothing -> return ()                            
                              Just name -> if dtName == name
                                             then return ()
                                             else throwErrorWithDescription $ text "Expected constructor of datatype" </> squotes (text name) </> 
                                                               text "and got constructor" </> squotes (text consName) </> 
                                                               text "of datatype" </> squotes (text dtName)
                            if arity (toMonotype consSch) /= length args 
                              then throwErrorWithDescription $ text "Constructor" </> squotes (text consName)
                                            </> text "expected" </> pretty (arity (toMonotype consSch)) </> text "binder(s) and got" <+> pretty (length args)
                              else ((consName, consT) :) <$> checkCases (Just dtName) cs
                          _ -> throwErrorWithDescription $ text "Not in scope: data constructor" </> squotes (text consName)
    checkCases _ [] = return []
  
localizeCase env scrVar pScrutinee t (Case consName args iBody) consT = cut $ do  
  runInSolver $ matchConsType (lastType consT) (typeOf pScrutinee)
  consT' <- runInSolver $ currentAssignment consT
  (syms, ass) <- caseSymbols env scrVar args consT'
  let caseEnv = foldr (uncurry addVariable) (addAssumption ass env) syms
  pCaseExpr <- local (over (_1 . matchDepth) (-1 +)) $
               inContext (\p -> Program (PMatch pScrutinee [Case consName args p]) t) $ 
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
localizeE env t (Program p AnyT) = localizeE' env t p

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
    pArg@(Program (PSymbol y) t) <- inContext argCtx $ localizeE env tArg iArg
    return $ Program (PApp pFun pArg) (substituteInType (isBound env) (Map.singleton x (Var (toSort $ baseTypeOf t) y)) tRes)
  where
    generateHOArg env ctx tArg iArg = case content iArg of
      PSymbol f -> do
        lets <- use lambdaLets
        case Map.lookup f lets of
          Nothing -> -- This is a function from the environment, with a known type: check symbol against tArg                      
            localizeETopLevel env tArg iArg 
          Just (env', def) -> do -- This is a locally defined function: check it against tArg as a fixpoint
            lambdaLets %= Map.delete f -- Remove from lambda-lets in case of recursive call
            writeLog 1 $ text "Checking lambda-let argument" <+> pretty iArg <+> text "::" <+> pretty tArg <+> text "in" $+$ pretty (ctx (untyped PHole))
            def' <- inContext ctx $ localizeTopLevel (Goal f env' (Monotype tArg) def 0 noPos)
            lambdaLets %= Map.insert f (env', def')
            return iArg
      _ -> do -- Lambda-abstraction: check against tArg
            let tArg' = renameAsImpl (isBound env) iArg tArg
            writeLog 1 $ text "Checking lambda argument" <+> pretty iArg <+> text "::" <+> pretty tArg' <+> text "in" $+$ pretty (ctx (untyped PHole))
            inContext ctx $ localizeI env tArg' iArg
      
localizeE' env typ impl = do
  throwErrorWithDescription $ text "Expected application term of type" </> squotes (pretty typ) </>
                                          text "and got" </> squotes (pretty $ untyped impl)
                                          
checkSymbol :: MonadHorn s => Environment -> RType -> RProgram -> Explorer s ()
checkSymbol env typ p@(Program (PSymbol name) pTyp) = do
  ctx <- asks $ _context . fst
  writeLog 1 $ text "Checking" <+> pretty p <+> text "::" <+> pretty typ <+> text "in" $+$ pretty (ctx (untyped PHole))
  
  requiredTypes %= Map.insertWith (++) name [typ]
  addConstraint $ Subtype env pTyp typ False name
  runInSolver simplifyAllConstraints
  
{- Repair -}

replaceViolations :: MonadHorn s => Environment -> RProgram -> Explorer s RProgram
replaceViolations env (Program (PFun x body) t@(FunctionT _ tArg _)) = do
  body' <- replaceViolations (addVariable x tArg env) body
  return $ Program (PFun x body') t
replaceViolations env (Program (PIf cond thn els) t) = do
  let ScalarT BoolT fml = typeOf cond
  thn' <- replaceViolations (addAssumption (substitute (Map.singleton valueVarName ftrue) fml) env) thn
  els' <- replaceViolations (addAssumption (substitute (Map.singleton valueVarName ffalse) fml) env) els
  return $ Program (PIf cond thn' els') t
-- replaceViolations (Program (PMatch scr cases) t) = do
  -- (defsScr, aScr) <- anfE scr True
  -- aCases <- mapM (\(Case ctor binders e) -> (Case ctor binders) <$> aNormalForm e) cases
  -- return $ foldDefs defsScr (Program (PMatch aScr aCases) t) t
-- replaceViolations (Program (PFix xs body) t) = do
  -- aBody <- aNormalForm body
  -- return $ Program (PFix xs aBody) t
replaceViolations env (Program (PLet x def body) t) = do
  reqs <- use requiredTypes
  def' <- case Map.lookup x reqs of
            Nothing -> replaceViolations env def
            Just ts -> generateRepair env (head ts) def -- ToDo: other ts
  body' <- replaceViolations (addVariable x (typeOf def) env) body
  return $ Program (PLet x def' body') t
replaceViolations env (Program (PApp fun arg) t) = do
  fun' <- replaceViolations env fun
  arg' <- replaceViolations env arg
  return $ Program (PApp fun' arg') t
replaceViolations _ p = return p

generateRepair :: MonadHorn s => Environment -> RType -> RProgram -> Explorer s RProgram
generateRepair env typ p = do
  writeLog 1 $ text "Generating repair for" <+> pretty p <+> text "::" <+> pretty typ
  cUnknown <- Unknown Map.empty <$> freshId "C"
  addConstraint $ WellFormedCond env cUnknown
  addConstraint $ Subtype (addAssumption cUnknown env) (typeOf p) typ False ""
  runInSolver $ solveTypeConstraints
  cond <- conjunction <$> currentValuation cUnknown -- Todo: multiple valuations: disjunction
  let pCond = Program PHole (ScalarT BoolT $ valBool |=| cond)
  pElse <- defaultValue
  return $ Program (PIf pCond p pElse) typ
  where
    defaultValue = do
      let f = head $ symbolList p
      let f' = "default" ++ drop 3 f -- ToDo: better way of finding default value
      case lookupSymbol f' 0 env of
        Nothing -> throwErrorWithDescription $ text "No default value found for sensitive component" $+$ text f
        Just (Monotype t) -> return $ Program (PSymbol f') t

{- Misc -}  
                                            
-- | 'aNormalForm' @p@: program equivalent to @p@ where arguments and top-level e-terms do not contain applications
aNormalForm :: MonadHorn s => RProgram -> Explorer s RProgram
aNormalForm (Program (PFun x body) t) = do
  aBody <- aNormalForm body
  return $ Program (PFun x aBody) t
aNormalForm (Program (PIf cond thn els) t) = do
  (defsCond, aCond) <- anfE cond True
  aThn <- aNormalForm thn
  aEls <- aNormalForm els
  return $ foldDefs defsCond (Program (PIf aCond aThn aEls) t) t
aNormalForm (Program (PMatch scr cases) t) = do
  (defsScr, aScr) <- anfE scr True
  aCases <- mapM (\(Case ctor binders e) -> (Case ctor binders) <$> aNormalForm e) cases
  return $ foldDefs defsScr (Program (PMatch aScr aCases) t) t
aNormalForm (Program (PFix xs body) t) = do
  aBody <- aNormalForm body
  return $ Program (PFix xs aBody) t
aNormalForm (Program (PLet x def body) t) = do
  (defsX, aX) <- anfE def False
  aBody <- aNormalForm body
  return $ foldDefs defsX (Program (PLet x aX aBody) t) t
aNormalForm (Program PErr t) = return $ Program PErr t
aNormalForm (Program PHole t) = error "aNormalForm: got a hole"
aNormalForm eTerm@(Program _ t) = do
  (defs, a) <- anfE eTerm True
  return $ foldDefs defs a t
  
foldDefs defs body t = foldr (\(name, def) p -> Program (PLet name def p) t) body defs
  
-- | 'anfE' @p varRequired@: convert E-term @p@ to a list of bindings and either a variable (if @varRequired@) or a flat application (if not @varRequired@)
anfE :: MonadHorn s => RProgram -> Bool -> Explorer s ([(Id, RProgram)], RProgram)
anfE p@(Program (PSymbol x) t) _ = return ([], p)
anfE (Program (PApp pFun pArg) t) varRequired = do
  (defsFun, xFun) <- anfE pFun False
  (defsArg, xArg) <- anfE pArg True
  if varRequired
    then do
      tmp <- freshId "T"
      return (defsFun ++ defsArg ++ [(tmp, Program (PApp xFun xArg) t)], (Program (PSymbol tmp) t))
    else return (defsFun ++ defsArg, (Program (PApp xFun xArg) t))
anfE p@(Program (PFun _ _) t) _ = do -- A case for abstraction, which can appear in applications and let-bindings
  p' <- aNormalForm p
  return ([], p')    
anfE p _ = error $ unwords ["anfE: not an E-term or abstraction", show p]    
