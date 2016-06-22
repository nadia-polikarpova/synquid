{-# LANGUAGE TupleSections, FlexibleContexts, TemplateHaskell #-}

-- | Functions for processing the AST created by the Parser (eg filling in unknown types, verifying that refinement formulas evaluate to a boolean, etc.)
module Synquid.Resolver (resolveDecls, resolveRefinement, resolveRefinedType, addAllVariables, ResolverState (..)) where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.Util
import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Control.Lens
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Maybe
import Data.Either
import Data.List
import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable

import Debug.Trace

{- Interface -}

data ResolverState = ResolverState {
  _environment :: Environment,  
  _goals :: [(Id, (UProgram, SourcePos))],
  _condQualifiers :: [Formula],
  _typeQualifiers :: [Formula],
  _mutuals :: Map Id [Id],
  _inlines :: Map Id ([Id], Formula),
  _sortConstraints :: [SortConstraint],
  _currentPosition :: SourcePos,
  _idCount :: Int
}

makeLenses ''ResolverState

initResolverState = ResolverState {
  _environment = emptyEnv,
  _goals = [],
  _condQualifiers = [],
  _typeQualifiers = [],
  _mutuals = Map.empty,
  _inlines = Map.empty,
  _sortConstraints = [],
  _currentPosition = noPos,
  _idCount = 0
}

-- | Convert a parsed program AST into a list of synthesis goals and qualifier maps
resolveDecls :: [Declaration] -> Either ErrorMessage ([Goal], [Formula], [Formula])
resolveDecls declarations = 
  case runExcept (execStateT go initResolverState) of
    Left msg -> Left msg
    Right st -> 
      Right (map (makeGoal (st ^. environment) (map fst (st ^. goals)) (st ^. mutuals)) (st ^. goals), st ^. condQualifiers, st ^. typeQualifiers)
  where
    go = do
      -- Pass 1: collect all declarations and resolve sorts, but do not resolve refinement types yet
      mapM_ (extractPos resolveDeclaration) declarations
      -- Pass 2: resolve refinement types in signatures
      mapM_ (extractPos resolveSignatures) declarations
    makeGoal env allNames allMutuals (name, (impl, pos)) = 
      let
        spec = allSymbols env Map.! name
        myMutuals = Map.findWithDefault [] name allMutuals
        toRemove = drop (fromJust $ elemIndex name allNames) allNames \\ myMutuals -- All goals after and including @name@, except mutuals
        env' = foldr removeVariable env toRemove
      in Goal name env' spec impl 0 pos
    extractPos pass (Pos pos decl) = do
      currentPosition .= pos
      pass decl
      
resolveRefinement :: Environment -> Formula -> Either ErrorMessage Formula
resolveRefinement env fml = runExcept (evalStateT (resolveTypeRefinement AnyS fml) (initResolverState {_environment = env})) --, _fmlSubstitution = subst}))

resolveRefinedType :: Environment -> RType -> Either ErrorMessage RType
resolveRefinedType env t = runExcept (evalStateT (resolveType t) (initResolverState {_environment = env}))

addAllVariables :: [Formula] -> Environment -> Environment
addAllVariables = flip (foldr (\(Var s x) -> addVariable x (fromSort s)))
    
{- Implementation -}    

type Resolver a = StateT ResolverState (Except ErrorMessage) a

throwResError descr = do
  pos <- use currentPosition
  throwError $ ErrorMessage ResolutionError pos descr

resolveDeclaration :: BareDeclaration -> Resolver ()
resolveDeclaration (TypeDecl typeName typeVars typeBody) = do
  typeBody' <- resolveType typeBody
  let extraTypeVars = typeVarsOf typeBody' Set.\\ Set.fromList typeVars
  if Set.null extraTypeVars
    then environment %= addTypeSynonym typeName typeVars typeBody'
    else throwResError (text "Type variable(s)" <+> hsep (map text $ Set.toList extraTypeVars) <+> 
              text "in the definition of type synonym" <+> text typeName <+> text "are undefined")
resolveDeclaration (FuncDecl funcName typeSchema) = addNewSignature funcName typeSchema
resolveDeclaration (DataDecl dtName tParams pParams ctors) = do
  let
    datatype = DatatypeDef {
      _typeParams = tParams,
      _predArgs = pParams,
      _constructors = map constructorName ctors,
      _wfMetric = Nothing
    }
  environment %= addDatatype dtName datatype  
  let addPreds typ = foldl (flip ForallP) (Monotype typ) pParams
  mapM_ (\(ConstructorSig name typ) -> addNewSignature name $ addPreds typ) ctors
resolveDeclaration (MeasureDecl measureName inSort outSort post defCases isTermination) = do
  -- Resolve measure signature:
  resolveSort inSort
  resolveSort outSort  
  case inSort of 
    DataS dtName sArgs -> do
      -- Check that the input sort of the measure is D a_i, where a_i are the type parameters in the declaration of D:
      datatype <- uses (environment . datatypes) (Map.! dtName)
      let tParams = datatype ^. typeParams
      let declDtSort = DataS dtName (map VarS tParams)
      if inSort /= declDtSort
        then throwResError (text "Type parameters of measure" <+> text measureName <+> text "must be the same as in the datatype declaration")
        else do                
          environment %= addGlobalPredicate measureName outSort [inSort]
          -- Possibly add as termination metric:      
          if isTermination
            then if (isJust $ datatype ^. wfMetric) 
                  then throwResError (text "Multiple termination metrics defined for datatype" <+> text dtName)
                  else if outSort == IntS
                        then environment %= addDatatype dtName datatype { _wfMetric = Just measureName }
                        else throwResError (text "Output sort of termination measure" <+> text measureName <+> text "must be Int")
            else return ()
    _ -> throwResError (text "Input sort of measure" <+> text measureName <+> text "must be a datatype")
resolveDeclaration (PredDecl (PredSig name argSorts resSort)) = do
  ifM (Map.member name <$> use (environment . globalPredicates)) (throwResError (text "Duplicate declaration of predicate" <+> text name)) (return ())
  mapM_ resolveSort (resSort : argSorts)
  environment %= addGlobalPredicate name resSort argSorts
resolveDeclaration (SynthesisGoal name impl) = do
  syms <- uses environment allSymbols
  pos <- use currentPosition
  if Map.member name syms
    then goals %= (++ [(name, (impl, pos))])
    else throwResError (text "No specification found for synthesis goal" <+> text name)
resolveDeclaration (QualifierDecl quals) = mapM_ resolveQualifier quals
  where
    resolveQualifier q = if Set.member valueVarName (Set.map varName $ varsOf q)
      then typeQualifiers %= (q:)
      else condQualifiers %= (q:)
resolveDeclaration (MutualDecl names) = mapM_ addMutuals names
  where
    addMutuals name = do
      goalMb <- uses goals (lookup name)
      case goalMb of
        Just _ -> mutuals %= Map.insert name (delete name names)
        Nothing -> throwResError (text "Synthesis goal" <+> text name <+> text "in a mutual clause is undefined")
resolveDeclaration (InlineDecl name args body) = 
  ifM (uses inlines (Map.member name))
    (throwResError (text "Duplicate definition of inline" <+> text name))
    (do
      let extraVars = Set.map varName (varsOf body) `Set.difference` Set.fromList args
      if not $ Set.null extraVars
        then throwResError (text "Variables" <+> hsep (map text $ Set.toList extraVars) <+> text "undefined in the body of inline" <+> text name)
        else inlines %= Map.insert name (args, body))
      
resolveSignatures :: BareDeclaration -> Resolver ()      
resolveSignatures (FuncDecl name _)  = do
  sch <- uses environment ((Map.! name) . allSymbols)
  sch' <- resolveSchema sch
  environment %= addPolyConstant name sch'
resolveSignatures (DataDecl dtName tParams pParams ctors) = mapM_ resolveConstructorSignature ctors
  where
    resolveConstructorSignature (ConstructorSig name _) = do
      sch <- uses environment ((Map.! name) . allSymbols)
      sch' <- resolveSchema sch
      let nominalType = ScalarT (DatatypeT dtName (map vartAll tParams) (map nominalPredApp pParams)) ftrue
      let returnType = lastType (toMonotype sch')
      if nominalType == returnType
        then do
          let nominalSort = toSort $ baseTypeOf nominalType
          let sch'' = addRefinementToLastSch sch' (Var nominalSort valueVarName |=| Cons nominalSort name (allArgs (toMonotype sch')))    
          environment %= addPolyConstant name sch''
        else throwResError (commaSep [text "Constructor" <+> text name <+> text "must return type" <+> pretty nominalType, text "got" <+> pretty returnType])      
resolveSignatures (MeasureDecl measureName _ _ post defCases _) = do
  (outSort : (inSort@(DataS dtName sArgs) : _)) <- uses (environment . globalPredicates) (Map.! measureName)
  datatype <- uses (environment . datatypes) (Map.! dtName)
  post' <- resolveTypeRefinement outSort post
  let ctors = datatype ^. constructors  
  if length defCases /= length ctors
    then throwResError $ text "Definition of measure" <+> text measureName <+> text "must include one case per constructor of" <+> text dtName
    else do
      defs' <- mapM (resolveMeasureDef ctors) defCases
      environment %= addMeasure measureName (MeasureDef inSort outSort defs' post')    
  where
    resolveMeasureDef allCtors (MeasureCase ctorName binders body) = 
      if not (ctorName `elem` allCtors)
        then throwResError $ text "Not in scope: data constructor" <+> text ctorName <+> text "used in definition of measure" <+> text measureName
        else do
          consSch <- uses environment ((Map.! ctorName) . allSymbols)
          let consT = toMonotype consSch
          let n = arity consT 
          if n /= length binders 
            then throwResError $ text "Data constructor" <+> text ctorName <+> text "expected" <+> pretty n <+> text "binders and got" <+> pretty (length binders) <+> text "in definition of measure" <+> text measureName
            else do
              let ctorParams = allArgs consT
              let subst = Map.fromList $ zip binders ctorParams
              let fml = Pred AnyS measureName [Var AnyS valueVarName] |=| substitute subst body
              fml' <- withLocalEnv $ do
                environment  . boundTypeVars .= boundVarsOf consSch
                environment %= addAllVariables ctorParams
                resolveTypeRefinement (toSort $ baseTypeOf $ lastType consT) fml
              return $ MeasureCase ctorName (map varName ctorParams) fml'
resolveSignatures _                      = return ()   

{- Types and sorts -}

resolveSchema :: RSchema -> Resolver RSchema
resolveSchema sch = do
  let tvs = Set.toList $ typeVarsOf (toMonotype sch)
  sch' <- withLocalEnv $ do
    environment . boundTypeVars %= (tvs ++)
    resolveSchema' sch  
  return $ Foldable.foldl (flip ForallT) sch' tvs
  where
    resolveSchema' (ForallP sig@(PredSig predName argSorts resSort) sch) = do
      ifM (elem predName <$> uses (environment . boundPredicates) (map predSigName)) 
        (throwResError $ text "Duplicate predicate variables" <+> text predName)
        (return ())
      mapM_ resolveSort argSorts
      when (resSort /= BoolS) $
        (throwResError $ text "Bound predicate variable" <+> text predName <+> text "must return Bool")
      sch' <- withLocalEnv $ do
        environment %= addBoundPredicate sig
        resolveSchema' sch
      let extraTypeVars = (Set.unions (map typeVarsOfSort argSorts)) Set.\\ typeVarsOf (toMonotype sch')
      when (not $ Set.null extraTypeVars) $
        (throwResError $ text "Unbound variables" <+> (commaSep $ map pretty $ Set.toList extraTypeVars) <+> text "in sort of bound predicate" <+> text predName)
      return $ ForallP sig sch'
    resolveSchema' (Monotype t) = Monotype <$> resolveType t

resolveType :: RType -> Resolver RType
resolveType (ScalarT (DatatypeT name tArgs pArgs) fml) = do
  ds <- use $ environment . datatypes
  case Map.lookup name ds of
    Nothing -> do
      t' <- substituteTypeSynonym name tArgs >>= resolveType      
      fml' <- resolveTypeRefinement (toSort $ baseTypeOf t') fml
      return $ addRefinement t' fml'
    Just (DatatypeDef tParams pParams _ _) -> do
      when (length tArgs /= length tParams) $ 
        throwResError $ text "Datatype" <+> text name <+> text "expected" <+> pretty (length tParams) <+> text "type arguments and got" <+> pretty (length tArgs)
      when (length pArgs /= length pParams) $ 
        throwResError $ text "Datatype" <+> text name <+> text "expected" <+> pretty (length pParams) <+> text "predicate arguments and got" <+> pretty (length pArgs) 
      -- Resolve type arguments:
      tArgs' <- mapM resolveType tArgs
      -- Resolve predicate arguments:
      let subst = noncaptureSortSubst tParams (map (toSort . baseTypeOf) tArgs')
      pArgs' <- zipWithM (resolvePredArg subst) pParams pArgs
      let baseT' = DatatypeT name tArgs' pArgs'
      -- Resolve refinementL
      fml' <- resolveTypeRefinement (toSort baseT') fml
      return $ ScalarT baseT' fml'
  where    
    resolvePredArg :: (Sort -> Sort) -> PredSig -> Formula -> Resolver Formula
    resolvePredArg subst (PredSig _ argSorts BoolS) fml = withLocalEnv $ do
      let argSorts' = map subst argSorts
      let vars = zipWith Var argSorts' deBrujns
      environment %= addAllVariables vars
      case fml of
        Pred _ p [] -> resolveTypeRefinement AnyS (Pred BoolS p vars)
        _ -> resolveTypeRefinement AnyS fml

resolveType (ScalarT baseT fml) = ScalarT baseT <$> resolveTypeRefinement (toSort baseT) fml
      
resolveType (FunctionT x tArg tRes) = 
  if x == valueVarName
    then throwResError $ text valueVarName <+> text "is a reserved variable name"
    else if x == dontCare
      then error $ unwords ["resolveType: blank in function type", show (FunctionT x tArg tRes)] -- Should never happen
      else do
        tArg' <- resolveType tArg
        tRes' <- withLocalEnv $ do
          when (not $ isFunctionType tArg') (environment %= addVariable x tArg')
          resolveType tRes
        return $ FunctionT x tArg' tRes'
  
resolveType AnyT = return AnyT  

-- | Check that sort has no unknown datatypes
resolveSort :: Sort -> Resolver ()
resolveSort (SetS elSort) = resolveSort elSort
resolveSort s@(DataS name sArgs) = do
  ds <- use $ environment . datatypes
  case Map.lookup name ds of
    Nothing -> throwResError $ text "Datatype" <+> text name <+> text "is undefined in sort" <+> pretty s
    Just (DatatypeDef tParams _ _ _) -> do
      let n = length tParams
      when (length sArgs /= n) $ throwResError $ text "Datatype" <+> text name <+> text "expected" <+> pretty n <+> text "type arguments and got" <+> pretty (length sArgs)
      mapM_ resolveSort sArgs
resolveSort s = return ()
  
{- Formulas -}

-- | 'resolveTypeRefinement' @valueSort fml@ : resolve @fml@ as a refinement with _v of sort @valueSort@;
-- when @valueSort@ is @AnyS@, _v must not occur
resolveTypeRefinement :: Sort -> Formula -> Resolver Formula
resolveTypeRefinement _ (BoolLit True) = return $ BoolLit True -- Special case to allow undefined value sort for function types
resolveTypeRefinement valueSort fml = do
  fml' <- withLocalEnv $ do -- Resolve fml with _v : valueSort 
    case valueSort of
      AnyS -> return ()
      _ -> environment %= addVariable valueVarName (fromSort valueSort)
    resolveFormula fml
  enforceSame (sortOf fml') BoolS -- Refinements must have Boolean sort
  sortAssignmnet <- solveSortConstraints -- Solve sort constraints and substitute
  let fml'' = sortSubstituteFml sortAssignmnet fml'
  
  boundTvs <- use $ environment . boundTypeVars
  let freeTvs = typeVarsOfSort (sortOf fml'') Set.\\ (Set.fromList boundTvs) -- Remaining free type variables
  let resolvedFml = if Set.null freeTvs then fml'' else sortSubstituteFml (constMap freeTvs IntS) fml''   
  
  boundPreds <- uses (environment . boundPredicates) (Set.fromList . map predSigName)
  let invalidPreds = negPreds resolvedFml `Set.intersection` boundPreds
  when (not $ Set.null invalidPreds) $ 
    throwResError $ text "Bound predicate(s)" <+> commaSep (map text $ Set.toList invalidPreds)<+> text "occur negatively in a refinement" <+> pretty resolvedFml
  return resolvedFml

resolveFormula :: Formula -> Resolver Formula
resolveFormula (Var s x) = do
  env <- use environment
  case Map.lookup x (symbolsOfArity 0 env) of
    Just sch ->
      case sch of
        Monotype (ScalarT baseType _) -> do
          let s' = (toSort baseType)
          return $ Var s' x
        _ -> error $ unwords ["resolveFormula: encountered non-scalar variable", x, "in a formula"]
    Nothing -> resolveFormula (Pred AnyS x []) `catchError` -- Maybe it's a zero-argument predicate?
                  const (throwResError $ text "Variable" <+> text x <+> text "is not in scope")      -- but if not, throw this error to avoid confusion
                      
resolveFormula (SetLit _ elems) = do
  elemSort <- freshSort
  elems' <- mapM resolveFormula elems
  zipWithM_ enforceSame (map sortOf elems') (repeat elemSort)
  return $ SetLit elemSort elems'
  
resolveFormula (Unary op fml) = fmap (Unary op) $ do
  fml' <- resolveFormula fml
  enforceSame (sortOf fml') (operandSort op)
  return fml'
  where
    operandSort Not = BoolS
    operandSort Neg = IntS  
            
resolveFormula (Binary op l r) = do
  l' <- resolveFormula l
  r' <- resolveFormula r
  op' <- addConstraints op (sortOf l') (sortOf r')
  return $ Binary op' l' r'
  where
    addConstraints op sl sr
      | op == Eq  || op == Neq                                        
        = enforceSame sl sr >> return op
      | op == And || op == Or || op == Implies || op == Iff           
        = enforceSame sl BoolS >> enforceSame sr BoolS >> return op
      | op == Member                                                  
        = enforceSame (SetS sl) sr >> return op
      | op == Union || op == Intersect || op == Diff || op == Subset  
        = do
            elemSort <- freshSort
            enforceSame sl (SetS elemSort)
            enforceSame sr (SetS elemSort)
            return op
      | op == Times || op == Plus || op == Minus  
        = if isSetS sl 
            then do
              elemSort <- freshSort
              enforceSame sl (SetS elemSort)
              enforceSame sr (SetS elemSort)
              return $ toSetOp op
            else enforceSame sl IntS >> enforceSame sr IntS >> return op      
      | op == Le 
        = if isSetS sl 
            then do
              elemSort <- freshSort
              enforceSame sl (SetS elemSort)
              enforceSame sr (SetS elemSort)
              return $ toSetOp op
            else enforceSame sl sr >> sortConstraints %= (++ [IsOrd sl]) >> return op            
      | op == Lt || op == Gt || op == Ge
        = enforceSame sl sr >> sortConstraints %= (++ [IsOrd sl]) >> return op
              
    toSetOp Times = Intersect
    toSetOp Plus = Union
    toSetOp Minus = Diff
    toSetOp Le = Subset
    
resolveFormula (Ite cond l r) = do
  cond' <- resolveFormula cond
  l' <- resolveFormula l
  r' <- resolveFormula r
  enforceSame (sortOf cond') BoolS
  enforceSame (sortOf l') (sortOf r')
  return $ Ite cond' l' r'
   
resolveFormula (Pred _ name argFmls) = do
  inlineMb <- uses inlines (Map.lookup name)
  case inlineMb of
    Just (args, body) -> resolveFormula (substitute (Map.fromList $ zip args argFmls) body)
    Nothing -> do
      ps <- uses environment allPredicates
      (resSort : argSorts) <- case Map.lookup name ps of
                                Nothing -> throwResError $ text "Predicate or measure" <+> text name <+> text "is undefined"
                                Just sorts -> instantiate sorts
      if length argFmls /= length argSorts
          then throwResError $ text "Expected" <+> pretty (length argSorts) <+> text "arguments for predicate or measure" <+> text name <+> text "and got" <+> pretty (length argFmls)
          else do
            argFmls' <- mapM resolveFormula argFmls
            zipWithM_ enforceSame (map sortOf argFmls') argSorts
            return $ Pred resSort name argFmls'
          
resolveFormula (Cons _ name argFmls) = do
  syms <- uses environment allSymbols
  case Map.lookup name syms of
    Nothing -> throwResError $ text "Data constructor" <+> text name <+> text "is undefined"
    Just consSch -> do
      let consT = toMonotype consSch
      (resSort : argSorts) <- instantiate $ map (toSort . baseTypeOf) $ lastType consT : allArgTypes consT
      if length argSorts /= length argFmls
        then throwResError $ text "Constructor" <+> text name <+> text "expected" <+> pretty (length argSorts) <+> text "arguments and got" <+> pretty (length argFmls)
        else do
            argFmls' <- mapM resolveFormula argFmls
            zipWithM_ enforceSame (map sortOf argFmls') argSorts
            return $ Cons resSort name argFmls'
         
resolveFormula fml = return fml         

{- Misc -}

nominalPredApp (PredSig pName argSorts resSort) = Pred resSort pName (zipWith Var argSorts deBrujns)

solveSortConstraints :: Resolver SortSubstitution
solveSortConstraints = do
  (unificationCs, typeClassCs) <- uses sortConstraints (partition isSameSortConstraint)
  tvs <- uses (environment . boundTypeVars) Set.fromList
  sortConstraints .= []
  idCount .= 0
  let (sls, srs) = unzip $ map (\(SameSort s1 s2) -> (s1, s2)) unificationCs  
  subst <- case unifySorts tvs sls srs of
    Left (x, y) -> throwResError $ text "Cannot unify sorts" <+> pretty x <+> text "and" <+> pretty y
    Right subst -> return subst
  mapM_ (checkTypeClass subst) typeClassCs
  return subst
  where
    isSameSortConstraint (SameSort _ _) = True
    isSameSortConstraint _ = False
    
    checkTypeClass subst (IsOrd s) = let s' = sortSubstitute subst s in
      case s' of
        IntS -> return ()
        VarS _ -> return ()
        _ -> throwResError $ text "Sort" <+> pretty s' <+> text "is not ordered"
    
addNewSignature name sch = do
  ifM (Set.member name <$> use (environment . constants)) (throwResError $ text "Duplicate declaration of function" <+> text name) (return ())
  environment %= addPolyConstant name sch
  environment %= addUnresolvedConstant name sch
  
substituteTypeSynonym name tArgs = do
  tss <- use $ environment . typeSynonyms
  case Map.lookup name tss of
    Nothing -> throwResError $ text "Datatype or synonym" <+> text name <+> text "is undefined"
    Just (tVars, t) -> do
      when (length tArgs /= length tVars) $ throwResError $ text "Type synonym" <+> text name <+> text "expected" <+> pretty (length tVars) <+> text "type arguments and got" <+> pretty (length tArgs)
      return $ noncaptureTypeSubst tVars tArgs t
      
-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshSort :: Resolver Sort
freshSort = do
  i <- use idCount
  idCount %= ( + 1)
  return $ VarS ("S" ++ show i)
  
-- | 'instantiate' @sorts@: replace all sort variables in @sorts@ with fresh sort variables
instantiate :: [Sort] -> Resolver [Sort]
instantiate sorts = do
  let tvs = Set.toList $ Set.unions (map typeVarsOfSort sorts)
  freshTvs <- replicateM (length tvs) freshSort
  return $ map (sortSubstitute $ Map.fromList $ zip tvs freshTvs) sorts

enforceSame :: Sort -> Sort -> Resolver ()  
enforceSame sl sr
  | sl == sr    = return ()
  | otherwise   = sortConstraints %= (++ [SameSort sl sr])
      
-- | Perform an action and restore the initial environment      
withLocalEnv :: Resolver a -> Resolver a
withLocalEnv c = do
  oldEnv <- use environment
  res <- c
  environment .= oldEnv
  return res
  