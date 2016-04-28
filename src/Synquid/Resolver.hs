{-# LANGUAGE TupleSections, FlexibleContexts, TemplateHaskell #-}

-- | Functions for processing the AST created by the Parser (eg filling in unknown types, verifying that refinement formulas evaluate to a boolean, etc.)
module Synquid.Resolver (resolveDecls, resolveRefinement, resolveRefinedType, ResolverState (..)) where

import Synquid.Program
import Synquid.Logic
import Synquid.Pretty
import Synquid.Util
import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Text.Printf
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

type ErrMsg = String

data ResolverState = ResolverState {
  _environment :: Environment,
  _goals :: [(Id, UProgram)],
  _condQualifiers :: [Formula],
  _typeQualifiers :: [Formula],
  _mutuals :: Map Id [Id],
  _inlines :: Map Id ([Id], Formula)
}

makeLenses ''ResolverState

initResolverState = ResolverState {
  _environment = emptyEnv,
  _goals = [],
  _condQualifiers = [],
  _typeQualifiers = [],
  _mutuals = Map.empty,
  _inlines = Map.empty
}

-- | Convert a parsed program AST into a synthesizable @Goal@ object.
resolveDecls :: [Declaration] -> Either ErrMsg ([Goal], [Formula], [Formula])
resolveDecls declarations = 
  case runExcept (execStateT go initResolverState) of
    Left msg -> Left msg
    Right (ResolverState env goals cquals tquals mutes _) -> 
      Right (map (makeGoal env (map fst goals) mutes) goals, cquals, tquals)
  where
    go = do
      -- Pass 1: collect all declarations and resolve sorts, but do not resolve refinement types yet
      mapM_ resolveDeclaration declarations
      -- Pass 2: resolve refinement types in signatures
      mapM_ resolveSignatures declarations
    makeGoal env allNames allMutuals (name, impl) = 
      let
        spec = allSymbols env Map.! name
        myMutuals = Map.findWithDefault [] name allMutuals
        toRemove = drop (fromJust $ elemIndex name allNames) allNames \\ myMutuals -- All goals after and including @name@, except mutuals
        env' = foldr removeVariable env toRemove
      in Goal name env' spec impl 0
      
resolveRefinement :: Environment -> Sort -> Formula -> Either ErrMsg Formula
resolveRefinement env valueSort fml = runExcept (evalStateT (resolveTypeRefinement valueSort fml) (initResolverState {_environment = env}))

resolveRefinedType :: Environment -> RType -> Either ErrMsg RType
resolveRefinedType env t = runExcept (evalStateT (resolveType t) (initResolverState {_environment = env}))
    
{- Implementation -}    

type Resolver a = StateT ResolverState (Except ErrMsg) a    

resolveDeclaration :: Declaration -> Resolver ()
resolveDeclaration (TypeDecl typeName typeVars typeBody) = do
  typeBody' <- resolveType typeBody
  let extraTypeVars = typeVarsOf typeBody' Set.\\ Set.fromList typeVars
  if Set.null extraTypeVars
    then environment %= addTypeSynonym typeName typeVars typeBody'
    else throwError $ unwords $ ["Type variable(s)"] ++ Set.toList extraTypeVars ++ ["in the definition of type synonym", typeName, "are undefined"]
resolveDeclaration (FuncDecl funcName typeSchema) = addNewSignature funcName typeSchema
resolveDeclaration (DataDecl dataName typeParams predParams constructors) = do
  let
    datatype = DatatypeDef {
      _typeArgs = typeParams,
      _predArgs = predParams,
      _constructors = map constructorName constructors,
      _wfMetric = Nothing
    }
  environment %= addDatatype dataName datatype  
  let addPreds typ = foldl (\s (PredSig p argSorts _) -> ForallP p argSorts s) (Monotype typ) predParams
  mapM_ (\(ConstructorSig name typ) -> addNewSignature name $ addPreds typ) constructors
resolveDeclaration (MeasureDecl measureName inSort outSort post defCases isTermination) = do
  -- Resolve measure signature:
  inSort'' <- resolveSort inSort
  case inSort'' of 
    DataS dtName tArgs -> do
      datatype <- uses (environment . datatypes) (Map.! dtName)
      let inSort' = DataS dtName (map VarS (datatype ^. typeArgs))
      let Right sortSubst = unifySorts [inSort''] [inSort']
      outSort' <- sortSubstitute sortSubst <$> resolveSort outSort      
      environment %= addGlobalPredicate measureName [outSort', inSort']
      -- Possibly add as termination metric:      
      if isTermination
        then if (isJust $ datatype ^. wfMetric) 
              then throwError $ unwords ["Multiple termination metrics defined for datatype", dtName]
              else if outSort' == IntS
                    then environment %= addDatatype dtName datatype { _wfMetric = Just measureName }
                    else throwError $ unwords ["Output sort of termination measure", measureName, "must be Int"]  
        else return ()
    _ -> throwError $ unwords ["Input sort of measure", measureName, "must be a datatype"]  
                  
resolveDeclaration (PredDecl sig) = void $ resolvePredSignature sig True
resolveDeclaration (SynthesisGoal name impl) = do
  syms <- uses environment allSymbols
  if Map.member name syms
    then goals %= (++ [(name, impl)])
    else throwError $ unwords ["No specification found for synthesis goal", name]
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
        Nothing -> throwError $ unwords ["Synthesis goal", name, "in a mutual clause is undefined"]
resolveDeclaration (InlineDecl name args body) = 
  ifM (uses inlines (Map.member name))
    (throwError $ unwords ["Duplicate definition of inline", name])
    (do
      let extraVars = Set.map varName (varsOf body) `Set.difference` Set.fromList args
      if not $ Set.null extraVars
        then throwError $ unwords (["Variables"] ++ Set.toList extraVars ++ ["undefined in the body of inline", name])
        else inlines %= Map.insert name (args, body))
      
resolveSignatures :: Declaration -> Resolver ()      
resolveSignatures (FuncDecl funcName _)  = resolveSignature funcName
resolveSignatures (DataDecl dtName tArgs pArgs ctors) = mapM_ resolveConstructorSignature ctors
  where
    resolveConstructorSignature (ConstructorSig name typ) = do
      sch <- uses environment ((Map.! name) . allSymbols)
      sch' <- resolveSchema sch
      let lastSort = toSort $ baseTypeOf $ lastType typ
      let dtSort = DataS dtName (map VarS tArgs) -- ToDo: compare base types instead
      if dtSort == lastSort
        then do
          let sch'' = addRefinementToLastSch sch' (Var dtSort valueVarName |=| Cons dtSort name (allArgs typ))    
          environment %= addPolyConstant name sch''
        else throwError $ unwords ["Constructor", name, "must return type", show dtSort, ", got", show lastSort]
    
    predApp (PredSig p sorts BoolS) = Pred BoolS p [] -- (zipWith Var sorts deBrujns)
  
resolveSignatures (MeasureDecl measureName _ _ post defCases _) = do
  (outSort : (inSort@(DataS dtName tArgs) : _)) <- uses (environment . globalPredicates) (Map.! measureName)
  datatype <- uses (environment . datatypes) (Map.! dtName)
  post' <- resolveTypeRefinement outSort post
  let ctors = datatype ^. constructors  
  if length defCases /= length ctors
    then throwError $ unwords $ ["Definition of measure", measureName, "must include one case per constructor of", dtName]
    else do
      defs' <- mapM (resolveMeasureDef ctors) defCases
      environment %= addMeasure measureName (MeasureDef inSort outSort defs' post')    
  where
    resolveMeasureDef allCtors (MeasureCase ctorName ctorArgs body) = 
      if not (ctorName `elem` allCtors)
        then throwError $ unwords ["Not in scope: data constructor", ctorName, "used in definition of measure", measureName]
        else do
          sch <- uses environment ((Map.! ctorName) . allSymbols)
          let n = arity $ toMonotype sch
          if n /= length ctorArgs 
            then throwError $ unwords ["Data constructor", ctorName, "expected", show n, "binders and got", show (length ctorArgs), "in definition of measure", measureName]
            else do
              let ctorArgsInType = allArgs $ toMonotype sch
              let subst = Map.fromList (zip ctorArgs (map (\(Var _ name) -> Var AnyS name) $ ctorArgsInType))
              let fml = Pred AnyS measureName [Var AnyS valueVarName] |=| substitute subst body
              sch' <- resolveSchema $ addMeasureRefinement fml sch
              let (ScalarT _ fml') = lastType $ toMonotype sch'
              return $ MeasureCase ctorName (map varName ctorArgsInType) fml'
    addMeasureRefinement fml (ForallT a sch) = addMeasureRefinement fml sch
    addMeasureRefinement fml (ForallP p argSorts sch) = ForallP p argSorts $ addMeasureRefinement fml sch
    addMeasureRefinement fml (Monotype t) = Monotype $ addRefinementToLast (refineTop $ shape t) fml

resolveSignatures _                      = return ()   

{- Types and sorts -}

resolveSchema :: RSchema -> Resolver RSchema
resolveSchema sch = do
  sch' <- resolveSchema' sch
  return $ Foldable.foldl (flip ForallT) sch' $ typeVarsOf (toMonotype sch')
  where
    resolveSchema' (ForallP predName sorts sch) = do
      oldEnv <- use environment
      (_ : sorts') <- resolvePredSignature (PredSig predName sorts BoolS) False
      sch' <- resolveSchema' sch
      environment .= oldEnv
      return $ ForallP predName sorts' sch'
    resolveSchema' (Monotype t) = Monotype <$> resolveType t

resolveType :: RType -> Resolver RType
resolveType (ScalarT (DatatypeT name tArgs pArgs) fml) = do
  ds <- use $ environment . datatypes
  case Map.lookup name ds of
    Nothing -> do
      t' <- substituteTypeSynonym name tArgs >>= resolveType      
      fml' <- resolveTypeRefinement (toSort $ baseTypeOf t') fml
      return $ addRefinement t' fml'
    Just (DatatypeDef tVars pVars _ _) -> do
      let n = length tVars
      when (length tArgs /= n) $ throwError $ unwords ["Datatype", name, "expected", show n, "type arguments and got", show (length tArgs)]
      when (length pArgs /= length pVars) $ throwError $ unwords ["Datatype", name, "expected", show (length pVars), "predicate arguments and got", show (length pArgs)]   
      tArgs' <- mapM resolveType tArgs
      pArgs' <- zipWithM resolvePredArg pVars pArgs
      let baseT' = DatatypeT name tArgs' pArgs'      
      fml' <- resolveTypeRefinement (toSort baseT') fml
      return $ ScalarT baseT' fml'
  where    
    resolvePredArg :: PredSig -> Formula -> Resolver Formula
    resolvePredArg (PredSig _ sorts BoolS) fml = do
      oldEnv <- use environment
      let vars = zipWith Var sorts deBrujns
      environment %= \env -> foldr (\(Var s x) -> addVariable x (fromSort s)) env vars
      res <- case fml of
                Pred _ p [] -> resolveTypeRefinement AnyS (Pred BoolS p vars)
                _ -> resolveTypeRefinement AnyS fml
      environment .= oldEnv      
      return res      
resolveType (ScalarT baseT fml) = ScalarT baseT <$> resolveTypeRefinement (toSort baseT) fml
      
resolveType (FunctionT x tArg tRes) = do
  when (x == valueVarName) $ throwError $
    valueVarName ++ " is a reserved variable name, so you can't bind function arguments to it"
  tArg' <- resolveType tArg
  oldEnv <- use environment
  when (not $ isFunctionType tArg') (environment %= addVariable x tArg')
  tRes' <- resolveType tRes
  environment .= oldEnv
  return $ FunctionT x tArg' tRes'
  
resolveType AnyT = return AnyT  

resolveSort :: Sort -> Resolver Sort
resolveSort (SetS elSort) = SetS <$> resolveSort elSort
resolveSort (DataS name sArgs) = do
  ds <- use $ environment . datatypes
  case Map.lookup name ds of
    Nothing -> do
      t' <- substituteTypeSynonym name (map fromSort sArgs)
      resolveSort $ toSort $ baseTypeOf t'
    Just (DatatypeDef tVars _ _ _) -> do
      let n = length tVars
      when (length sArgs /= n) $ throwError $ unwords ["Datatype", name, "expected", show n, "type arguments and got", show (length sArgs)]
      sArgs' <- mapM resolveSort sArgs
      return $ DataS name sArgs'
resolveSort s = return s
  
{- Formulas -}

resolveTypeRefinement :: Sort -> Formula -> Resolver Formula
resolveTypeRefinement valueSort fml = do
  fml' <- resolveFormula BoolS valueSort fml
  env <- use environment
  let invalidPreds = negPreds fml' `Set.intersection` (Map.keysSet $ env ^. boundPredicates)
  when (not $ Set.null invalidPreds) $ 
    throwError $ unwords ["Bound predicate(s)", show (commaSep (map text $ Set.toList invalidPreds)), "occur negatively in a refinement", show fml']
  return fml'

resolveFormula :: Sort -> Sort -> Formula -> Resolver Formula
resolveFormula targetSort valueSort (SetLit AnyS memberFmls) = do
  _ <- targetSort `unifiedWith` (SetS AnyS)
  case memberFmls of
    [] -> return $ SetLit (elemSort targetSort) []
    (fml:fmls) -> do
      fml' <- resolveFormula (elemSort targetSort) valueSort fml
      let newElemSort = sortOf fml'
      fmls' <- mapM (resolveFormula newElemSort valueSort) fmls
      return $ SetLit newElemSort (fml':fmls')
  where
    elemSort (SetS s) = s
    elemSort AnyS = AnyS  
      
resolveFormula targetSort valueSort (Var AnyS varName) =
  if varName == valueVarName
    then flip Var varName <$> (valueSort `unifiedWith` targetSort)
    else do
      env <- use environment
      case Map.lookup varName (symbolsOfArity 0 env) of
        Just varType ->
          case toMonotype varType of
            ScalarT baseType _ -> flip Var varName <$> (toSort baseType `unifiedWith` targetSort)
            FunctionT _ _ _ -> error "The impossible happened: function in a formula"
        Nothing -> resolveFormula targetSort valueSort (Pred AnyS varName []) `catchError` -- Maybe it's a zero-argument predicate?
                      const (throwError $ printf "Var `%s` is not in scope." varName)      -- but if not, throw this error to avoid confusion
      
resolveFormula targetSort valueSort (Unary op fml) = fmap (Unary op) $ 
    do
      _ <- unifiedWith resSort targetSort
      resolveFormula operandSort valueSort fml
  where
    resSort = case op of
      Not -> BoolS
      _ -> IntS
    operandSort = case op of
      Not -> BoolS
      _ -> IntS

resolveFormula targetSort valueSort (Binary op l r) = 
  if wrongTargetSort op
    then throwError $ unwords ["Encountered binary operation", show op, "where", show targetSort, "was expected"]
    else do
      l' <- resolveFormula (leftSort op) valueSort l
      let lS = sortOf l'
      op' <- newOp op lS
      let rS = right op' lS
      r' <- resolveFormula rS valueSort r
      return $ Binary op' l' r'
  where
    wrongTargetSort op
      | op == Times || op == Plus || op == Minus            = isLeft (unifySorts [targetSort] [IntS]) && isLeft (unifySorts [targetSort] [SetS AnyS])
      | op == Union || op == Intersect || op == Diff        = isLeft (unifySorts [targetSort] [SetS AnyS]) 
      | otherwise                                           = isLeft (unifySorts [targetSort] [BoolS])
  
    leftSort op
      | op == Times || op == Plus || op == Minus            = targetSort
      | op == Eq  || op == Neq                              = AnyS
      | op == Lt || op == Le || op == Gt || op == Ge        = AnyS
      | op == And || op == Or || op == Implies || op == Iff = BoolS
      | op == Member                                        = AnyS
      | op == Union || op == Intersect || op == Diff        = targetSort
      | op == Subset                                        = targetSort
      
    newOp op lSort
      | op == Times || op == Plus || op == Minus  = case lSort of
                                                            IntS -> return op
                                                            SetS a -> return $ toSetOp op
                                                            _ -> throwError $ unwords ["No overloading of", show op, "for", show lSort]
      | op == Le                                  = case lSort of
                                                            IntS -> return op
                                                            VarS _ -> return op
                                                            SetS a -> return $ toSetOp op
                                                            _ -> throwError $ unwords ["No overloading of", show op, "for", show lSort]
      | op == Lt || op == Gt || op == Ge          = case lSort of
                                                            IntS -> return op
                                                            VarS _  -> return op
                                                            _ -> throwError $ unwords ["No overloading of", show op, "for", show lSort]
      | op == Eq  || op == Neq                    = case lSort of
                                                            _ -> return op
      | otherwise                                 = return op
      
    toSetOp Times = Intersect
    toSetOp Plus = Union
    toSetOp Minus = Diff
    toSetOp Le = Subset
      
    right op lSort
      | op == Times || op == Plus || op == Minus            = IntS
      | op == Eq  || op == Neq                              = lSort
      | op == Lt || op == Le || op == Gt || op == Ge        = lSort
      | op == And || op == Or || op == Implies || op == Iff = BoolS
      | op == Union || op == Intersect || op == Diff        = lSort
      | op == Member                                        = SetS lSort
      | op == Subset                                        = lSort
    
resolveFormula targetSort valueSort (Ite cond l r) = do
  cond' <- resolveFormula BoolS valueSort cond
  l' <- resolveFormula targetSort valueSort l
  r' <- resolveFormula (sortOf l') valueSort r
  return $ Ite cond' l' r'
   
resolveFormula targetSort valueSort (Pred AnyS name argFmls) = do
  inlineMb <- uses inlines (Map.lookup name)
  case inlineMb of
    Just (args, body) -> resolveFormula targetSort valueSort (substitute (Map.fromList $ zip args argFmls) body)
    Nothing -> do
      ps <- uses environment allPredicates
      (resSort : argSorts) <- case Map.lookup name ps of
                                Nothing -> throwError $ unwords ["Predicate or measure", name, "is undefined"]
                                Just sorts -> return sorts
      if length argFmls /= length argSorts
          then throwError $ unwords ["Expected", show (length argSorts), "arguments for predicate or measure", name, "and got", show (length argFmls)]
          else do
            (resSort', argFmls') <- unifyArguments valueSort argSorts resSort argFmls targetSort
            return $ Pred resSort' name argFmls'
          
resolveFormula targetSort valueSort (Cons AnyS name argFmls) = do
  syms <- uses environment allSymbols
  case Map.lookup name syms of
    Nothing -> throwError $ unwords ["Data constructor", name, "is undefined"]
    Just consSch -> do
      let consT = toMonotype consSch
      let argSorts = map (toSort . baseTypeOf) $ allArgTypes consT
      let resSort = toSort $ baseTypeOf $ lastType consT
      if length argSorts /= length argFmls
        then throwError $ unwords ["Constructor", name, "expected", show (length argSorts), "arguments and got", show (length argFmls)]
        else do
              (resSort', argFmls') <- unifyArguments valueSort argSorts resSort argFmls targetSort
              return $ Cons resSort' name argFmls'
            
resolveFormula targetSort _ fml = let s = sortOf fml -- Formula of a known type: check
  in if complies targetSort s
    then return fml
    else throwError $ unwords ["Encountered", show s, "where", show targetSort, "was expected"]            
-- resolveFormula targetSort _ fml = -- Formula of a known type: check
  -- case unifySorts [targetSort] [sortOf fml] of
    -- Left (x, y) -> throwError $ unwords ["Cannot unify sorts", show x, "and", show y, "when resolving", show fml]
    -- Right subst -> return $ sortSubstituteFml subst fml

{- Misc -}

-- | @s@ unified with @s'@; @s@ should not contain more unknowns than @s'@
unifiedWith :: Sort -> Sort -> Resolver Sort
unifiedWith s s' = case unifySorts [s] [s'] of
  Left (x, y) -> throwError $ unwords ["Cannot unify sorts", show x, "and", show y]
  Right subst -> return $ sortSubstitute subst s
      
unifyArguments :: Sort -> [Sort] -> Sort -> [Formula] -> Sort -> Resolver (Sort, [Formula])
unifyArguments valueSort argSorts resSort argFmls targetSort = do
  let typeVars = Set.unions (map typeVarsOfSort (resSort : argSorts)) -- Type variables of the argument sorts
  let substAny = constMap typeVars AnyS
  let argSortsAny = map (sortSubstitute substAny) argSorts -- Argument sorts with unknown type parameters
  argFmls' <- zipWithM (flip resolveFormula valueSort) argSortsAny argFmls -- Resolve arguments against argument sorts with unknown type parameters
  
  let substUnique = Map.fromList $ zip (Set.toList typeVars) (map VarS deBrujns)
  let (resSortUnique : argSortsUnique) = map (sortSubstitute substUnique) (resSort : argSorts)
  
  case unifySorts (resSortUnique : argSortsUnique) (targetSort : map sortOf argFmls') of -- Unify required and inferred argument sorts (this can fail if the same type variable has to match two different sorts)
    Left (x, y) -> throwError $ unwords ["Cannot unify sorts", show x, "and", show y]
    Right subst -> return $ (sortSubstitute subst resSortUnique, argFmls')      
    
addNewSignature name sch = do
  ifM (Set.member name <$> use (environment . constants)) (throwError $ unwords ["Duplicate declaration of function", name]) (return ())
  environment %= addPolyConstant name sch
  environment %= addUnresolvedConstant name sch
  
resolveSignature name = do
  sch <- uses environment ((Map.! name) . allSymbols)
  sch' <- resolveSchema sch
  environment %= addPolyConstant name sch'
  
resolvePredSignature (PredSig name argSorts resSort) global = do
  ifM (Map.member name <$> uses environment allPredicates) (throwError $ unwords ["Duplicate declaration of predicate", name]) (return ())
  sorts' <- mapM resolveSort (resSort : argSorts)
  environment %= if global then addGlobalPredicate name sorts' else addBoundPredicate name sorts'
  return sorts'
  
substituteTypeSynonym name tArgs = do
  tss <- use $ environment . typeSynonyms
  case Map.lookup name tss of
    Nothing -> throwError $ unwords ["Datatype or synonym", name, "is undefined"]
    Just (tVars, t) -> do
      when (length tArgs /= length tVars) $ throwError $ unwords ["Type synonym", name, "expected", show (length tVars), "type arguments and got", show (length tArgs)]
      let tempVars = take (length tVars) deBrujns
      let t' = typeSubstitute (Map.fromList $ zip tVars (map vartAll tempVars)) t -- We need to do this since tVars and tArgs are not necessarily disjoint
      return $ typeSubstitute (Map.fromList $ zip tempVars tArgs) t'
