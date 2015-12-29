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
import qualified Data.Set as Set
import Data.Maybe
import Data.List
import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable

{- Interface -}

type ErrMsg = String

data ResolverState = ResolverState {
  _environment :: Environment,
  _goals :: [(Id, UProgram)],
  _condQualifiers :: [Formula],
  _typeQualifiers :: [Formula]
}

makeLenses ''ResolverState

-- | Convert a parsed program AST into a synthesizable @Goal@ object.
resolveDecls :: [Declaration] -> Either ErrMsg ([Goal], [Formula], [Formula])
resolveDecls declarations = 
  case runExcept (execStateT go (ResolverState emptyEnv [] [] [])) of
    Left msg -> Left msg
    Right (ResolverState env goals cquals tquals) -> Right (map (makeGoal env (map fst goals)) goals, cquals, tquals)
  where
    go = do
      -- Pass 1: collect all declarations and resolve sorts, but do not resolve refinement types yet
      mapM_ resolveDeclaration declarations
      -- Pass 2: resolve refinement types in signatures
      syms <- uses environment allSymbols
      syms' <- Traversable.mapM resolveSchema syms
      environment %= flip (Map.foldWithKey addPolyConstant) syms' 
    makeGoal env allNames (name, impl) = 
      let
        spec = allSymbols env Map.! name
        toRemove = drop (fromJust $ elemIndex name allNames) allNames -- All goals after and including @name@
        env' = foldr removeVariable env toRemove
      in Goal name env' spec impl
      
resolveRefinement :: Environment -> Sort -> Formula -> Either ErrMsg Formula
resolveRefinement env valueSort fml = runExcept (evalStateT (resolveFormula BoolS valueSort fml) (ResolverState env [] [] []))

resolveRefinedType :: Environment -> RType -> Either ErrMsg RType
resolveRefinedType env t = runExcept (evalStateT (resolveType t) (ResolverState env [] [] []))
    
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
      _typeArgCount = length typeParams,
      _predArgs = map (\(PredSig _ sorts) -> sorts) predParams,
      _constructors = map constructorName constructors,
      _wfMetric = Nothing
    }
  environment %= addDatatype dataName datatype
  let addPreds sch = foldl (\s (PredSig p sorts) -> ForallP p sorts s) sch predParams
  mapM_ (\(ConstructorSig name schema) -> addNewSignature name $ addPreds schema) constructors
resolveDeclaration (MeasureDecl measureName inSort outSort post defCases isTermination) = do
  -- Resolve measure signature:
  inSort'@(DataS dtName _) <- resolveSort inSort
  outSort' <- resolveSort outSort
  post' <- resolveFormula BoolS outSort' post
  environment %= addMeasure measureName (MeasureDef inSort' outSort' post')
  -- Possibly add as termination metric:
  datatype <- uses (environment . datatypes) (Map.! dtName)
  if isTermination
    then environment %= addDatatype dtName datatype { _wfMetric = Just measureName }
    else return ()
  -- Insert definition cases as refinements into constructor types:
  let ctors = datatype ^. constructors
  if length defCases /= length ctors
    then throwError $ unwords $ ["Definition of measure", measureName, "must include one case per constructor of", dtName]
    else mapM_ (resolveMeasureDef ctors) defCases
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
              let subst = Map.fromList (zip ctorArgs (map (\(Var _ name) -> Var AnyS name) $ allArgs $ toMonotype sch))
              let fml = Measure AnyS measureName (Var AnyS valueVarName) |=| substitute subst body
              -- sch' <- resolveSchema $ addMeasureRefinement fml sch
              environment %= addPolyConstant ctorName (addMeasureRefinement fml sch)
    addMeasureRefinement fml (ForallT a sch) = addMeasureRefinement fml sch
    addMeasureRefinement fml (ForallP p argSorts sch) = ForallP p argSorts $ addMeasureRefinement fml sch
    addMeasureRefinement fml (Monotype t) = Monotype $ addRefinementToLast t fml
                  
resolveDeclaration (PredDecl (PredSig name sorts)) = void $ resolvePredSignature name sorts
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

{- Types -}

resolveSchema :: RSchema -> Resolver RSchema
resolveSchema sch = do
  sch' <- resolveSchema' sch
  return $ Foldable.foldl (flip ForallT) sch' $ typeVarsOf (toMonotype sch')
  where
    resolveSchema' (ForallP predName sorts sch) = do
      oldEnv <- use environment
      sorts' <- resolvePredSignature predName sorts
      sch' <- resolveSchema' sch
      environment .= oldEnv
      return $ ForallP predName sorts' sch'
    resolveSchema' (Monotype t) = Monotype <$> resolveType t

resolveType :: RType -> Resolver RType
resolveType (ScalarT (DatatypeT name tArgs pArgs) fml) = do
  ds <- use $ environment . datatypes
  case Map.lookup name ds of
    Nothing -> do
      tss <- use $ environment . typeSynonyms
      case Map.lookup name tss of
        Nothing -> throwError $ unwords ["Datatype or synonym", name, "is undefined"]
        Just (tVars, t) -> do
          when (length tArgs /= length tVars) $ throwError $ unwords ["Type synonym", name, "expected", show (length tVars), "type arguments and got", show (length tArgs)]
          let tempVars = take (length tVars) deBrujns
          let t' = typeSubstitute (Map.fromList $ zip tVars (map vartAll tempVars)) t -- We need to do this since tVars and tArgs are not necessarily disjoint
          let t'' = typeSubstitute (Map.fromList $ zip tempVars tArgs) t'
          fml' <- resolveFormula BoolS (toSort $ baseTypeOf t'') fml
          return $ addRefinement t'' fml'
    Just (DatatypeDef n pVars _ _) -> do
      when (length tArgs /= n) $ throwError $ unwords ["Datatype", name, "expected", show n, "type arguments and got", show (length tArgs)]
      when (length pArgs /= length pVars) $ throwError $ unwords ["Datatype", name, "expected", show (length pVars), "predicate arguments and got", show (length pArgs)]   
      tArgs' <- mapM resolveType tArgs
      pArgs' <- zipWithM resolvePredArg pVars pArgs
      let baseT' = DatatypeT name tArgs' pArgs'      
      fml' <- resolveFormula BoolS (toSort baseT') fml
      return $ ScalarT baseT' fml'
  where    
    resolvePredArg :: [Sort] -> Formula -> Resolver Formula
    resolvePredArg sorts fml = do
      oldEnv <- use environment
      let vars = zipWith Var sorts deBrujns
      environment %= \env -> foldr (\(Var s x) -> addVariable x (fromSort s)) env vars
      res <- case fml of
                Pred p [] -> resolveFormula BoolS AnyS (Pred p vars)
                _ -> resolveFormula BoolS AnyS fml
      environment .= oldEnv      
      return res      
resolveType (ScalarT baseT fml) = ScalarT baseT <$> resolveFormula BoolS (toSort baseT) fml
      
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
  
{- Formulas -}  

resolveFormula :: Sort -> Sort -> Formula -> Resolver Formula
resolveFormula targetSort valueSort (SetLit AnyS memberFmls) = 
  if complies targetSort (SetS AnyS)
    then case memberFmls of
      [] -> return $ SetLit (elemSort targetSort) []
      (fml:fmls) -> do
        fml' <- resolveFormula (elemSort targetSort) valueSort fml
        let newElemSort = sortOf fml'
        fmls' <- mapM (resolveFormula newElemSort valueSort) fmls
        return $ SetLit newElemSort (fml':fmls')
    else throwError $ unwords ["Encountered set literal where", show targetSort, "was expected"]
  where
    elemSort (SetS s) = s
    elemSort AnyS = AnyS  
      
resolveFormula targetSort valueSort (Var AnyS varName) =
  if varName == valueVarName
    then if complies targetSort valueSort 
          then return $ Var valueSort varName
          else throwError $ unwords ["Encountered value variable of sort", show valueSort, "where", show targetSort, "was expected"]
    else do
      env <- use environment
      case Map.lookup varName (symbolsOfArity 0 env) of
        Just varType ->
          case toMonotype varType of
            ScalarT baseType _ -> let s = toSort baseType in 
              if complies targetSort s  
                then return $ Var s varName
                else throwError $ unwords ["Encountered variable of sort", show s, "where", show targetSort, "was expected"]
            FunctionT _ _ _ -> error "The impossible happened: function in a formula"
        Nothing -> throwError $ printf "Var `%s` is not in scope." varName
      
resolveFormula targetSort valueSort (Unary op fml) = fmap (Unary op) $ 
    if complies resSort targetSort
      then resolveFormula operandSort valueSort fml
      else throwError $ unwords ["Encountered unary operation", show op, "where", show targetSort, "was expected"]
  where
    resSort = case op of
      Not -> BoolS
      _ -> IntS
    operandSort = case op of
      Not -> BoolS
      _ -> IntS

resolveFormula targetSort valueSort (Binary op l r) = do
  l' <- resolveFormula (leftSort op) valueSort l
  let lS = sortOf l'
  op' <- newOp op lS
  let (rS, resS) = rightRes op' lS
  r' <- resolveFormula rS valueSort r
  if complies resS targetSort
    then return $ Binary op' l' r'
    else throwError $ unwords ["Encountered binary operation", show op, "where", show targetSort, "was expected"]
  where
    leftSort op
      | op == Times || op == Plus || op == Minus            = AnyS
      | op == Eq  || op == Neq                              = AnyS
      | op == Lt || op == Le || op == Gt || op == Ge        = AnyS
      | op == And || op == Or || op == Implies || op == Iff = BoolS
      | op == Member                                        = AnyS
      | op == Union || op == Intersect || op == Diff        = SetS AnyS
      | op == Subset                                        = SetS AnyS
      
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
                                                            -- DataS _ _ -> throwError $ unwords ["No overloading of", show op, "for", show lSort]
                                                            _ -> return op
      | otherwise                                 = return op
      
    toSetOp Times = Intersect
    toSetOp Plus = Union
    toSetOp Minus = Diff
    toSetOp Le = Subset
      
    rightRes op lSort
      | op == Times || op == Plus || op == Minus            = (IntS, IntS)
      | op == Eq  || op == Neq                              = (lSort, BoolS)
      | op == Lt || op == Le || op == Gt || op == Ge        = (lSort, BoolS)
      | op == And || op == Or || op == Implies || op == Iff = (BoolS, BoolS)
      | op == Union || op == Intersect || op == Diff        = (lSort, lSort)
      | op == Member                                        = (SetS lSort, BoolS)
      | op == Subset                                        = (lSort, BoolS)
    
resolveFormula targetSort valueSort (Ite cond l r) = do
  cond' <- resolveFormula BoolS valueSort cond
  l' <- resolveFormula targetSort valueSort l
  r' <- resolveFormula targetSort valueSort r
  return $ Ite cond' l' r'
  
resolveFormula targetSort valueSort (Measure AnyS name argFml) = do
  ms <- use $ environment . measures
  case Map.lookup name ms of
    Nothing -> throwError $ unwords ["Measure", name, "is undefined"]
    Just (MeasureDef (DataS dtName tVars) outSort _) -> do
      argFml' <- resolveFormula (DataS dtName $ replicate (length tVars) AnyS) valueSort argFml
      let (DataS _ tArgs) = sortOf argFml'
      let outSort' = sortSubstitute (Map.fromList $ zip (map (\(VarS a) -> a) tVars) tArgs) outSort
      if complies outSort' targetSort
        then return $ Measure outSort' name argFml'
        else throwError $ unwords ["Encountered measure", name, "where", show targetSort, "was expected"]
        
resolveFormula targetSort valueSort (Cons AnyS name argFmls) = do
  syms <- uses environment allSymbols
  case Map.lookup name syms of
    Nothing -> throwError $ unwords ["Predicate or constructor", name, "is undefined"]
    Just consSch -> do
      let consT = toMonotype consSch
      let argSorts = map (toSort . baseTypeOf) $ allArgTypes consT
      let resSort = toSort $ baseTypeOf $ lastType consT
      -- let typeVars = Set.toList $ typeVarsOf consT -- ToDo: order!
      -- let consT' = sortSubstitute (Map.fromList $ zip typeVars (repreat AnyS)) consT
      if complies targetSort resSort -- ToDo: substitute type variables
        then if length argSorts /= length argFmls
                then throwError $ unwords ["Constructor", name, "expected", show (length argSorts), "arguments and got", show (length argFmls)]
                else Cons resSort name <$> zipWithM (flip resolveFormula valueSort) argSorts argFmls
        else throwError $ unwords ["Encountered constructor", name, "where", show targetSort, "was expected"]
        
resolveFormula targetSort valueSort (Pred name argFmls) = do
  ps <- use $ environment . boundPredicates
  case Map.lookup name ps of
    Nothing -> resolveFormula targetSort valueSort (Cons AnyS name argFmls)
    Just argSorts -> if length argFmls /= length argSorts
                      then throwError $ unwords ["Expected", show (length argSorts), "arguments for predicate", name, "and got", show (length argFmls)]
                      else if complies targetSort BoolS 
                        then Pred name <$> zipWithM (flip resolveFormula valueSort) argSorts argFmls
                        else throwError $ unwords ["Encountered a predicate where", show targetSort, "was expected"]
    
resolveFormula targetSort _ fml = let s = sortOf fml -- Formula of a known type: check
  in if complies targetSort s
    then return fml
    else throwError $ unwords ["Encountered", show s, "where", show targetSort, "was expected"]

{- Misc -}

addNewSignature name sch = do
  ifM (Set.member name <$> use (environment . constants)) (throwError $ unwords ["Duplicate declaration of function", name]) (return ())
  environment %= addPolyConstant name sch
  
resolvePredSignature name sorts = do
  ifM (Map.member name <$> use (environment . boundPredicates)) (throwError $ unwords ["Duplicate declaration of predicate", name]) (return ())
  sorts' <- mapM resolveSort sorts
  environment %= addPredicate name sorts'
  return sorts'
  
resolveSort (SetS elSort) = SetS <$> resolveSort elSort        
resolveSort s = do
  t <- resolveType $ fromSort s
  return $ toSort $ baseTypeOf t
