{-# LANGUAGE TupleSections, FlexibleContexts, TemplateHaskell #-}

-- | Functions for processing the AST created by the Parser (eg filling in unknown types, verifying that refinement formulas evaluate to a boolean, etc.)
module Synquid.Resolver (resolveProgramAst, resolveRefinement, resolveType, ResolverState (..)) where

import Synquid.Program
import Synquid.Explorer
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


{- Interface -}

type ErrMsg = String

data ResolverState = ResolverState {
  _environment :: Environment,
  _goalNames :: [Id],
  _condQualifiers :: [Formula],
  _typeQualifiers :: [Formula]
}

makeLenses ''ResolverState

-- | Convert a parsed program AST into a synthesizable @Goal@ object.
resolveProgramAst :: ProgramAst -> Either ErrMsg ([Goal], [Formula], [Formula])
resolveProgramAst declarations = 
  case runExcept (execStateT (mapM_ resolveDeclaration declarations) (ResolverState emptyEnv [] [] [])) of
    Left msg -> Left msg
    Right (ResolverState env gNames cquals tquals) -> Right (map (makeGoal env gNames) gNames, cquals, tquals)
  where
    makeGoal env allNames name = 
      let
        spec = allSymbols env Map.! name
        toRemove = drop (fromJust $ elemIndex name allNames) allNames -- All goals after and including @name@
        env' = foldr removeVariable env toRemove
      in Goal name env' spec
      
resolveRefinement :: Environment -> Sort -> Formula -> Maybe Formula
resolveRefinement env valueSort fml = case runExcept (evalStateT (resolveFormula BoolS valueSort fml) (ResolverState env [] [] [])) of
    Left _ -> Nothing
    Right fml' -> Just fml'
    
{- Implementation -}    

type Resolver a = StateT ResolverState (Except ErrMsg) a    

resolveDeclaration :: Declaration -> Resolver ()
resolveDeclaration (TypeDecl typeName typeVars typeBody) = do
  typeBody' <- resolveType typeBody
  let extraTypeVars = typeVarsOf typeBody' Set.\\ Set.fromList typeVars
  if Set.null extraTypeVars
    then environment %= addTypeSynonym typeName typeVars typeBody'
    else throwError $ unwords $ ["Type variable(s)"] ++ Set.toList extraTypeVars ++ ["in the defintion of type synonym", typeName, "are undefined"]
resolveDeclaration (FuncDecl funcName typeSchema) = resolveSignature funcName typeSchema
resolveDeclaration (DataDecl dataName typeParams predParams wfMetricMb constructors) = do
  case wfMetricMb of
    Nothing -> return ()
    Just wfMetric -> do
      ifM (not . Map.member wfMetric <$> (use $ environment . measures)) (throwError $ unwords ["Measure", wfMetric, "is undefined"]) (return ())
  -- ToDo: check sorts in predParams
  let
    datatype = DatatypeDef {
      _typeArgCount = length typeParams,
      _predArgs = map (\(PredDecl _ sorts) -> sorts) predParams,
      _constructors = map constructorName constructors,
      _wfMetric = wfMetricMb
    }
  environment %= addDatatype dataName datatype
  let addPreds sch = foldl (\s (PredDecl p sorts) -> ForallP p sorts s) sch predParams
  mapM_ (\(ConstructorDef name schema) -> resolveSignature name $ addPreds schema) constructors
resolveDeclaration (MeasureDecl measureName inSort outSort post) = do
  post' <- resolveFormula BoolS outSort post
  environment %= addMeasure measureName (MeasureDef inSort outSort post')
resolveDeclaration (SynthesisGoal name) = do
  syms <- uses environment allSymbols
  if Map.member name syms
    then goalNames %= (++ [name])
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
      environment %= addPredicate predName sorts
      sch' <- resolveSchema' sch
      environment .= oldEnv
      return $ ForallP predName sorts sch'
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
                Pred p [] -> resolveFormula BoolS UnknownS (Pred p vars)
                _ -> resolveFormula BoolS UnknownS fml
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
  
{- Formulas -}  

resolveFormula :: Sort -> Sort -> Formula -> Resolver Formula
resolveFormula targetSort valueSort (SetLit UnknownS memberFmls) = 
  if complies targetSort (SetS UnknownS)
    then case memberFmls of
      [] -> return $ SetLit (elemSort targetSort) []
      (fml:fmls) -> do
        fml' <- resolveFormula (elemSort targetSort) valueSort fml
        let newElemSort = sortOf fml'
        fmls' <- mapM (resolveFormula newElemSort valueSort) fmls
        return $ SetLit newElemSort (fml':fmls')
    else throwError $ unwords ["Enountered set literal where", show targetSort, "was expected"]
  where
    elemSort (SetS s) = s
    elemSort UnknownS = UnknownS  
      
resolveFormula targetSort valueSort (Var UnknownS varName) =
  if varName == valueVarName
    then if complies targetSort valueSort 
          then return $ Var valueSort varName
          else throwError $ unwords ["Enountered value variable of sort", show valueSort, "where", show targetSort, "was expected"]
    else do
      env <- use environment
      case Map.lookup varName (symbolsOfArity 0 env) of
        Just varType ->
          case toMonotype varType of
            ScalarT baseType _ -> let s = toSort baseType in 
              if complies targetSort s  
                then return $ Var s varName
                else throwError $ unwords ["Enountered variable of sort", show s, "where", show targetSort, "was expected"]
            FunctionT _ _ _ -> error "The impossible happened: function in a formula"
        Nothing -> throwError $ printf "Var `%s` is not in scope." varName
      
resolveFormula targetSort valueSort (Unary op fml) = fmap (Unary op) $ 
    if complies resSort targetSort
      then resolveFormula operandSort valueSort fml
      else throwError $ unwords ["Enountered unary operation", show op, "where", show targetSort, "was expected"]
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
    else throwError $ unwords ["Enountered binary operation", show op, "where", show targetSort, "was expected"]
  where
    leftSort op
      | op == Times || op == Plus || op == Minus            = UnknownS
      | op == Eq  || op == Neq                              = UnknownS
      | op == Lt || op == Le || op == Gt || op == Ge        = UnknownS
      | op == And || op == Or || op == Implies || op == Iff = BoolS
      | op == Member                                        = UnknownS
      | op == Union || op == Intersect || op == Diff        = SetS UnknownS
      | op == Subset                                        = SetS UnknownS
      
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
                                                            DataS _ _ -> throwError $ unwords ["No overloading of", show op, "for", show lSort]
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
    
  
resolveFormula targetSort valueSort (Measure UnknownS name argFml) = do
  ms <- use $ environment . measures
  case Map.lookup name ms of
    Nothing -> throwError $ unwords ["Measure", name, "is undefined"]
    Just (MeasureDef (DataS dtName tVars) outSort _) -> do
      argFml' <- resolveFormula (DataS dtName $ replicate (length tVars) UnknownS) valueSort argFml
      let (DataS _ tArgs) = sortOf argFml'
      let outSort' = sortSubstitute (Map.fromList $ zip (map (\(VarS a) -> a) tVars) tArgs) outSort
      if complies outSort' targetSort
        then return $ Measure outSort' name argFml'
        else throwError $ unwords ["Enountered measure", name, "where", show targetSort, "was expected"]
        
resolveFormula targetSort valueSort (Cons UnknownS name argFmls) = do
  syms <- uses environment allSymbols
  case Map.lookup name syms of
    Nothing -> throwError $ unwords ["Predicate or constructor", name, "is undefined"]
    Just consSch -> do
      let consT = toMonotype consSch
      let argSorts = map (toSort . baseTypeOf) $ allArgTypes consT
      let resSort = toSort $ baseTypeOf $ lastType consT
      -- let typeVars = Set.toList $ typeVarsOf consT -- ToDo: order!
      -- let consT' = sortSubstitute (Map.fromList $ zip typeVars (repreat UnknownS)) consT
      if complies targetSort resSort -- ToDo: substitute type variables
        then if length argSorts /= length argFmls
                then throwError $ unwords ["Constructor", name, "expected", show (length argSorts), "arguments and got", show (length argFmls)]
                else Cons resSort name <$> zipWithM (flip resolveFormula valueSort) argSorts argFmls
        else throwError $ unwords ["Enountered constructor", name, "where", show targetSort, "was expected"]
        
resolveFormula targetSort valueSort (Pred name argFmls) = do
  ps <- use $ environment . boundPredicates
  case Map.lookup name ps of
    Nothing -> resolveFormula targetSort valueSort (Cons UnknownS name argFmls)
    Just argSorts -> if length argFmls /= length argSorts
                      then throwError $ unwords ["Expected", show (length argSorts), "arguments for predicate", name, "and got", show (length argFmls)]
                      else if complies targetSort BoolS 
                        then Pred name <$> zipWithM (flip resolveFormula valueSort) argSorts argFmls
                        else throwError $ unwords ["Enountered a predicate where", show targetSort, "was expected"]
    
resolveFormula targetSort _ fml = let s = sortOf fml -- Formula of a known type: check
  in if complies targetSort s
    then return fml
    else throwError $ unwords ["Enountered", show s, "where", show targetSort, "was expected"]

{- Misc -}

resolveSignature name sch = do
  ifM (Set.member name <$> use (environment . constants)) (throwError $ unwords ["Duplicate declaration of funtion", name]) (return ())
  sch' <- resolveSchema sch
  environment %= addPolyConstant name sch'
