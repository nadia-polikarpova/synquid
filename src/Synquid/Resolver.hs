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
resolveDeclaration (TypeDecl typeName typeBody) = do
  typeBody' <- resolveType typeBody
  environment %= addTypeSynonym typeName typeBody'
resolveDeclaration (FuncDecl funcName typeSchema) = resolveSignature funcName typeSchema
resolveDeclaration (DataDecl dataName typeParams wfMetricMb constructors) = do
  case wfMetricMb of
    Nothing -> return ()
    Just wfMetric -> do
      ifM (not . Map.member wfMetric <$> (use $ environment . measures)) (throwError $ unwords ["Measure", wfMetric, "is undefined"]) (return ())
  let
    datatype = DatatypeDef {
      _typeArgCount = length typeParams,
      _constructors = map constructorName constructors,
      _wfMetric = wfMetricMb
    }
  environment %= addDatatype dataName datatype
  mapM_ (\(ConstructorDef name schema) -> resolveSignature name schema) constructors
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
resolveSchema (Monotype t) = do
  t' <- resolveType t
  return $ Foldable.foldl (flip Forall) (Monotype t') $ typeVarsOf t'

resolveType :: RType -> Resolver RType
resolveType (ScalarT baseType typeFml) = do
  baseType' <- resolveBase baseType
  typeFml' <- resolveFormula BoolS (toSort baseType) typeFml
  typeSyns <- use $ environment . typeSynonyms
  return $ substituteTypeSynonym typeSyns $ ScalarT baseType' typeFml'
  where
    resolveBase (DatatypeT name tArgs) = do
      ds <- use $ environment . datatypes
      case Map.lookup name ds of
        Nothing -> do
          tss <- use $ environment . typeSynonyms
          case Map.lookup name tss of
            Nothing -> throwError $ unwords ["Datatype or synonym", name, "is undefined"]
            Just _ -> when (not $ null tArgs) $ throwError $ unwords ["Type synonym", name, "did not expect type arguments"]    
        Just (DatatypeDef n _ _) -> when (length tArgs /= n) $ throwError $ unwords ["Datatype", name, "expected", show n, "type arguments and got", show (length tArgs)]   
      DatatypeT name <$> mapM resolveType tArgs
    resolveBase baseT = return baseT
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
        let newElemSort = fromJust $ sortOf fml'
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
  let lS = fromJust $ sortOf l'
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
      let (DataS _ tArgs) = fromJust $ sortOf argFml'
      let outSort' = sortSubstitute (Map.fromList $ zip (map (\(VarS a) -> a) tVars) tArgs) outSort
      if complies outSort' targetSort
        then return $ Measure outSort' name argFml'
        else throwError $ unwords ["Enountered measure", name, "where", show targetSort, "was expected"]
    
resolveFormula targetSort _ fml = let s = fromJust $ sortOf fml -- Formula of a known type: check
  in if complies targetSort s
    then return fml
    else throwError $ unwords ["Enountered", show s, "where", show targetSort, "was expected"]

{- Misc -}

substituteTypeSynonym :: TypeSubstitution -> RType -> RType
substituteTypeSynonym synonyms rtype@(ScalarT (DatatypeT typeName typeArgs) refinement) =
  case synonyms ^. at typeName of
    Just val -> addRefinement val refinement -- TODO: add polymorphic synonyms 
    Nothing -> rtype
substituteTypeSynonym synonyms (FunctionT argId argRef returnRef) = FunctionT argId (substituteTypeSynonym synonyms argRef) (substituteTypeSynonym synonyms returnRef)
substituteTypeSynonym synonyms rtype = rtype

resolveSignature name sch = do
  ifM (Set.member name <$> use (environment . constants)) (throwError $ unwords ["Duplicate declaration of funtion", name]) (return ())
  sch' <- resolveSchema sch
  environment %= addPolyConstant name sch'
