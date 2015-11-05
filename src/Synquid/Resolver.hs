{-# LANGUAGE TupleSections, FlexibleContexts #-}

-- | Functions for processing the AST created by the Parser (eg filling in unknown types, verifying that refinement formulas evaluate to a boolean, etc.)
module Synquid.Resolver where

import Synquid.Program
import Synquid.Explorer
import Synquid.Logic
import Synquid.Pretty
import Control.Applicative
import Control.Monad.Except
import Text.Printf
import Control.Lens
import Data.Maybe
import Data.List
import qualified Data.Foldable as Foldable

type ErrMsg = String
type ResolverError = Either ErrMsg

-- | A convenience function that allows us to use Maybes with error messages in the @ResolverError@ monad.
maybeErr :: Maybe a -> ErrMsg -> ResolverError a
maybeErr (Just a) _ = return a
maybeErr Nothing errMsg = throwError errMsg

-- | Convert a parsed program AST into a synthesizable @Goal@ object.
resolveProgramAst :: ProgramAst -> ResolverError Goal
resolveProgramAst declarations = do
  env <- foldM (resolveDeclaration) emptyEnv declarations
  (SynthesisGoal goalName) <- maybeErr (find isSynthesisGoal declarations) "No synthesis goal specified"
  goalType <- maybeErr (allSymbols env ^. at goalName) "No type signature for synthesis goal"
  return $ Goal goalName (removeVariable goalName env) goalType undefined
  where
    isSynthesisGoal (SynthesisGoal _) = True
    isSynthesisGoal _ = False

substituteTypeSynonym :: TypeSubstitution -> RType -> RType
substituteTypeSynonym synonyms rtype@(ScalarT (DatatypeT typeName typeArgs) refinement) =
  case synonyms ^. at typeName of
    Just val -> addRefinement val refinement -- TODO: add polymorphic synonyms 
    Nothing -> rtype
substituteTypeSynonym synonyms (FunctionT argId argRef returnRef) = FunctionT argId (substituteTypeSynonym synonyms argRef) (substituteTypeSynonym synonyms returnRef)
substituteTypeSynonym synonyms rtype = rtype

resolveDeclaration :: Environment -> Declaration -> ResolverError Environment
resolveDeclaration env (TypeDef typeName typeBody) = do
  typeBody' <- resolveType env typeBody
  return $ addTypeSynonym typeName typeBody' env
resolveDeclaration env (FuncDef funcName typeSchema) = do
  typeSchema' <- resolveSchema env typeSchema
  return $ addPolyConstant funcName typeSchema' env
resolveDeclaration env (DataDef dataName typeParams wfMetricMb constructors) = do
  let
    datatype = Datatype {
      _typeArgCount = length typeParams,
      _constructors = map constructorName constructors,
      _wfMetric = wfMetricMb
    }
  constructors' <- mapM (\ (ConstructorDef name schema) -> fmap (name,) $ resolveSchema env schema) constructors
  return $ foldl (\ env (id', schema) -> addPolyConstant id' schema env) (addDatatype dataName datatype env) constructors'
resolveDeclaration env (MeasureDef measureName inSort outSort) = return $ addMeasure measureName (inSort, outSort) env
resolveDeclaration env (SynthesisGoal _) = return env

resolveSchema :: Environment -> RSchema -> ResolverError RSchema
resolveSchema env (Monotype typeSkel) = do
  typeSkel' <- resolveType env typeSkel
  return $ Foldable.foldl (flip Forall) (Monotype typeSkel') $ typeVarsOf typeSkel'
-- resolveSchema env (Forall id' schemaSkel) = fmap (Forall id') $ resolveSchema env schemaSkel

resolveType :: Environment -> RType -> ResolverError RType
resolveType env (ScalarT baseType typeFml) = do
  baseType' <- resolveBase baseType
  typeFml' <- resolveFormula BoolS (toSort baseType) env typeFml
  return $ substituteTypeSynonym (env ^. typeSynonyms) $ ScalarT baseType' typeFml'
  where
    resolveBase (DatatypeT name tArgs) = DatatypeT name <$> mapM (resolveType env) tArgs
    resolveBase baseT = return baseT
resolveType env (FunctionT x tArg tRes) = do
  when (x == valueVarName) $ throwError $
    valueVarName ++ " is a reserved variable name, so you can't bind function arguments to it"
  tArg' <- resolveType env tArg
  let env' = if isFunctionType tArg' then env else addVariable x tArg' env
  tRes' <- resolveType env' tRes
  return $ FunctionT x tArg' tRes'

-- | 'complies' @s s'@: are @s@ and @s'@ the same modulo unknowns?
complies :: Sort -> Sort -> Bool  
complies UnknownS s = True  
complies s UnknownS = True
complies (SetS s) (SetS s') = complies s s'
complies s s' = s == s'

resolveFormula :: Sort -> Sort -> Environment -> Formula -> ResolverError Formula
resolveFormula targetSort valueSort env (SetLit UnknownS memberFmls) = 
  if complies targetSort (SetS UnknownS)
    then case memberFmls of
      [] -> return $ SetLit (elemSort targetSort) []
      (fml:fmls) -> do
        fml' <- resolveFormula (elemSort targetSort) valueSort env fml
        let newElemSort = fromJust $ sortOf fml'
        fmls' <- mapM (resolveFormula newElemSort valueSort env) fmls
        return $ SetLit newElemSort (fml':fmls')
    else throwError $ unwords ["Enountered set literal where", show targetSort, "was expected"]
  where
    elemSort (SetS s) = s
    elemSort UnknownS = UnknownS  
      
resolveFormula targetSort valueSort env (Var UnknownS varName) =
  if varName == valueVarName
    then if complies targetSort valueSort 
          then return $ Var valueSort varName
          else throwError $ unwords ["Enountered value variable of sort", show valueSort, "where", show targetSort, "was expected"]
    else case env ^. symbols ^. at 0 >>= view (at varName) of
      Just varType ->
        case toMonotype varType of
          ScalarT baseType _ -> let s = toSort baseType in 
            if complies targetSort s  
              then return $ Var s varName
              else throwError $ unwords ["Enountered variable of sort", show s, "where", show targetSort, "was expected"]
          FunctionT _ _ _ -> error "The impossible happened: function in a formula"
      Nothing -> throwError $ printf "Var `%s` is not in scope." varName
      
resolveFormula targetSort valueSort env (Unary op fml) = fmap (Unary op) $ 
    if complies resSort targetSort
      then resolveFormula operandSort valueSort env fml
      else throwError $ unwords ["Enountered unary operation", show op, "where", show targetSort, "was expected"]
  where
    resSort = case op of
      Not -> BoolS
      _ -> IntS
    operandSort = case op of
      Not -> BoolS
      _ -> IntS

resolveFormula targetSort valueSort env (Binary op l r) = do
  l' <- resolveFormula (leftSort op) valueSort env l
  let lS = fromJust $ sortOf l'
  op' <- newOp op lS
  let (rS, resS) = rightRes op' lS
  r' <- resolveFormula rS valueSort env r
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
      
    newOp op lSort
      | op == Times || op == Plus || op == Minus || op == Le = case lSort of
                                                                IntS -> return op
                                                                SetS a -> return $ toSetOp op
                                                                _ -> throwError $ unwords ["No overloading of", show op, "for", show lSort]
      | otherwise                                           = return op
      
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
    
  
resolveFormula targetSort valueSort env (Measure UnknownS name argFml) = do
  case env ^. measures ^. at name of
    Nothing -> throwError $ name ++ " is undefined"
    Just (inSort, outSort) -> do
      argFml' <- resolveFormula inSort valueSort env argFml
      if complies outSort targetSort  -- TODO: type parameter substitution
        then return $ Measure outSort name argFml'
        else throwError $ unwords ["Enountered measure", name, "where", show targetSort, "was expected"]
    
resolveFormula _ _ _ fml = return fml
