{-
 - Functions for processing the AST created by the Parser (eg filling in unknown types, verifying that refinement
 - formulas evaluate to a boolean, etc.)
 -}

{-# LANGUAGE TupleSections #-}

module Synquid.Resolver where

import Synquid.Program
import Synquid.Explorer
import Synquid.Logic
import Synquid.Pretty
import Control.Applicative
import Control.Monad.Except
import Text.Printf
import Control.Lens
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
  return $ Goal goalName env goalType undefined
  where
    isSynthesisGoal (SynthesisGoal _) = True
    isSynthesisGoal _ = False

substituteTypeSynonym :: TypeSubstitution -> RType -> RType
substituteTypeSynonym synonyms rtype@(ScalarT (DatatypeT typeName) typeArgs refinement) =
  case synonyms ^. at typeName of
    Just typeSubstitute -> typeSubstitute -- what if `refinement` isn't just BoolLit True?
    Nothing -> rtype
substituteTypeSynonym synonyms (FunctionT argId argRef returnRef) = FunctionT argId (substituteTypeSynonym synonyms argRef) (substituteTypeSynonym synonyms returnRef)
substituteTypeSynonym synonyms rtype = rtype

resolveDeclaration :: Environment -> Declaration -> ResolverError Environment
resolveDeclaration env (TypeDef typeName typeBody) = do
  typeBody' <- resolveTypeSkeleton env typeBody
  return $ addTypeSynonym typeName typeBody' env
resolveDeclaration env (FuncDef funcName typeSchema) = do
  typeSchema' <- resolveSchemaSkeleton env typeSchema
  return $ addPolyConstant funcName typeSchema' env
resolveDeclaration env (DataDef dataName typeParams metricName constructors) = do
  let
    datatype = Datatype {
      _typeArgCount = length typeParams,
      _constructors = map constructorName constructors,
      _wfMetric = Nothing
    }
  constructors' <- mapM (\ (ConstructorDef name schema) -> fmap (name,) $ resolveSchemaSkeleton env schema) constructors
  return $ foldl (\ env (id', schema) -> addPolyVariable id' schema env) (addDatatype dataName datatype env) constructors'
resolveDeclaration env (MeasureDef measureName inSort outSort) = return $ addMeasure measureName (inSort, outSort) env
resolveDeclaration env (SynthesisGoal _) = return env

resolveSchemaSkeleton :: Environment -> RSchema -> ResolverError RSchema
resolveSchemaSkeleton env (Monotype typeSkel) = do
  typeSkel' <- resolveTypeSkeleton env typeSkel
  return $ Foldable.foldl (flip Forall) (Monotype typeSkel') $ typeVarsOf typeSkel'
resolveSchemaSkeleton env (Forall id' schemaSkel) = fmap (Forall id') $ resolveSchemaSkeleton env schemaSkel

resolveTypeSkeleton :: Environment -> RType -> ResolverError RType
resolveTypeSkeleton env (ScalarT baseType typeParamRefs typeFml) = do
  typeFml' <- resolveFormula (toSort baseType) env typeFml
  case sortOf typeFml' of
    Just BoolS -> do
      typeParamRefs' <- mapM (resolveTypeSkeleton env) typeParamRefs
      return $ substituteTypeSynonym (env ^. typeSynonyms) $ ScalarT baseType typeParamRefs' typeFml'
    Just _ -> throwError "Refinement formula doesn't evaluate to a boolean"
    Nothing -> throwError "Failed to determine type of formula"
resolveTypeSkeleton env (FunctionT argId argRef returnRef) = do
  when (argId == valueVarName) $ throwError $
    valueVarName ++ " is a reserved variable name, so you can't bind function arguments to it"
  argRef' <- resolveTypeSkeleton env argRef
  when (isFunctionType argRef') $ throwError $
    "The argument to a function can't be another function"
  let env' = addVariable argId argRef' env
  returnRef' <- resolveTypeSkeleton env' returnRef
  return $ FunctionT argId argRef' returnRef'

resolveFormula :: Sort -> Environment -> Formula -> ResolverError Formula
resolveFormula valueType env (SetLit UnknownS memberFmls) = do
  resolvedMembers <- mapM (resolveFormula valueType env) memberFmls
  case mapM sortOf resolvedMembers of
    Just [] -> throwError "Can't have empty set?"
    Just (expectedSort:otherSorts) -> if all (== expectedSort) otherSorts
      then return $ SetLit expectedSort resolvedMembers
      else throwError "Set members don't all have the same type."
    Nothing -> throwError "Couldn't determine the type of a member (TODO: add specific details about which member/what error occurred?)"
resolveFormula valueType env (Var UnknownS varName) =
  if varName == valueVarName
    then return $ Var valueType varName
    else case env ^. symbols ^. at 0 >>= view (at varName) of
      Just varType ->
        case toMonotype varType of
          ScalarT baseType _ _ -> return $ Var (toSort baseType) varName
          FunctionT _ _ _ -> error "Variable of function type? What do?"
      Nothing -> throwError $ printf "Var `%s` is not in scope." varName
resolveFormula valueType env (Unary op fml) = fmap (Unary op) $ resolveFormula valueType env fml
resolveFormula valueType env (Binary op fml1 fml2) = liftA2 (Binary op)
  (resolveFormula valueType env fml1) (resolveFormula valueType env fml2)
resolveFormula valueType env (Measure UnknownS name argFml) = do
  argFml' <- resolveFormula valueType env argFml
  case env ^. measures ^. at name of
    Just (inSort, outSort) ->
      case sortOf argFml' of
        Just argSort ->
          if argSort /= inSort
            then throwError "Measure applied to argument of wrong sort"
            else return $ Measure outSort name argFml'
        Nothing -> throwError $ "Couldn't resolve sort of " ++ show argFml'
    Nothing -> throwError $ name ++ " is undefined"
resolveFormula _ _ fml = return fml
