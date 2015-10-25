{-
 - Functions for processing the AST created by the Parser (eg filling in unknown types, verifying that refinement
 - formulas evaluate to a boolean, etc.)
 -}

{-# OPTIONS_GHC -Wall #-}

module Synquid.Resolver where

import Synquid.Program
import Synquid.Logic
import Control.Applicative
import Control.Monad.Except
import Text.Printf
import Control.Lens
import Control.Monad

type ResolverError = Either String

resolveTypeSkeleton :: Environment -> TypeSkeleton Formula -> ResolverError (TypeSkeleton Formula)
resolveTypeSkeleton env (ScalarT baseType typeParamRefs typeFml) = do
  typeFml' <- resolveFormula (toSort baseType) env typeFml
  case sortOf typeFml' of
    Just BoolS -> do
      typeParamRefs' <- mapM (resolveTypeSkeleton env) typeParamRefs
      return $ ScalarT baseType typeParamRefs' typeFml'
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
