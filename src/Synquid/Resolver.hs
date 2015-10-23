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

type ResolverError = Either String

resolveTypeSkeleton :: Environment -> TypeSkeleton Formula -> ResolverError (TypeSkeleton Formula)
resolveTypeSkeleton env (ScalarT baseType typeParamRefs typeFml) = do
  typeFml' <- resolveFormula env typeFml
  case sortOf typeFml' of
    Just BoolS -> do
      typeParamRefs' <- mapM (resolveTypeSkeleton env) typeParamRefs
      return $ ScalarT baseType typeParamRefs' typeFml
    Just _ -> throwError "Refinement formula doesn't evaluate to a boolean"
    Nothing -> throwError "Failed to determine type of formula"
resolveTypeSkeleton env (FunctionT argId argRef returnRef) = do
  argRef' <- resolveTypeSkeleton env argRef
  let env' = addVariable argId argRef' env
  returnRef' <- resolveTypeSkeleton env' returnRef
  return $ FunctionT argId argRef' returnRef'

resolveFormula :: Environment -> Formula -> ResolverError Formula
resolveFormula env (SetLit UnknownS memberFmls) = do
  resolvedMembers <- mapM (resolveFormula env) memberFmls
  case mapM sortOf resolvedMembers of
    Just [] -> throwError "Can't have empty set?"
    Just (expectedSort:otherSorts) -> if all (== expectedSort) otherSorts
      then return $ SetLit expectedSort resolvedMembers
      else throwError "Set members don't all have the same type."
    Nothing -> throwError "Couldn't determine the type of a member (TODO: add specific details about which member/what error occurred?)"
resolveFormula env (Var UnknownS varName) =
  case env ^. symbols ^. at 0 >>= view (at varName) of
    Just varType ->
      case toMonotype varType of
        ScalarT baseType _ _ -> return $ Var (toSort baseType) varName
        FunctionT _ _ _ -> error "Variable of function type? What do?"
    Nothing -> throwError $ printf "Var `%s` is not in scope." varName
resolveFormula env (Unary op fml) = fmap (Unary op) $ resolveFormula env fml
resolveFormula env (Binary op fml1 fml2) = liftA2 (Binary op) (resolveFormula env fml1) (resolveFormula env fml2)
resolveFormula _ fml = return fml
