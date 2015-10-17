module Synquid.Parser where

import Synquid.Logic
import Synquid.Program
import qualified Control.Applicative as Applicative
import Control.Applicative ((<$), (*>), (<*))
import qualified Text.Parsec as Parsec
import qualified Text.Parsec.Token as Token
import qualified Text.Parsec.Expr as Expr
import Text.Parsec ((<|>), (<?>))

type Parser = Parsec.Parsec String ()

applyParser parser = Parsec.parse parser ""

parse :: String -> TypeSkeleton Formula
parse str = case Parsec.parse parseType "" str of
  Right parsed -> parsed
  Left err -> error "foobar!"

parseType :: Parser (TypeSkeleton Formula)
parseType = Parsec.choice [parseScalarType, parseFunctionType]

parseFunctionType :: Parser (TypeSkeleton Formula)
parseFunctionType = do
  Parsec.char '('
  Parsec.spaces
  argId <- parseIdentifier
  Parsec.spaces
  Parsec.char ':'
  Parsec.spaces
  argType <- parseType
  Parsec.spaces
  Parsec.string "->"
  Parsec.spaces
  returnType <- parseType
  Parsec.spaces
  Parsec.char ')'
  return $ FunctionT argId argType returnType

parseScalarType :: Parser (TypeSkeleton Formula)
parseScalarType = Parsec.choice [parseScalarRefType, parseScalarUnrefType]
  where
    parseScalarUnrefType = do
      baseType <- parseBaseType
      Parsec.spaces
      typeVarRefinements <- Parsec.many $
        Parsec.between (Parsec.char '(') (Parsec.char ')') parseType <* Parsec.spaces
      return $ ScalarT baseType typeVarRefinements ftrue

    parseScalarRefType = do
      Parsec.char '{'
      Parsec.spaces
      ScalarT baseType typeVarRefinements _ <- parseScalarUnrefType
      Parsec.char '|'
      Parsec.spaces
      refinement <- parseFormula
      Parsec.spaces
      Parsec.char '}'
      return $ ScalarT baseType typeVarRefinements refinement

parseBaseType :: Parser BaseType
parseBaseType = Parsec.choice [
    BoolT <$ Parsec.string "Bool",
    IntT <$ Parsec.string "Int",
    fmap DatatypeT parseCustomType,
    fmap TypeVarT parseIdentifier]
  where
    parseCustomType = Applicative.liftA2 (:) Parsec.upper $ Parsec.many (Parsec.alphaNum <|> Parsec.char '_')

parseFormula :: Parser Formula
parseFormula = Expr.buildExpressionParser exprTable (parseTerm <* Parsec.spaces)
  where
    exprTable = [
      [unary '!' Not, unary '-' Neg],
      [bin "*" (|*|)],
      [bin "+" (|+|), bin "-" (|-|), bin "/+" (/+/), bin "/*" (/*/), bin "/-" (/-/)],
      [bin "=" (|=|), bin "/=" (|/=|), bin "<=" (|<=|), bin "<" (|<|), bin ">=" (|>=|), bin ">" (|>|),
        bin "/<=" (/<=/)],
      [bin "&" (|&|), bin "|" (|||)],
      [bin "=>" (|=>|), bin "<=>" (|<=>|)]]
    unary opChar opType = Expr.Prefix (Parsec.char opChar <* Parsec.spaces >> (return $ Unary opType))
    bin opStr func = Expr.Infix parseOpStr Expr.AssocLeft
      where
        parseOpStr = Parsec.try $ do
          Parsec.string opStr
          Parsec.notFollowedBy $ Parsec.oneOf ">=" -- This is a dirty hack.
          Parsec.spaces
          return func

parseTerm :: Parser Formula
parseTerm = Parsec.choice [Parsec.between (Parsec.char '(') (Parsec.char ')') parseFormula, parseBoolLit, parseIntLit, parseVar, parseSetLit]

parseBoolLit :: Parser Formula
parseBoolLit = Parsec.try $ fmap BoolLit $ False <$ Parsec.string "False" <|> True <$ Parsec.string "True"

parseIntLit :: Parser Formula
parseIntLit = fmap (IntLit . read) $ Parsec.many1 Parsec.digit

parseSetLit :: Parser Formula
parseSetLit = do
  Parsec.char '{'
  Parsec.spaces
  elements <- Parsec.sepBy parseFormula $ Parsec.spaces *> Parsec.char ',' *> Parsec.spaces
  Parsec.spaces
  Parsec.char '}'
  return $ SetLit UnknownT elements

parseVar :: Parser Formula
parseVar = fmap (Var UnknownT) parseIdentifier

parseUnaryOp :: Parser Formula
parseUnaryOp = do
  op <- Neg <$ Parsec.char '-' <|> Not <$ Parsec.char '!'
  refinement <- parseFormula
  return $ Unary op refinement

parseIdentifier :: Parser Id
parseIdentifier = Applicative.liftA2 (:) firstChar otherChars
  where
    firstChar = Parsec.char '_' <|> Parsec.lower
    otherChars = Parsec.many (Parsec.alphaNum <|> Parsec.char '_')
