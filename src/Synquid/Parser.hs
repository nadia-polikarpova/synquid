{- 
 - The parser for Synquid's program specification DSL.
 -}

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

{-
 - | @Formula@ parsing is broken up into two functions: @parseFormula@ and @parseTerm@. @parseFormula's@ responsible
 - for parsing binary and unary expressions that consist of other @Formula@s, while @parseTerm@ parses everything else
 - (ie literals).
 -}
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

          -- | The parser runs into a problem with operators that have the same leading characters but different
          -- precedences, like @<=@ and @<=>@ (the former having higher precedence than the latter). Parsec will try to
          -- parse the higher-precedence operator first and thus will /never/ match @<=>@, since it'll consume @<=@ and
          -- leave @>@ in the string. If the actual operator was @<=>@, Parsec will then try to parse the leftover @>@
          -- as a term (the second argument to the @<=@ operator) and obviously error. If the parser used a token-based
          -- approach this would be easy to avoid, but since it operates directly on the string we'll use the
          -- quick-and-dirty fix of just making sure than no operator-like characters follow the parsed operator.
          Parsec.notFollowedBy $ Parsec.oneOf ">="
          Parsec.spaces
          return func

parseTerm :: Parser Formula
parseTerm = Parsec.choice [Parsec.between (Parsec.char '(') (Parsec.char ')') parseFormula, parseBoolLit, parseIntLit, Parsec.try $ parseMeasure, parseVar, parseSetLit]

parseBoolLit :: Parser Formula
parseBoolLit = fmap BoolLit $ False <$ Parsec.string "False" <|> True <$ Parsec.string "True"

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

parseMeasure :: Parser Formula
parseMeasure = do
  measureName <- parseIdentifier
  Parsec.spaces
  arg <- parseFormula
  return $ Measure UnknownT measureName arg

parseIdentifier :: Parser Id
parseIdentifier = Applicative.liftA2 (:) firstChar otherChars
  where
    firstChar = Parsec.char '_' <|> Parsec.lower
    otherChars = Parsec.many (Parsec.alphaNum <|> Parsec.char '_')
