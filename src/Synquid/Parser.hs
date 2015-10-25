{-
 - The parser for Synquid's program specification DSL.
 -}

module Synquid.Parser where

import Synquid.Logic
import Synquid.Program

import qualified Control.Applicative as Applicative
import Control.Applicative ((<$), (*>), (<*))
import Control.Monad.Except
import Control.Monad.Identity

import qualified Text.Parsec as Parsec
import qualified Text.Parsec.Token as Token
import qualified Text.Parsec.Expr as Expr
import qualified Text.Parsec.Char as Char
import Text.Parsec ((<|>), (<?>))

import Text.Printf

type Parser = Parsec.Parsec String ()
-- Rschema or skeleton?
type ProgramAst = [Declaration]
data ConstructorDef = ConstructorDef Id RSchema-- deriving Show
data Declaration =
  TypeDef Id RType | -- | Type name and definition.
  FuncDef Id RSchema | -- | Function name and signature.
  DataDef Id [Id] [ConstructorDef] | -- | Datatype name, type parameters, and constructor definitions.
  MeasureDef Id Sort Sort | -- | Measure name, input sort, output sort.
  SynthesisGoal Id -- Name of the function to synthesize.

-- Quick and dirty Show instances to aid in debugging.
instance Show Declaration where
  show (TypeDef id' type') = printf "type %s = %s" id' $ show type'
  show (FuncDef id' schema) = printf "func %s = %s" id' $ show schema
  show (DataDef id' typeParams ctors) = printf "data %s %s\n%s" id' (show typeParams) $ unlines $ map ((++) "  " . show) ctors
  show (MeasureDef id' inSort outSort) = printf "msre %s = %s -> %s" id' (show inSort) $ show outSort
  show (SynthesisGoal id') = printf "goal %s = ??" id'

instance Show ConstructorDef where
  show (ConstructorDef id' schema) = printf "ctor %s = %s" id' $ show schema

parse parser str = case Parsec.parse parser "" str of
  Left err -> Left $ show err
  Right parsed -> Right parsed

parseProgram :: Parser ProgramAst
parseProgram = parseCommentOrWs *> Parsec.sepEndBy1 parseDeclaration parseCommentOrWs <* Parsec.eof
  where
    parseCommentOrWs = Parsec.many $ (Parsec.space >> Parsec.spaces) <|> parseComment
    parseComment = do
      Parsec.string "--"
      Parsec.manyTill Parsec.anyChar Parsec.endOfLine
      return ()

parseDeclaration :: Parser Declaration
parseDeclaration = Parsec.choice [parseTypeDef, parseDataDef, parseMeasureDef, Parsec.try parseSynthesisGoal, parseFuncDef] <?> "declaration"

parseTypeDef :: Parser Declaration
parseTypeDef = do
  Parsec.try $ Parsec.string "type"
  Parsec.spaces
  typeName <- parseTypeName
  Parsec.spaces
  Parsec.char '='
  Parsec.spaces
  typeDef <- parseType
  return $ TypeDef typeName typeDef
  <?> "type definition"

parseDataDef :: Parser Declaration
parseDataDef = do
  Parsec.try $ Parsec.string "data"
  Parsec.spaces
  typeName <- parseTypeName
  Parsec.spaces
  typeParams <- Parsec.manyTill (parseIdentifier <* Parsec.spaces) $ Parsec.string "where"
  Parsec.spaces
  constructors <- (Parsec.many1 $ parseConstructorDef <* Parsec.spaces)
  return $ DataDef typeName typeParams constructors
  <?> "data definition"

parseConstructorDef :: Parser ConstructorDef
parseConstructorDef = do
  ctorName <- parseTypeName
  Parsec.spaces
  Parsec.string "::"
  Parsec.spaces
  ctorType <- parseSchemaSkeleton
  return $ ConstructorDef ctorName ctorType
  <?> "constructor definition"

parseMeasureDef :: Parser Declaration
parseMeasureDef = do
  Parsec.try $ Parsec.string "measure"
  Parsec.spaces
  measureName <- parseIdentifier
  Parsec.spaces
  Parsec.string "::"
  Parsec.spaces
  inSort <- parseSort
  Parsec.spaces
  Parsec.string "->"
  Parsec.spaces
  outSort <- parseSort
  return $ MeasureDef measureName inSort outSort
  <?> "measure definition"

parseFuncDef :: Parser Declaration
parseFuncDef = do
  funcName <- parseIdentifier
  Parsec.spaces
  Parsec.string "::"
  Parsec.spaces
  fmap (FuncDef funcName) parseSchemaSkeleton
  <?> "function definition"

parseSynthesisGoal :: Parser Declaration
parseSynthesisGoal = do
  goalId <- parseIdentifier
  Parsec.spaces
  Parsec.char '='
  Parsec.spaces
  Parsec.string "??"
  return $ SynthesisGoal goalId

parseSchemaSkeleton :: Parser RSchema
parseSchemaSkeleton = do
  Parsec.char '<'
  typeVarId <- parseIdentifier
  Parsec.char '>'
  fmap (Forall typeVarId) parseSchemaSkeleton
  <|> fmap Monotype parseType
  <?> "type schema"

parseType :: Parser (TypeSkeleton Formula)
parseType = Parsec.between (Parsec.char '(') (Parsec.char ')') parseType' <|> parseType'
  where parseType' = Parsec.choice [Parsec.try parseFunctionType, parseScalarType] <?> "type definition"

parseFunctionType :: Parser (TypeSkeleton Formula)
parseFunctionType = do
  {- Parsec.char '(' -}
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
  {- Parsec.char ')' -}
  return $ FunctionT argId argType returnType
  <?> "function type"

parseScalarType :: Parser (TypeSkeleton Formula)
parseScalarType = Parsec.choice [parseScalarRefType, parseScalarUnrefType] <?> "scalar type"
  where
    parseScalarUnrefType = do
      baseType <- parseBaseType
      Parsec.spaces
      typeVarRefinements <- Parsec.many $ parseType <* Parsec.spaces
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
  fmap DatatypeT parseTypeName,
  fmap TypeVarT parseIdentifier]

parseSort :: Parser Sort
parseSort = Parsec.choice [
  BoolS <$ Parsec.string "Bool",
  IntS <$ Parsec.string "Int",
  fmap SetS $ Parsec.string "Set" >> Parsec.spaces >> parseSort,
  parseCustomSort]
  where
    parseCustomSort = do
      typeName <- parseTypeName
      Parsec.spaces
      typeParams <- Parsec.many $ parseIdentifier <* Parsec.spaces
      return $ UninterpretedS typeName -- Discard `typeParams` because `Sort` doesn't currently support type params.

{-
 - | @Formula@ parsing is broken up into two functions: @parseFormula@ and @parseTerm@. @parseFormula's@ responsible
 - for parsing binary and unary expressions that consist of other @Formula@s, while @parseTerm@ parses everything else
 - (ie literals).
 -}
parseFormula :: Parser Formula
parseFormula = Expr.buildExpressionParser exprTable (parseTerm <* Parsec.spaces) <?> "refinement formula"
  where
    exprTable = [
      [unary '!' Not, unary '-' Neg],
      [bin "*" (|*|)],
      [bin "+" (|+|), bin "-" (|-|), bin "/+" (/+/), bin "/*" (/*/), bin "/-" (/-/)],
      [bin "==" (|=|), bin "/=" (|/=|), bin "<=" (|<=|), bin "<" (|<|), bin ">=" (|>=|), bin ">" (|>|),
        bin "/<=" (/<=/)],
      [bin "&&" (|&|), bin "||" (|||)],
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
parseTerm = Parsec.choice [
  Parsec.between (Parsec.char '(') (Parsec.char ')') parseFormula,
  parseBoolLit, parseIntLit, Parsec.try $ parseMeasure, parseVar, parseSetLit]

parseBoolLit :: Parser Formula
parseBoolLit = (fmap BoolLit $ False <$ Parsec.string "False" <|> True <$ Parsec.string "True") <?> "boolean"

parseIntLit :: Parser Formula
parseIntLit = (fmap (IntLit . read) $ Parsec.many1 Parsec.digit) <?> "number"

parseSetLit :: Parser Formula
parseSetLit = do
  Parsec.char '['
  Parsec.spaces
  elements <- Parsec.sepBy parseFormula $ Parsec.spaces *> Parsec.char ',' *> Parsec.spaces
  Parsec.spaces
  Parsec.char ']'
  return $ SetLit UnknownS elements
  <?> "set"

parseVar :: Parser Formula
parseVar = fmap (Var UnknownS) parseIdentifier <?> "variable"

parseMeasure :: Parser Formula
parseMeasure = do
  measureName <- parseIdentifier
  Parsec.spaces
  arg <- parseFormula
  return $ Measure UnknownS measureName arg
  <?> "measure"

parseIdentifier :: Parser Id
parseIdentifier = Applicative.liftA2 (:) firstChar otherChars <?> "identifier"
  where
    firstChar = Parsec.char '_' <|> Parsec.lower
    otherChars = Parsec.many (Parsec.alphaNum <|> Parsec.char '_')

parseTypeName :: Parser Id
parseTypeName = (Applicative.liftA2 (:) Parsec.upper $ Parsec.many (Parsec.alphaNum <|> Parsec.char '_')) <?> "type name"
