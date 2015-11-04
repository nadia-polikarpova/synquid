-- | The parser for Synquid's program specification DSL.
module Synquid.Parser where

import Synquid.Logic
import Synquid.Program

import Data.Char
import Data.List
import Data.Map (Map, (!), elems, fromList)

import qualified Control.Applicative as Applicative
import Control.Applicative ((<$), (*>), (<*))
import Control.Monad.Except
import Control.Monad.Identity

import Text.Parsec
import qualified Text.Parsec.Token as Token
import Text.Parsec.Expr
import qualified Text.Parsec.Char as Char
import Text.Parsec ((<|>), (<?>))

import Text.Printf

{- Interface -}

type Parser = Parsec String ()

parseProgram :: Parser ProgramAst
parseProgram = whiteSpace *> many parseDeclaration <* eof
      
{- Tokens -}

-- | Keywords
keywords :: [String]
keywords = ["Bool", "data", "decreases", "else", "False", "if", "in", "Int", "match", "measure", "then", "True", "type", "where", "with"]

-- | Names of unary operators    
unOpTokens :: Map UnOp String
unOpTokens = fromList [(Neg, "-")
                      ,(Not, "!")
                      ,(Abs, "~")]
                           
-- | Names of binary operators             
binOpTokens :: Map BinOp String
binOpTokens = fromList [(Times,     "*")
                       ,(Plus,      "+")
                       ,(Minus,     "-")
                       ,(Eq,        "==")
                       ,(Neq,       "!=")
                       ,(Lt,        "<")
                       ,(Le,        "<=")
                       ,(Gt,        ">")
                       ,(Ge,        ">=")                       
                       ,(And,       "&&")
                       ,(Or,        "||")
                       ,(Implies,   "==>")
                       ,(Iff,       "<==>")
                       ,(Union,     "/+/")                       
                       ,(Intersect, "/*/")
                       ,(Diff,      "/-/")
                       ,(Member,    "in")
                       ,(Subset,    "/<=/")
                      ]
                        
-- | Other operators         
otherOps :: [String]
otherOps = ["::", ":", "->", "|", "=", "??"] 

-- | Characters allowed in identifiers (in addition to letters and digits)
identifierChars = "_"
-- | Start of a multi-line comment
commentStart = "{-"
-- | End of a multi-line comment
commentEnd = "-}"
-- | Start of a single-line comment
commentLine = "--"


{- Lexical analysis -}

opNames :: [String]
opNames = elems unOpTokens ++ (elems binOpTokens \\ keywords) ++ otherOps

opStart :: [Char]
opStart = nub (map head opNames)

opLetter :: [Char]
opLetter = nub (concatMap tail opNames)

synquidDef :: Token.LanguageDef st
synquidDef = Token.LanguageDef 
  commentStart
  commentEnd
  commentLine
  False
  (letter <|> oneOf identifierChars)
  (alphaNum <|> oneOf identifierChars)
  (oneOf opStart)
  (oneOf opLetter)
  keywords
  opNames
  True
  
lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser synquidDef    
      
identifier = Token.identifier lexer
reserved = Token.reserved lexer
reservedOp = Token.reservedOp lexer
natural = Token.natural lexer
whiteSpace = Token.whiteSpace lexer
angles = Token.angles lexer
brackets = Token.brackets lexer
parens = Token.parens lexer
braces = Token.braces lexer
comma = Token.comma lexer
commaSep = Token.commaSep lexer
commaSep1 = Token.commaSep1 lexer

      
{- Parsing -}      

parseDeclaration :: Parser Declaration
parseDeclaration = choice [parseTypeDef, parseDataDef, parseMeasureDef, try parseSynthesisGoal, parseFuncDef] <?> "declaration"

parseTypeDef :: Parser Declaration
parseTypeDef = do
  reserved "type"
  typeName <- parseTypeName
  reservedOp "="
  typeDef <- parseType
  return $ TypeDef typeName typeDef
  <?> "type definition"

parseDataDef :: Parser Declaration
parseDataDef = do
  reserved "data"
  typeName <- parseTypeName
  typeParams <- many parseIdentifier
  wfMetricName <- optionMaybe $ reserved "decreases" >> parseIdentifier
  reserved "where"
  constructors <- many1 parseConstructorDef
  return $ DataDef typeName typeParams wfMetricName constructors
  <?> "data definition"

parseConstructorDef :: Parser ConstructorDef
parseConstructorDef = do
  ctorName <- parseTypeName
  reservedOp "::"
  ctorType <- Monotype <$> parseType
  return $ ConstructorDef ctorName ctorType
  <?> "constructor definition"

parseMeasureDef :: Parser Declaration
parseMeasureDef = do
  reserved "measure"
  measureName <- parseIdentifier
  reservedOp "::"
  inSort <- parseSort
  reservedOp "->"
  outSort <- parseSort
  return $ MeasureDef measureName inSort outSort
  <?> "measure definition"

parseFuncDef :: Parser Declaration
parseFuncDef = do
  funcName <- parseIdentifier
  reservedOp "::"
  FuncDef funcName . Monotype <$> parseType
  <?> "function definition"

parseSynthesisGoal :: Parser Declaration
parseSynthesisGoal = do
  goalId <- parseIdentifier
  reservedOp "="
  reservedOp "??"
  return $ SynthesisGoal goalId

parseType :: Parser RType
parseType = choice [try parseFunctionType, parseUnrefTypeWithArgs, parseTypeAtom] <?> "type definition"

parseTypeAtom :: Parser RType
parseTypeAtom = choice [
  parens parseType,
  parseScalarRefType,
  parseUnrefTypeNoArgs
  ]
  
parseUnrefTypeNoArgs = do
  baseType <- parseBaseType
  return $ ScalarT baseType [] ftrue  
  where
    parseBaseType = choice [
      BoolT <$ reserved "Bool",
      IntT <$ reserved "Int",
      DatatypeT <$> parseTypeName,
      TypeVarT <$> parseIdentifier]
  
parseUnrefTypeWithArgs = do
  baseType <- DatatypeT <$> parseTypeName
  typeArgs <- many parseTypeAtom
  return $ ScalarT baseType typeArgs ftrue    
  
parseScalarUnrefType = parseUnrefTypeWithArgs <|> parseUnrefTypeNoArgs
  
parseScalarRefType = braces $ do
  ScalarT baseType typeArgs _ <- parseScalarUnrefType
  reservedOp "|"
  refinement <- parseFormula
  return $ ScalarT baseType typeArgs refinement  

parseFunctionType :: Parser RType
parseFunctionType = do
  argId <- option "_" parseArgName
  argType <- parseUnrefTypeWithArgs <|> parseTypeAtom
  reservedOp "->"
  returnType <- parseType
  return $ FunctionT argId argType returnType
  <?> "function type"
  where
    parseArgName = parseIdentifier <* reservedOp ":"

parseSort :: Parser Sort
parseSort = choice [
  BoolS <$ reserved "Bool",
  IntS <$ reserved "Int",
  fmap SetS $ reserved "Set" >> parseSort,
  parseCustomSort]
  where
    parseCustomSort = do
      typeName <- parseTypeName <|> parseIdentifier
      typeParams <- many parseSort
      return $ UninterpretedS typeName -- Discard `typeParams` because `Sort` doesn't currently support type params.

{-
 - | @Formula@ parsing is broken up into two functions: @parseFormula@ and @parseTerm@. @parseFormula's@ responsible
 - for parsing binary and unary expressions that consist of other @Formula@s, while @parseTerm@ parses everything else
 - (ie literals).
 -}
parseFormula :: Parser Formula
parseFormula = buildExpressionParser exprTable parseTerm <?> "refinement formula"
  where
    exprTable = [
      [unary Not, unary Neg, unary Abs],
      [binary Times AssocLeft],
      [binary Plus AssocLeft, binary Minus AssocLeft, binary Union AssocLeft, binary Intersect AssocLeft, binary Diff AssocLeft],
      [binary Eq AssocNone, binary Neq AssocNone, binary Le AssocNone, binary Lt AssocNone, binary Ge AssocNone, binary Gt AssocNone, binary Member AssocNone, binary Subset AssocNone],
      [binary And AssocLeft, binary Or AssocLeft],
      [binary Implies AssocRight, binary Iff AssocRight]]
    unary op = Prefix (reservedOp (unOpTokens ! op) >> return (Unary op))
    binary op assoc = Infix (reservedOp (binOpTokens ! op) >> return (Binary op)) assoc

parseTerm :: Parser Formula
parseTerm = choice [
    parens parseFormula
  , parseBoolLit
  , parseIntLit
  , parseSetLit
  , varOrApp ]
  where
    parseBoolLit = (reserved "False" >> return ffalse) <|> (reserved "True" >> return ftrue) <?> "boolean"
    parseIntLit = IntLit <$> natural
    parseSetLit = SetLit UnknownS <$> brackets (commaSep parseFormula)
    varOrApp = do
      name <- identifier
      option (Var UnknownS name) (parseTerm >>= return . Measure UnknownS name)

parseIdentifier :: Parser Id
parseIdentifier = try $ do
  name <- identifier
  if isUpper $ head name then unexpected ("capitalized " ++ show name) else return name

parseTypeName :: Parser Id
parseTypeName = try $ do
  name <- identifier
  if isLower $ head name then unexpected ("non-capitalized " ++ show name) else return name
