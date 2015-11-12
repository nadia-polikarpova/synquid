{-# LANGUAGE TupleSections #-}

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

testParse :: Parser a -> String -> Either String a
testParse parser str = case parse parser "" str of
  Left err -> Left $ show err
  Right parsed -> Right parsed
      
{- Tokens -}

-- | Keywords
keywords :: [String]
keywords = ["Bool", "data", "decreases", "False", "in", "Int", "match", "measure", "qualifier", "Set", "True", "type", "where"]

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
                       ,(Member,    "in")
                      ]
                        
-- | Other operators         
otherOps :: [String]
otherOps = ["::", ":", "->", "|", "=", "??", ","] 

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

      
{- Declarations -}      

parseDeclaration :: Parser Declaration
parseDeclaration = choice [parseTypeDef, parseDataDef, parseMeasureDef, parseQualifierDef, try parseSynthesisGoal, parseFuncDef] <?> "declaration"

parseTypeDef :: Parser Declaration
parseTypeDef = do
  reserved "type"
  typeName <- parseTypeName
  reservedOp "="
  typeDef <- parseType
  return $ TypeDecl typeName typeDef

parseDataDef :: Parser Declaration
parseDataDef = do
  reserved "data"
  typeName <- parseTypeName
  typeParams <- many parseIdentifier
  wfMetricName <- optionMaybe $ reserved "decreases" >> parseIdentifier
  reserved "where"
  constructors <- many1 parseConstructorDef
  return $ DataDecl typeName typeParams wfMetricName constructors

parseConstructorDef :: Parser ConstructorDef
parseConstructorDef = do
  ctorName <- parseTypeName
  reservedOp "::"
  ctorType <- Monotype <$> parseType
  return $ ConstructorDef ctorName ctorType

parseMeasureDef :: Parser Declaration
parseMeasureDef = do
  reserved "measure"
  measureName <- parseIdentifier
  reservedOp "::"
  inSort <- parseSort
  reservedOp "->"
  (outSort, post) <- parseRefinedSort <|> ((, ftrue) <$> parseSort)
  return $ MeasureDecl measureName inSort outSort post
  
parseQualifierDef :: Parser Declaration
parseQualifierDef = do
  reserved "qualifier"
  QualifierDecl <$> braces (commaSep parseFormula)

parseFuncDef :: Parser Declaration
parseFuncDef = do
  funcName <- parseIdentifier
  reservedOp "::"
  FuncDecl funcName . Monotype <$> parseType

parseSynthesisGoal :: Parser Declaration
parseSynthesisGoal = do
  goalId <- parseIdentifier
  reservedOp "="
  reservedOp "??"
  return $ SynthesisGoal goalId
  
{- Types -}  

parseType :: Parser RType
parseType = choice [try parseFunctionType, parseUnrefTypeWithArgs, parseTypeAtom] <?> "type"

parseTypeAtom :: Parser RType
parseTypeAtom = choice [
  parens parseType,
  parseScalarRefType,
  parseUnrefTypeNoArgs
  ]
  
parseUnrefTypeNoArgs = do
  baseType <- parseBaseType
  return $ ScalarT baseType ftrue  
  where
    parseBaseType = choice [
      BoolT <$ reserved "Bool",
      IntT <$ reserved "Int",
      flip DatatypeT [] <$> parseTypeName,
      TypeVarT <$> parseIdentifier]
  
parseUnrefTypeWithArgs = do
  name <- parseTypeName
  typeArgs <- many parseTypeAtom
  return $ ScalarT (DatatypeT name typeArgs) ftrue    
  
parseScalarUnrefType = parseUnrefTypeWithArgs <|> parseUnrefTypeNoArgs
  
parseScalarRefType = braces $ do
  ScalarT baseType _ <- parseScalarUnrefType
  reservedOp "|"
  refinement <- parseFormula
  return $ ScalarT baseType refinement  

parseFunctionType :: Parser RType
parseFunctionType = do
  argId <- option dontCare (try parseArgName)
  argType <- parseUnrefTypeWithArgs <|> parseTypeAtom
  reservedOp "->"
  returnType <- parseType
  return $ FunctionT argId argType returnType
  where
    parseArgName = parseIdentifier <* reservedOp ":"

parseSort :: Parser Sort
parseSort = parseSortWithArgs <|> parseSortAtom 
  where
    parseSortAtom = choice [
      parens parseSort,
      BoolS <$ reserved "Bool",
      IntS <$ reserved "Int",
      VarS <$> parseIdentifier,
      flip DataS [] <$> parseTypeName
      ]
      
    parseSortWithArgs = choice [
      SetS <$> (reserved "Set" >> parseSortAtom),
      do
        typeName <- parseTypeName
        typeParams <- many parseSortAtom
        return $ DataS typeName typeParams
      ]
      
parseRefinedSort :: Parser (Sort, Formula)
parseRefinedSort = braces $ do
  s <- parseSort
  reservedOp "|"
  refinement <- parseFormula
  return (s, refinement)
      
{- Formulas -}     

{-
 - | @Formula@ parsing is broken up into two functions: @parseFormula@ and @parseTerm@. @parseFormula's@ responsible
 - for parsing binary and unary expressions that consist of other @Formula@s, while @parseTerm@ parses everything else
 - (ie literals).
 -}
parseFormula :: Parser Formula
parseFormula = buildExpressionParser exprTable parseTerm <?> "refinement term"
  where
    exprTable = [
      [unary Not, unary Neg, unary Abs],
      [binary Times AssocLeft],
      [binary Plus AssocLeft, binary Minus AssocLeft],
      [binary Eq AssocNone, binary Neq AssocNone, binary Le AssocNone, binary Lt AssocNone, binary Ge AssocNone, binary Gt AssocNone, binary Member AssocNone],
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
    parseBoolLit = (reserved "False" >> return ffalse) <|> (reserved "True" >> return ftrue)
    parseIntLit = IntLit <$> natural
    parseSetLit = SetLit UnknownS <$> brackets (commaSep parseFormula)
    varOrApp = do
      name <- identifier
      option (Var UnknownS name) (parseTerm >>= return . Measure UnknownS name)
      
{- Misc -}      

parseIdentifier :: Parser Id
parseIdentifier = try $ do
  name <- identifier
  if isUpper $ head name then unexpected ("capitalized " ++ show name) else return name

parseTypeName :: Parser Id
parseTypeName = try $ do
  name <- identifier
  if isLower $ head name then unexpected ("non-capitalized " ++ show name) else return name
