{-# LANGUAGE TupleSections #-}

-- | The parser for Synquid's program specification DSL.
module Synquid.Parser where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.Tokens
import Synquid.Util

import Data.List
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Monad.State
import Control.Applicative hiding ((<|>), many)

import Text.Parsec hiding (State)
import qualified Text.Parsec.Token as Token
import Text.Parsec.Expr
import Text.Parsec.Indent
import Text.Parsec.Error
import Text.PrettyPrint.ANSI.Leijen (text, vsep)

import Debug.Trace

{- Interface -}

type Parser a = IndentParser String () a

parseProgram :: Parser [Declaration]
parseProgram = whiteSpace *> option [] (block parseDeclaration) <* eof

parseFromFile :: Parser a -> String -> IO (Either ParseError a)
parseFromFile aParser fname = do
  input <- readFile fname
  return $ runIndent fname $ runParserT aParser () fname input
  
toErrorMessage :: ParseError -> ErrorMessage  
toErrorMessage err = ErrorMessage ParseError (errorPos err) 
  (vsep $ map text $ tail $ lines $ showErrorMessages "or" "unknown parse error" "expecting" "Unexpected" "end of input" (errorMessages err))

{- Lexical analysis -}

opNames :: [String]
opNames = Map.elems unOpTokens ++ (Map.elems binOpTokens \\ keywords) ++ otherOps

opStart :: [Char]
opStart = nub (map head opNames)

opLetter :: [Char]
opLetter = nub (concatMap tail opNames)

synquidDef :: Token.GenLanguageDef String st (State SourcePos)
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
  
lexer :: Token.GenTokenParser String st (State SourcePos)
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
dot = Token.dot lexer
      
{- Declarations -}      

parseDeclaration :: Parser Declaration
parseDeclaration = attachPosBefore $
  (choice [ parseTypeDecl
         , parseDataDecl
         , parseMeasureDecl
         , parsePredDecl
         , parseQualifierDecl
         , parseMutualDecl
         , parseInlineDecl
         , parseFuncDeclOrGoal] <?> "declaration")

parseTypeDecl :: Parser BareDeclaration
parseTypeDecl = do
  reserved "type"
  typeName <- parseTypeName
  typeVars <- many parseIdentifier
  reservedOp "="
  typeDef <- parseType
  return $ TypeDecl typeName typeVars typeDef

parseDataDecl :: Parser BareDeclaration
parseDataDecl = do
  reserved "data"
  typeName <- parseTypeName
  tParams <- many (sameOrIndented >> parseIdentifier)
  pParams <- many (sameOrIndented >> parsePredParam)
  constructors <- option [] (reserved "where" >> indented >> block parseConstructorSig) 
  return $ DataDecl typeName tParams pParams constructors  
  where
    parsePredParam = do
      p <- angles parsePredSig
      var <- option False (reservedOp (unOpTokens Map.! Not) >> return True)
      return (p, var)

parseConstructorSig :: Parser ConstructorSig
parseConstructorSig = do
  ctorName <- parseTypeName
  reservedOp "::"
  ctorType <- parseType  
  return $ ConstructorSig ctorName ctorType

parseMeasureDecl :: Parser BareDeclaration
parseMeasureDecl = do
  isTermination <- option False (reserved "termination" >> return True)
  reserved "measure"
  measureName <- parseIdentifier
  reservedOp "::"
  inSort <- parseSort
  reservedOp "->"
  (outSort, post) <- parseRefinedSort <|> ((, ftrue) <$> parseSort)
  cases <- option [] (reserved "where" >> indented >> block parseDefCase) 
  return $ MeasureDecl measureName inSort outSort post cases isTermination
  where
    parseDefCase = do
      ctor <- parseTypeName
      binders <- many parseIdentifierOrBlank
      reservedOp "->"
      body <- parseFormula
      return $ MeasureCase ctor binders body  
  
parsePredDecl :: Parser BareDeclaration
parsePredDecl = do
  reserved "predicate"
  sig <- parsePredSig
  return $ PredDecl sig
  
parseQualifierDecl :: Parser BareDeclaration
parseQualifierDecl = do
  reserved "qualifier"
  QualifierDecl <$> braces (commaSep parseFormula)
  
parseMutualDecl :: Parser BareDeclaration
parseMutualDecl = do
  reserved "mutual"
  MutualDecl <$> braces (commaSep parseIdentifier)  
  
parseInlineDecl :: Parser BareDeclaration
parseInlineDecl = do
  reserved "inline"
  name <- parseIdentifier
  args <- many parseIdentifier
  reservedOp "="
  body <- parseFormula
  return $ InlineDecl name args body
  
parseFuncDeclOrGoal :: Parser BareDeclaration
parseFuncDeclOrGoal = do
  funcName <- parseIdentifier
  (reservedOp "::" >> FuncDecl funcName <$> parseSchema) <|>
    (reservedOp "=" >> SynthesisGoal funcName <$> parseImpl)
  
{- Types -}

parseSchema :: Parser RSchema
parseSchema = parseForall <|> (Monotype <$> parseType)

parseForall :: Parser RSchema
parseForall = do
  sig <- angles parsePredSig
  dot
  sch <- parseSchema
  return $ ForallP sig sch

parseType :: Parser RType
parseType = withPos (choice [try parseFunctionTypeWithArg, parseFunctionTypeMb] <?> "type")
  
-- | Parse top-level type that starts with an argument name, and thus must be a function type
parseFunctionTypeWithArg = do
  argId <- parseArgName  
  argType <- parseUnrefTypeWithArgs <|> parseTypeAtom
  reservedOp "->"
  returnType <- parseType
  return $ FunctionT argId argType returnType
  where
    parseArgName = parseIdentifier <* reservedOp ":"

-- | Parse top-level type that does not start with an argument name 
-- and thus could be a scalar or a function type depending on whether followed by ->
parseFunctionTypeMb = do
  argType <- parseUnrefTypeWithArgs <|> parseTypeAtom   
  parseFunctionRest argType <|> return argType
  where
    parseFunctionRest argType = do
      reservedOp "->"
      returnType <- parseType
      return $ FunctionT ("arg" ++ show (arity returnType)) argType returnType

parseTypeAtom :: Parser RType
parseTypeAtom = choice [
  parens parseType,
  parseScalarRefType,
  parseUnrefTypeNoArgs,
  parseListType
  ]
  
parseUnrefTypeNoArgs = do
  baseType <- parseBaseType
  return $ ScalarT baseType ftrue  
  where
    parseBaseType = choice [
      BoolT <$ reserved "Bool",
      IntT <$ reserved "Int",
      (\name -> DatatypeT name [][]) <$> parseTypeName,
      TypeVarT Map.empty <$> parseIdentifier]
  
parseUnrefTypeWithArgs = do
  name <- parseTypeName
  typeArgs <- many (sameOrIndented >> parseTypeAtom)
  predArgs <- many (sameOrIndented >> angles parsePredArg)
  return $ ScalarT (DatatypeT name typeArgs predArgs) ftrue    
  
parsePredArg = braces parseFormula <|> (flip (Pred AnyS) [] <$> parseIdentifier)
  
parseScalarUnrefType = parseUnrefTypeWithArgs <|> parseUnrefTypeNoArgs
  
parseScalarRefType = braces $ do
  ScalarT baseType _ <- parseScalarUnrefType
  reservedOp "|"
  refinement <- parseFormula
  return $ ScalarT baseType refinement  

parseListType = do
  elemType <- brackets parseType
  return $ ScalarT (DatatypeT "List" [elemType] []) ftrue
  
parseSort :: Parser Sort
parseSort = withPos (parseSortWithArgs <|> parseSortAtom <?> "sort")
  where
    parseSortAtom = choice [
      parens parseSort,
      BoolS <$ reserved "Bool",
      IntS <$ reserved "Int",
      VarS <$> parseIdentifier,
      flip DataS [] <$> parseTypeName
      ]
      
    parseSortWithArgs = choice [
      SetS <$> (reserved "Set" >> sameOrIndented >> parseSortAtom),
      do
        typeName <- parseTypeName        
        typeParams <- many (sameOrIndented >> parseSortAtom)
        return $ DataS typeName typeParams
      ]
      
parseRefinedSort :: Parser (Sort, Formula)
parseRefinedSort = braces $ do
  s <- parseSort
  reservedOp "|"
  refinement <- parseFormula
  return (s, refinement)
      
{- Formulas -}

-- | Expression table
exprTable mkUnary mkBinary withGhost = [
  [unary Not, unary Neg],
  [binary Times AssocLeft],
  [binary Plus AssocLeft, binary Minus AssocLeft],
  [binary Eq AssocNone, binary Neq AssocNone, binary Le AssocNone, binary Lt AssocNone, binary Ge AssocNone, binary Gt AssocNone] 
    ++ if withGhost then [binaryWord Member AssocNone] else [],
  [binary And AssocLeft, binary Or AssocLeft],
  [binary Implies AssocRight, binary Iff AssocRight]]
  where
    unary op = Prefix (reservedOp (unOpTokens Map.! op) >> return (mkUnary op))
    binary op assoc = Infix (reservedOp (binOpTokens Map.! op) >> return (mkBinary op)) assoc
    binaryWord op assoc = Infix (reserved (binOpTokens Map.! op) >> return (mkBinary op)) assoc    

{-
 - | @Formula@ parsing is broken up into two functions: @parseFormula@ and @parseTerm@. @parseFormula's@ responsible
 - for parsing binary and unary expressions that consist of other @Formula@s, while @parseTerm@ parses everything else
 - (ie literals).
 -}
parseFormula :: Parser Formula
parseFormula = withPos $ (buildExpressionParser (exprTable Unary Binary True) parseTerm <?> "refinement term")

parseTerm :: Parser Formula
parseTerm = parseIte <|> try parseAppTerm <|> parseAtomTerm
  where
    parseIte = do
      reserved "if"
      e0 <- parseFormula
      reserved "then"
      e1 <- parseFormula
      reserved "else"
      e2 <- parseFormula
      return $ Ite e0 e1 e2
    parseAppTerm = parseConsApp <|> parsePredApp
    parseAtomTerm = choice [
        parens parseFormula
      , parseBoolLit
      , parseIntLit
      , parseSetLitOrComp
      , parseNullaryCons
      , parseVariable
      ]      
    parseBoolLit = (reserved "False" >> return ffalse) <|> (reserved "True" >> return ftrue)
    parseIntLit = IntLit <$> natural
    parseSetLitOrComp = brackets (try parseSetComp <|> parseSetLit)
    parseSetComp = do
      name <- parseIdentifier
      reservedOp "|"
      e <- parseFormula
      return $ SetComp (Var AnyS name) e
    parseSetLit = SetLit AnyS <$> commaSep parseFormula    
    parseNullaryCons = flip (Cons AnyS) [] <$> parseTypeName
    parseVariable = Var AnyS <$> parseIdentifier 
    parseConsApp = do
      name <- parseTypeName
      args <- many1 (sameOrIndented >> parseAtomTerm)
      return $ Cons AnyS name args
    parsePredApp = do
      name <- parseIdentifier
      args <- many1 (sameOrIndented >> parseAtomTerm)
      return $ Pred AnyS name args
      
{- Implementations -}

parseImpl :: Parser UProgram
parseImpl = withPos (parseError <|> parseLet <|> parseFun <|> parseMatch <|> parseIf <|> parseETerm)

parseError = reserved "error" >> return (untyped PErr)

parseFun = do
  reservedOp "\\"
  x <- parseIdentifierOrBlank
  reservedOp "."
  body <- parseImpl
  return $ untyped $ PFun x body

parseLet = do
  reserved "let"
  x <- parseIdentifierOrBlank
  reservedOp "="
  e1 <- parseImpl
  reserved "in"
  e2 <- parseImpl
  return $ untyped $ PLet x e1 e2

parseMatch = do
    reserved "match"
    scr <- parseETerm
    reserved "with"    
    cases <- indented >> block parseCase
    return $ untyped $ PMatch scr cases
  where
    parseCase = do
      ctor <- parseTypeName
      args <- many parseIdentifierOrBlank
      reservedOp "->"
      body <- parseImpl
      return $ Case ctor args body

parseIf = do
  reserved "if"
  iCond <- parseETerm
  reserved "then" 
  iThen <- parseImpl
  reserved "else"
  iElse <- parseImpl
  return $ untyped $ PIf iCond iThen iElse

parseETerm = buildExpressionParser (exprTable mkUnary mkBinary False) parseAppTerm <?> "elimination term"
  where
    mkUnary op = untyped . PApp (untyped $ PSymbol (unOpTokens Map.! op))
    mkBinary op p1 p2 = untyped $ PApp (untyped $ PApp (untyped $ PSymbol (binOpTokens Map.! op)) p1) p2
    parseAppTerm = do
      head <- parseAtomTerm
      args <- many (sameOrIndented >> (try parseAtomTerm <|> parens parseImpl))
      return $ foldl (\e1 e2 -> untyped $ PApp e1 e2) head args
    parseAtomTerm = choice [
        parens (withOptionalType parseImpl)
      , parseHole
      , parseBoolLit
      , parseIntLit
      , parseSymbol
      , parseList
      ]
    parseBoolLit = (reserved "False" >> return (untyped $ PSymbol "False")) <|> (reserved "True" >> return (untyped $ PSymbol "True"))
    parseIntLit = natural >>= return . untyped . PSymbol . show
    parseHole = reserved "??" >> return (untyped PHole)
    parseSymbol = (parseIdentifier <|> parseTypeName) >>= (return . untyped . PSymbol)
    
parseList = do
  elems <- brackets (commaSep parseImpl)
  return $ foldr cons nil elems
  where 
    cons x xs = untyped $ PApp (untyped $ PApp (untyped $ PSymbol "Cons") x) xs
    nil = untyped $ PSymbol "Nil"

withOptionalType p = do
  (Program content _) <- p
  typ <- option AnyT $ reserved "::" >> parseType
  return $ Program content typ
      
{- Misc -}

parsePredSig :: Parser PredSig
parsePredSig = do
  predName <- parseIdentifier
  reservedOp "::"
  sorts <- parseSort `sepBy1` reservedOp "->"
  return $ PredSig predName (init sorts) (last sorts)

parseIdentifier :: Parser Id
parseIdentifier = try $ do
  name <- identifier
  if isTypeName name 
    then unexpected ("capitalized " ++ show name) 
    else if name == dontCare then unexpected ("blank") else return name
  
parseIdentifierOrBlank :: Parser Id
parseIdentifierOrBlank = try $ do
  name <- identifier
  if isTypeName name then unexpected ("capitalized " ++ show name) else return name  

parseTypeName :: Parser Id
parseTypeName = try $ do
  name <- identifier
  if not (isTypeName name) then unexpected ("non-capitalized " ++ show name) else return name
  
-- | 'attachPosBefore' @p@ : parser that behaves like @p@, but also attaches the source position before the first token it parsed to the result
attachPosBefore :: Parser a -> Parser (Pos a)
attachPosBefore = liftM2 Pos getPosition  
  
{- Debug -}

printRefPos :: String -> Parser ()
printRefPos msg = do
  pos <- get
  trace (msg ++ show pos) $ return ()
  
printCurPos :: String -> Parser ()
printCurPos msg = do
  pos <- getPosition
  trace (msg ++ show pos) $ return ()  
