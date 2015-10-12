module Synquid.Parser where

import Synquid.Logic
import Synquid.Program
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
parseType = Parsec.choice [parseScalarType{-, parseFunctionType-}]

parseScalarType :: Parser (TypeSkeleton Formula)
parseScalarType = Parsec.choice [parseScalarRefType, parseScalarUnrefType]

parseScalarUnrefType :: Parser (TypeSkeleton Formula)
parseScalarUnrefType = do
	baseType <- parseBaseType
	return $ ScalarT baseType [] $ BoolLit True

parseScalarRefType :: Parser (TypeSkeleton Formula)
parseScalarRefType = do
	Parsec.char '{'
	Parsec.spaces
	baseType <- parseBaseType
	Parsec.spaces
	Parsec.char '|'
	Parsec.spaces
	refinement <- parseRefinement
	Parsec.spaces
	Parsec.char '}'
	return $ ScalarT baseType [] refinement

parseBaseType :: Parser BaseType
parseBaseType = BoolT <$ Parsec.string "Bool" <|> IntT <$ Parsec.string "Int"

parseRefinement = Expr.buildExpressionParser exprTable (parseTerm <* Parsec.spaces)
	where
		exprTable = [
			[bin "*" (|*|)],
			[bin "+" (|+|), bin "-" (|-|), bin "/+" (/+/), bin "/*" (/*/), bin "/-" (/-/)],
			[bin "=" (|=|), bin "/=" (|/=|), bin "<=" (|<=|), bin "<" (|<|), bin ">=" (|>=|), bin ">" (|>|),
				bin "/<=" (/<=/)],
			[bin "&" (|&|), bin "|" (|||)],
			[bin "=>" (|=>|), bin "<=>" (|<=>|)]]
		bin opChar func = Expr.Infix (Parsec.try $ Parsec.string opChar <* Parsec.spaces >> return func) Expr.AssocLeft

parseTerm :: Parser Formula
parseTerm = Parsec.choice [Parsec.between (Parsec.char '(') (Parsec.char ')') parseRefinement, parseBoolLit, parseIntLit]

parseBoolLit :: Parser Formula
parseBoolLit = fmap BoolLit $ False <$ Parsec.string "false" <|> True <$ Parsec.string "true"

parseIntLit :: Parser Formula
parseIntLit = fmap (IntLit . read) $ Parsec.many1 Parsec.digit

parseUnaryOp :: Parser Formula
parseUnaryOp = do
	op <- Neg <$ Parsec.char '-' <|> Not <$ Parsec.char '!'
	refinement <- parseRefinement
	return $ Unary op refinement

parseBinaryOp :: Parser (Formula -> Formula -> Formula)
parseBinaryOp = fmap Binary $ Parsec.choice [Times <$ Parsec.string "*", Plus <$ Parsec.string "+"]
	where
