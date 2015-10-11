module Synquid.Parser where

import Synquid.Logic
import Synquid.Program
import Control.Applicative ((<$))
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>), (<?>))

type Parser = Parsec.Parsec String ()

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

parseRefinement :: Parser Formula
parseRefinement = Parsec.choice [parseBoolLit, parseIntLit, parseUnaryOp{-, parseBinaryOp-}]

parseBoolLit :: Parser Formula
parseBoolLit = fmap BoolLit $ False <$ Parsec.string "false" <|> True <$ Parsec.string "true"

parseIntLit :: Parser Formula
parseIntLit = fmap (IntLit . read) $ Parsec.many1 Parsec.digit

parseUnaryOp :: Parser Formula
parseUnaryOp = do
	op <- Neg <$ Parsec.char '-' <|> Not <$ Parsec.char '!'
	refinement <- parseRefinement
	return $ Unary op refinement
