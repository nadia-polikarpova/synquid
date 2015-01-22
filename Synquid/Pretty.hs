{-# LANGUAGE FlexibleInstances #-}

module Synquid.Pretty (   
  -- * Interface
  Pretty (..),
  Doc,
  renderPretty,
  putDoc,
  -- * Basic documents  
  empty,
  isEmpty,
  text,
  int,
  integer,
  linebreak,
  semi,
  lbrace, rbrace,
  -- * Combinators
  option,
  optionMaybe,  
  (<+>), ($+$), (<>),
  hcat,
  vcat,
  hsep,
  vsep,
  punctuate,
  tupled,
  -- * Enclosing
  commaSep,  
  parens,
  condParens,
  dquotes,
  brackets,
  braces,
  angles,
  spaces,
    -- * Indentation
  nest,
  -- * Structures
  hMapDoc,
  vMapDoc  
) where

import Synquid.Logic
import Synquid.Program

import Text.PrettyPrint.ANSI.Leijen hiding ((<+>), (<$>), hsep, vsep)
import qualified Text.PrettyPrint.ANSI.Leijen as L
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map, (!))

import Control.Lens

infixr 5 $+$
infixr 6 <+>
  
-- | Is document empty?
isEmpty d = case renderCompact d of
  SEmpty -> True
  _ -> False
  
-- | Separate two documents by space if both are nonempty  
doc1 <+> doc2 = if isEmpty doc1
  then doc2
  else if isEmpty doc2
    then doc1
    else doc1 L.<+> doc2
    
-- | Separate two documents by linebreak if both are nonempty    
doc1 $+$ doc2 = if isEmpty doc1
  then doc2
  else if isEmpty doc2
    then doc1
    else doc1 L.<$> doc2

-- | Separate by spaces
hsep = foldr (<+>) empty    
-- | Separate by new lines
vsep = foldr ($+$) empty    
-- | Separate by commas
commaSep = hsep . punctuate comma

-- | Enclose in spaces    
spaces d = space <> d <> space
-- | Conditionally enclose in parentheses  
condParens b doc = if b then parens doc else doc
      
-- | Conditionally produce a doc
option b doc = if b then doc else empty

-- | Convert a 'Just' value to doc
optionMaybe mVal toDoc = case mVal of
  Nothing -> empty
  Just val -> toDoc val
    
entryDoc keyDoc valDoc (k, v) = nest 2 $ (keyDoc k  <+> text "->") <+> valDoc v 
  
hMapDoc :: (k -> Doc) -> (v -> Doc) -> Map k v -> Doc    
hMapDoc keyDoc valDoc m = brackets (commaSep (map (entryDoc keyDoc valDoc) (Map.toList m)))  
  
vMapDoc :: (k -> Doc) -> (v -> Doc) -> Map k v -> Doc  
vMapDoc keyDoc valDoc m = vsep $ map (entryDoc keyDoc valDoc) (Map.toList m)  

{- Formulas -}

instance Pretty UnOp where
  pretty Neg = text "-"
  pretty Not = text "!"

instance Show UnOp where
  show = show . pretty
  
instance Pretty BinOp where
  pretty Plus = text "+"
  pretty Minus = text "-"
  pretty Eq = text "=="
  pretty Neq = text "/="
  pretty Lt = text "<"
  pretty Le = text "<="
  pretty Gt = text ">"
  pretty Ge = text ">="
  pretty And = text "&&"
  pretty Or = text "||"
  pretty Implies = text "==>"  
  pretty Iff = text "<==>"  
  
instance Show BinOp where
  show = show . pretty  

-- | Binding power of a formula
power :: Formula -> Int
power (Unary _ _) = 5
power (Binary op _ _) 
  | op `elem` [Plus, Minus] = 4
  | op `elem` [Eq, Neq, Lt, Le, Gt, Ge] = 3
  | op `elem` [And, Or] = 2
  | op `elem` [Implies] = 1
  | op `elem` [Iff] = 0
power _ = 5

-- | Pretty-printed formula  
fmlDoc :: Formula -> Doc
fmlDoc fml = fmlDocAt (-1) fml

-- | 'fmlDocAt' @n fml@ : print @expr@ in a context with binding power @n@
fmlDocAt :: Int -> Formula -> Doc
fmlDocAt n fml = condParens (n' <= n) (
  case fml of
    BoolLit b -> pretty b
    IntLit i -> pretty i
    Var ident -> text ident
    Unknown ident -> text "?" <> text ident
    Unary op e -> pretty op <> fmlDocAt n' e
    Binary op e1 e2 -> fmlDocAt n' e1 <+> pretty op <+> fmlDocAt n' e2
  )
  where
    n' = power fml
    
instance Pretty Formula where pretty e = fmlDoc e

instance Show Formula where
  show = show . pretty
    
instance Pretty Valuation where
  pretty val = braces $ commaSep $ map pretty $ Set.toList val
  
instance Pretty Solution where
  pretty = hMapDoc text pretty
  
instance Pretty QSpace where
  pretty space = braces $ commaSep $ map pretty $ view qualifiers space
  
instance Pretty QMap where
  pretty = hMapDoc text pretty  

programDoc :: Program -> Doc
programDoc (PIntLit i) = pretty i
programDoc (PVar ident) = text ident
programDoc (PApp f x) = pretty f <+> pretty x
programDoc (PIf c t e) = parens (fmlDoc c <+> text "?" <+> programDoc t <+> text ":" <+> programDoc e)
programDoc (PHole t) = parens (text "??" <+> text "::" <+> pretty t)

instance Pretty Program where
  pretty = programDoc
  
instance Show Program where
  show = show . pretty