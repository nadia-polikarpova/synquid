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
import Synquid.SMTSolver

import Text.PrettyPrint.ANSI.Leijen hiding ((<+>), (<$>), hsep, vsep)
import qualified Text.PrettyPrint.ANSI.Leijen as L
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map, (!))
import qualified Data.Bimap as BMap
import Data.Bimap (Bimap)

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
  pretty Times = text "*"
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
power (Unary _ _) = 6
power (Binary op _ _) 
  | op `elem` [Times] = 5
  | op `elem` [Plus, Minus] = 4
  | op `elem` [Eq, Neq, Lt, Le, Gt, Ge] = 3
  | op `elem` [And, Or] = 2
  | op `elem` [Implies] = 1
  | op `elem` [Iff] = 0
power _ = 6

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
    Unknown ident -> text ident
    Unary op e -> pretty op <> fmlDocAt n' e
    Binary op e1 e2 -> fmlDocAt n' e1 <+> pretty op <+> fmlDocAt n' e2
    Parameter ident -> text "??" <> text ident
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
  pretty = vMapDoc text pretty  

programDoc :: (Pretty s, Pretty c) => Program s c -> Doc
programDoc (PSymbol s) = pretty s
programDoc (PApp f x) = parens (pretty f <+> pretty x)
programDoc (PFun x e) = parens (text "\\" <> pretty x <+> text "." <+> pretty e)
programDoc (PIf c t e) = parens (pretty c <+> text "?" <+> programDoc t <+> text ":" <+> programDoc e)
programDoc (PFix f e) = parens (text "let rec" <> pretty f <+> text "=" <+> pretty e)

instance (Pretty s, Pretty c) => Pretty (Program s c) where
  pretty = programDoc
  
instance (Pretty s, Pretty c) => Show (Program s c) where
  show = show . pretty
  
instance Pretty SMTModel where
  pretty = hMapDoc text pretty
  
instance Show SMTModel where
  show = show . pretty

instance Pretty PSolution where
  pretty sol = pretty (sol ^. solution) <+> pretty (sol ^. model)
  
instance Show PSolution where
  show = show . pretty

instance Pretty BaseType where
  pretty IntT = text "int"
  pretty BoolT = text "bool"  
  
prettySType :: SType -> Doc
prettySType (ScalarT base _) = pretty base
prettySType (FunctionT t1 t2) = parens $ pretty t1 <+> text "->" <+> pretty t2  

instance Pretty SType where
  pretty = prettySType
  
instance Show SType where
 show = show . pretty
  
prettyType :: RType -> Doc
prettyType (ScalarT base (v, fml)) = braces $ text v <> text ":" <> pretty base <+> text "|" <+> pretty fml
prettyType (FunctionT t1 t2) = parens $ pretty t1 <+> text "->" <+> pretty t2

instance Pretty RType where
  pretty = prettyType
  
instance Show RType where
 show = show . pretty  
  
prettyBinding (name, typ) = text name <+> text "::" <+> pretty typ

prettyAssumptions env = commaSep (map pretty (Set.toList $ env ^. assumptions) ++ map (pretty . fnot) (Set.toList $ env ^. negAssumptions)) 
prettyBindings env = commaSep (map pretty (Map.elems (env ^. symbols))) 
  
instance Pretty Environment where
  -- pretty env = vsep (map prettyBinding (BMap.toList (env ^. symbols)) ++ map pretty (Set.toList $ env ^. assumptions)) 
  pretty env = commaSep (map pretty (Map.elems (env ^. symbols)) ++ map pretty (Set.toList $ env ^. assumptions) ++ map (pretty . fnot) (Set.toList $ env ^. negAssumptions)) 
  
prettyConstraint :: Constraint -> Doc  
prettyConstraint (Subtype env t1 t2) = prettyAssumptions env <+> text "|-" <+> pretty t1 <+> text "<:" <+> pretty t2
prettyConstraint (WellFormed env t) = prettyBindings env <+> text "|-" <+> pretty t
prettyConstraint (WellFormedCond env c) = prettyBindings env <+> text "|-" <+> pretty c
prettyConstraint (WellFormedSymbol env t) = prettyBindings env <+> text "|-" <+> text "symbol" <+> pretty t
  
instance Pretty Constraint where
  pretty = prettyConstraint
   
