{-# LANGUAGE FlexibleInstances, UndecidableInstances, FlexibleContexts #-}

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
  (<+>), ($+$), (<>), (</>),
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
  squotes,
  dquotes,
  brackets,
  braces,
  angles,
  spaces,
  -- * Indentation
  nest,
  hang,
  indent,
  -- * Structures
  hMapDoc,
  vMapDoc,
  mkTable,
  mkTableLaTeX,
  -- * Programs
  prettySpec,
  prettySolution,
  -- * Highlighting
  plain,
  errorDoc,
  -- * Counting
  typeNodeCount,
  programNodeCount
) where

import Synquid.Logic
import Synquid.Type
import Synquid.Error
import Synquid.Program
import Synquid.Tokens
import Synquid.Util

import Text.PrettyPrint.ANSI.Leijen hiding ((<+>), (<$>), hsep, vsep)
import qualified Text.PrettyPrint.ANSI.Leijen as L
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map, (!))
import Data.List

import Control.Lens

infixr 5 $+$
infixr 6 <+>

tab = 2

-- | Is document empty?
isEmpty d = case renderCompact d of
  SEmpty -> True
  _ -> False

-- | Separate two documents by space if both are nonempty
doc1 <+> doc2 | isEmpty doc1 = doc2
              | isEmpty doc2 = doc1
              | otherwise    = doc1 L.<+> doc2

-- | Separate two documents by linebreak if both are nonempty
doc1 $+$ doc2 | isEmpty doc1 = doc2
              | isEmpty doc2 = doc1
              | otherwise    = doc1 L.<$> doc2

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

{- Syntax highlighting -}

errorDoc = red
keyword = bold . blue . text
parenDoc = dullwhite
operator = dullwhite . text
special = bold . text
intLiteral = dullcyan . pretty

hlParens = enclose (parenDoc lparen) (parenDoc rparen)
hlBraces = enclose (parenDoc lbrace) (parenDoc rbrace)
hlAngles = enclose (parenDoc langle) (parenDoc rangle)
hlBrackets = enclose (parenDoc lbracket) (parenDoc rbracket)

condHlParens b doc = if b then hlParens doc else doc

{- Formulas -}

instance Pretty Sort where
  pretty IntS = text "Int"
  pretty BoolS = text "Bool"
  pretty (SetS el) = text "Set" <+> pretty el
  pretty (VarS name) = text name
  pretty (DataS name args) = text name <+> hsep (map (hlParens . pretty) args)
  pretty AnyS = operator "?"

instance Show Sort where
  show = show . pretty
  
instance Pretty PredSig where
  pretty (PredSig p argSorts resSort) = hlAngles $ text p <+> text "::" <+> hsep (map (\s -> pretty s <+> text "->") argSorts) <+> pretty resSort

instance Pretty UnOp where
  pretty op = operator $ unOpTokens Map.! op

instance Show UnOp where
  show = show . pretty

instance Pretty BinOp where
  pretty op = operator $ binOpTokens Map.! op

instance Show BinOp where
  show = show . pretty

-- | Binding power of a formula
power :: Formula -> Int
power (Pred _ _ []) = 10
power (Cons _ _ []) = 10
power Pred {} = 9
power Cons {} = 9
power Unary {} = 8
power (Binary op _ _)
  | op `elem` [Times, Intersect] = 7
  | op `elem` [Plus, Minus, Union, Diff] = 6
  | op `elem` [Eq, Neq, Lt, Le, Gt, Ge, Member, Subset] = 5
  | op `elem` [And, Or] = 4
  | op `elem` [Implies] = 3
  | op `elem` [Iff] = 2
power All {} = 1
power Ite {} = 1
power _ = 10

-- | Pretty-printed formula
fmlDoc :: Formula -> Doc
fmlDoc = fmlDocAt 0

-- | 'fmlDocAt' @n fml@ : print @expr@ in a context with binding power @n@
fmlDocAt :: Int -> Formula -> Doc
fmlDocAt n fml = condHlParens (n' <= n) (
  case fml of
    BoolLit b -> pretty b
    IntLit i -> intLiteral i
    SetLit s elems -> withSort (SetS s) (hlBrackets $ commaSep $ map fmlDoc elems)
    SetComp (Var s x) e -> withSort (SetS s) (hlBrackets $ text x <> operator "|" <> pretty e)
    Var s name -> withSort s $ if name == valueVarName then special name else text name
    Unknown s name -> if Map.null s then text name else hMapDoc pretty pretty s <> text name
    Unary op e -> pretty op <> fmlDocAt n' e
    Binary op e1 e2 -> fmlDocAt n' e1 <+> pretty op <+> fmlDocAt n' e2
    Ite e0 e1 e2 -> keyword "if" <+> fmlDoc e0 <+> keyword "then" <+> fmlDoc e1 <+> keyword "else" <+> fmlDoc e2
    Pred b name args -> withSort b $ text name <+> hsep (map (fmlDocAt n') args)
    Cons b name args -> withSort b $ hlParens (text name <+> hsep (map (fmlDocAt n') args))
    All x e -> keyword "forall" <+> pretty x <+> operator "." <+> fmlDoc e
  )
  where
    n' = power fml
    withSort s doc = doc -- <> text ":" <> pretty s

instance Pretty Formula where pretty e = fmlDoc e

instance Show Formula where
  show = show . pretty

instance Pretty Valuation where
  pretty val = braces $ commaSep $ map pretty $ Set.toList val

instance Pretty Solution where
  pretty = hMapDoc text pretty

instance Pretty QSpace where
  pretty space = braces $ commaSep $ map pretty $ view qualifiers space

instance Show QSpace where
  show = show . pretty

instance Pretty QMap where
  pretty = vMapDoc text pretty
  
{- Types -}

prettyBase :: Pretty r => (TypeSkeleton r -> Doc) -> BaseType r -> Doc
prettyBase prettyType base = case base of 
  IntT -> text "Int"
  BoolT -> text "Bool"
  TypeVarT s name -> if Map.null s then text name else hMapDoc pretty pretty s <> text name
  DatatypeT name tArgs pArgs -> text name <+> hsep (map prettyType tArgs) <+> hsep (map (hlAngles . pretty) pArgs)

instance Pretty (BaseType ()) where
  pretty = prettyBase (hlParens . pretty)

instance Pretty (BaseType Formula) where
  pretty = prettyBase (prettyTypeAt 1)

instance Show (BaseType Formula) where
  show = show . pretty
  
prettySType :: SType -> Doc
prettySType (ScalarT base _) = pretty base
prettySType (FunctionT _ t1 t2) = hlParens (pretty t1 <+> operator "->" <+> pretty t2)
prettySType AnyT = text "_"

instance Pretty SType where
  pretty = prettySType

instance Show SType where
 show = show . pretty

-- | Pretty-printed refinement type
prettyType :: RType -> Doc
prettyType t = prettyTypeAt 0 t

-- | Binding power of a type
typePower :: RType -> Int
typePower FunctionT {} = 1
typePower (ScalarT (DatatypeT _ tArgs pArgs) r)
  | ((not (null tArgs) || not (null pArgs)) && (r == ftrue)) = 2
typePower _ = 3

prettyTypeAt :: Int -> RType -> Doc
prettyTypeAt n t = condHlParens (n' <= n) (
  case t of
    ScalarT base (BoolLit True) -> pretty base
    ScalarT base fml -> hlBraces (pretty base <> operator "|" <> pretty fml)
    AnyT -> text "_"
    FunctionT x t1 t2 -> text x <> operator ":" <> prettyTypeAt n' t1 <+> operator "->" <+> prettyTypeAt 0 t2
    LetT x t1 t2 -> text "LET" <+> text x <> operator ":" <> prettyTypeAt n' t1 <+> operator "IN" <+> prettyTypeAt 0 t2
  )
  where
    n' = typePower t

instance Pretty RType where
  pretty = prettyType

instance Show RType where
 show = show . pretty
 
prettySchema :: Pretty (TypeSkeleton r) => SchemaSkeleton r -> Doc
prettySchema sch = case sch of
  Monotype t -> pretty t
  ForallT a sch' -> hlAngles (text a) <+> operator "." <+> prettySchema sch'
  ForallP sig sch' -> pretty sig <+> operator "." <+> prettySchema sch'

instance Pretty SSchema where
  pretty = prettySchema

instance Show SSchema where
 show = show . pretty

instance Pretty RSchema where
  pretty = prettySchema

instance Show RSchema where
  show = show . pretty

{- Programs -}  

prettyCase :: (Pretty t) => Case t -> Doc
prettyCase cas = hang tab $ text (constructor cas) <+> hsep (map text $ argNames cas) <+> operator "->" </> prettyProgram (expr cas)

prettyProgram :: (Pretty t) => Program t -> Doc
prettyProgram (Program p typ) = case p of
    PSymbol s -> case asInteger s of 
                  Nothing -> if s == valueVarName then special s else text s
                  Just n -> intLiteral n
    PApp f x -> let
      optParens p = case p of
        Program (PSymbol _) _ -> prettyProgram p
        Program PHole _ -> prettyProgram p
        _ -> hlParens (prettyProgram p)
      prefix = hang tab $ prettyProgram f </> optParens x
      in case content f of
          PSymbol name -> if name `elem` Map.elems unOpTokens
                            then hang tab $ operator name <+> optParens x
                            else prefix
          PApp g y -> case content g of
            PSymbol name -> if name `elem` Map.elems binOpTokens
                              then hang tab $ optParens y </> operator name </> optParens x -- Binary operator: use infix notation
                              else prefix
            _ -> prefix
          _ -> prefix
    PFun x e -> nest 2 $ operator "\\" <> text x <+> operator "." </> prettyProgram e
    PIf c t e -> linebreak <> (hang tab $ keyword "if" <+> prettyProgram c $+$ (hang tab (keyword "then" </> prettyProgram t)) $+$ (hang tab (keyword "else" </> prettyProgram e)))
    PMatch l cases -> linebreak <> (hang tab $ keyword "match" <+> prettyProgram l <+> keyword "with" $+$ vsep (map prettyCase cases))
    PFix fs e -> prettyProgram e
    PLet x e e' -> linebreak <> (align $ hang tab (keyword "let" <+> withType (text x) (typeOf e) <+> operator "=" </> prettyProgram e </> keyword "in") $+$ prettyProgram e')
    PHole -> if show (pretty typ) == dontCare then operator "??" else hlParens $ operator "?? ::" <+> pretty typ
    PErr -> keyword "error"
  where
    withType doc t = doc -- <> text ":" <+> pretty t

instance (Pretty t) => Pretty (Program t) where
  pretty = prettyProgram

instance (Pretty t) => Show (Program t) where
  show = show . pretty

instance Pretty TypeSubstitution where
  pretty = hMapDoc text pretty
  
instance Pretty MeasureCase where
  pretty (MeasureCase cons args def) = text cons <+> hsep (map text args) <+> text "->" <+> pretty def
  
instance Pretty MeasureDef where
  pretty (MeasureDef inSort outSort defs post) = nest 2 (pretty inSort <+> text "->" <+> pretty outSort <+> braces (pretty post) $+$ vsep (map pretty defs))

prettyBinding (name, typ) = text name <+> operator "::" <+> pretty typ

prettyAssumptions env = commaSep (map pretty (Set.toList $ env ^. assumptions))
prettyBindings env = commaSep (map pretty (Map.keys $ removeDomain (env ^. constants) (allSymbols env)))
-- prettyBindings env = hMapDoc pretty pretty (removeDomain (env ^. constants) (allSymbols env))
-- prettyBindings env = empty

instance Pretty Environment where
  pretty env = prettyBindings env <+> prettyAssumptions env
  
prettySortConstraint :: SortConstraint -> Doc
prettySortConstraint (SameSort sl sr) = pretty sl <+> text "=" <+> pretty sr
prettySortConstraint (IsOrd s) = text "Ord" <+> pretty s

instance Pretty SortConstraint where
  pretty = prettySortConstraint

instance Show SortConstraint where
  show = show . pretty

prettyConstraint :: Constraint -> Doc
prettyConstraint (Subtype env t1 t2 False label) = pretty env <+> operator "|-" <+> pretty t1 <+> operator "<:" <+> pretty t2 <+> parens (text label)
prettyConstraint (Subtype env t1 t2 True label) = pretty env <+> operator "|-" <+> pretty t1 <+> operator "/\\" <+> pretty t2 <+> parens (text label)
prettyConstraint (WellFormed env t) = prettyBindings env <+> operator "|-" <+> pretty t
prettyConstraint (WellFormedCond env c) = prettyBindings env <+> operator "|-" <+> pretty c
prettyConstraint (WellFormedMatchCond env c) = prettyBindings env <+> operator "|- (match)" <+> pretty c
prettyConstraint (WellFormedPredicate _ sorts p) = operator "|-" <+> pretty p <+> operator "::" <+> hsep (map (\s -> pretty s <+> operator "->") sorts) <+> pretty BoolS

instance Pretty Constraint where
  pretty = prettyConstraint

instance Show Constraint where
  show = show . pretty

instance Pretty Candidate where
  pretty (Candidate sol valids invalids label) = text label <> text ":" <+> pretty sol <+> parens (pretty (Set.size valids) <+> pretty (Set.size invalids))

instance Show Candidate where
  show = show . pretty
  
instance Pretty Goal where
  pretty (Goal name env spec impl depth _) = pretty env <+> operator "|-" <+> text name <+> operator "::" <+> pretty spec $+$ text name <+> operator "=" <+> pretty impl $+$ parens (text "depth:" <+> pretty depth)

instance Show Goal where
  show = show. pretty
  
prettySpec g@(Goal name _ _ _ _ _) = text name <+> operator "::" <+> pretty (unresolvedSpec g)
prettySolution (Goal name _ _ _ _ _) prog = text name <+> operator "=" </> pretty prog

{- Input language -}

instance Pretty ConstructorSig where
  pretty (ConstructorSig name t) = text name <+> text "::" <+> pretty t
  
prettyVarianceParam (predSig, contra) = pretty predSig <> (if contra then pretty Not else empty)  

instance Pretty BareDeclaration where
  pretty (TypeDecl name tvs t) = keyword "type" <+> text name <+> hsep (map text tvs) <+> operator "=" <+> pretty t
  pretty (QualifierDecl fmls) = keyword "qualifier" <+> hlBraces (commaSep $ map pretty fmls)
  pretty (FuncDecl name t) = text name <+> operator "::" <+> pretty t
  pretty (DataDecl name tParams pParams ctors) = hang tab $ 
    keyword "data" <+> text name <+> hsep (map text tParams) <+> hsep (map prettyVarianceParam pParams) <+> keyword "where" 
    $+$ vsep (map pretty ctors)
  pretty (MeasureDecl name inSort outSort post cases isTermination) = hang tab $ 
    if isTermination then keyword "termination" else empty
    <+> keyword "measure" <+> text name <+> operator "::" <+> pretty inSort <+> operator "->"
    <+> if post == ftrue then pretty outSort else hlBraces (pretty outSort <+> operator "|" <+> pretty post) <+> keyword "where"
    $+$ vsep (map pretty cases)                                                        
  pretty (SynthesisGoal name impl) = text name <+> operator "=" <+> pretty impl
  pretty (MutualDecl names) = keyword "mutual" <+> commaSep (map text names)
  pretty (InlineDecl name args body) = keyword "inline" <+> text name <+> hsep (map text args) <+> operator "=" <+> pretty body
  
instance Pretty a => Pretty (Pos a) where
  pretty (Pos _ x) = pretty x
  
prettyError (ErrorMessage ParseError pos descr) = align $ hang tab $ 
  errorDoc (hcat $ map (<> colon) [text (sourceName pos), pretty (sourceLine pos), pretty (sourceColumn pos), text " Parse Error"]) $+$
  pretty descr    
prettyError (ErrorMessage ResolutionError pos descr) = hang tab $ 
  errorDoc (hcat $ map (<> colon) [text (sourceName pos), pretty (sourceLine pos), text " Resolution Error"]) $+$
  pretty descr  
prettyError (ErrorMessage TypeError pos descr) = hang tab $ 
  errorDoc (hcat $ map (<> colon) [text (sourceName pos), pretty (sourceLine pos), text " Error"]) $+$
  pretty descr
    
instance Pretty ErrorMessage where
  pretty = prettyError
  
instance Show ErrorMessage where
  show = show . pretty

{- AST node counting -}

-- | 'fmlNodeCount' @fml@ : size of @fml@ (in AST nodes)
fmlNodeCount :: Formula -> Int
fmlNodeCount (SetLit _ args) = 1 + sum (map fmlNodeCount args)
fmlNodeCount (SetComp _ e) = 1 + fmlNodeCount e
fmlNodeCount (Unary _ e) = 1 + fmlNodeCount e
fmlNodeCount (Binary _ l r) = 1 + fmlNodeCount l + fmlNodeCount r
fmlNodeCount (Ite c l r) = 1 + fmlNodeCount c + fmlNodeCount l + fmlNodeCount r
fmlNodeCount (Pred _ _ args) = 1 + sum (map fmlNodeCount args)
fmlNodeCount (Cons _ _ args) = 1 + sum (map fmlNodeCount args)
fmlNodeCount (All _ e) = 1 + fmlNodeCount e
fmlNodeCount _ = 1

fmlNodeCount' :: Formula -> Int
fmlNodeCount' (BoolLit _) = 0
fmlNodeCount' f = fmlNodeCount f

-- | 'typeNodeCount' @t@ : cumulative size of all refinements in @t@
typeNodeCount :: RType -> Int
typeNodeCount (ScalarT (DatatypeT _ tArgs pArgs) fml) = fmlNodeCount' fml + sum (map typeNodeCount tArgs) + sum (map fmlNodeCount' pArgs)
typeNodeCount (ScalarT _ fml) = fmlNodeCount' fml
typeNodeCount (FunctionT _ tArg tRes) = typeNodeCount tArg + typeNodeCount tRes

-- | 'programNodeCount' @p@ : size of @p@ (in AST nodes)
programNodeCount :: RProgram -> Int
programNodeCount (Program p _) = case p of
  PSymbol _ -> 1
  PApp e1 e2 -> 1 + programNodeCount e1 + programNodeCount e2
  PFun _ e -> 1 + programNodeCount e
  PIf c e1 e2 -> 1 + programNodeCount c + programNodeCount e1 + programNodeCount e2
  PMatch e cases -> 1 + programNodeCount e + sum (map (\(Case _ _ e) -> programNodeCount e) cases)
  PFix _ e -> programNodeCount e
  PLet x e e' -> 1 + programNodeCount e + programNodeCount e'
  PHole -> 0
  PErr -> 1

-- | Prints data in a table, with fixed column widths.
-- Positive widths for left justification, negative for right.
mkTable :: [Int] -> [[Doc]] -> Doc
mkTable widths docs = vsep $ map (mkTableRow widths) docs
mkTableRow widths docs = hsep $ zipWith signedFill widths docs

signedFill w doc | w < 0 = lfill (-w) doc
                 | otherwise = fill w doc

mkTableLaTeX :: [Int] -> [[Doc]] -> Doc
mkTableLaTeX widths docs =
  uncurry mkTable $ insertSeps widths docs
 where
  insertSeps widths docs = (intersperse 3 widths ++ [3], 
    map ((++ [nl]) . intersperse tab) docs)
  tab = text " &"     
  nl = text " \\\\"

-- | Really? They didn't think I might want to right-align something?
-- This implementation only works for simple documents with a single string.
-- Implementing the general case seemed not worth it.
lfill :: Int -> Doc -> Doc
lfill w d        = case renderCompact d of
  SText l s _ -> spaces (w - l) <> d
 where
  spaces n | n <= 0    = empty
           | otherwise = text $ replicate n ' '
