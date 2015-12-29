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
  -- * Counting
  typeNodeCount,
  programNodeCount
) where

import Synquid.Logic
import Synquid.Program
import Synquid.Tokens
import Synquid.Util

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

instance Pretty Sort where
  pretty IntS = text "Int"
  pretty BoolS = text "Bool"
  pretty (SetS el) = text "Set" <+> pretty el
  pretty (VarS name) = text name
  pretty (DataS name args) = text name <+> hsep (map (parens . pretty) args)
  pretty AnyS = text "?"

instance Show Sort where
  show = show . pretty

instance Pretty UnOp where
  pretty op = text $ unOpTokens Map.! op

instance Show UnOp where
  show = show . pretty

instance Pretty BinOp where
  pretty op = text $ binOpTokens Map.! op

instance Show BinOp where
  show = show . pretty

-- | Binding power of a formula
power :: Formula -> Int
power (Measure _ _ _) = 7
power (Cons _ _ _) = 7
power (Pred _ _) = 7
power (Unary _ _) = 6
power (Binary op _ _)
  | op `elem` [Times, Intersect] = 5
  | op `elem` [Plus, Minus, Union, Diff] = 4
  | op `elem` [Eq, Neq, Lt, Le, Gt, Ge, Member, Subset] = 3
  | op `elem` [And, Or] = 2
  | op `elem` [Implies] = 1
  | op `elem` [Iff] = 0
power (All _ _) = -1
power (Ite _ _ _) = -1  
power _ = 8

-- | Pretty-printed formula
fmlDoc :: Formula -> Doc
fmlDoc fml = fmlDocAt (-2) fml

-- | 'fmlDocAt' @n fml@ : print @expr@ in a context with binding power @n@
fmlDocAt :: Int -> Formula -> Doc
fmlDocAt n fml = condParens (n' <= n) (
  case fml of
    BoolLit b -> pretty b
    IntLit i -> pretty i
    SetLit _ elems -> brackets $ commaSep $ map fmlDoc elems
    Var s name -> text name -- <> text ":" <> pretty  s
    Unknown s name -> if Map.null s then text name else hMapDoc pretty pretty s <> text name
    Unary op e -> pretty op <> fmlDocAt n' e
    Binary op e1 e2 -> fmlDocAt n' e1 <+> pretty op <+> fmlDocAt n' e2
    Ite e0 e1 e2 -> text "if" <+> fmlDoc e0 <+> text "then" <+> fmlDoc e1 <+> text "else" <+> fmlDoc e2
    Measure b name arg -> text name <+> fmlDocAt n' arg -- text name <> text ":" <> pretty  b <+> pretty arg
    Cons b name args -> parens (text name <+> hsep (map (fmlDocAt n') args))
    Pred name args -> text name <+> hsep (map (fmlDocAt n') args)
    All x e -> text "forall" <+> pretty x <+> text "." <+> fmlDoc e
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

instance Show QSpace where
  show = show . pretty

instance Pretty QMap where
  pretty = vMapDoc text pretty

instance Pretty SBaseType where
  pretty IntT = text "Int"
  pretty BoolT = text "Bool"
  pretty (TypeVarT name) = text name -- if Map.null s then text name else hMapDoc pretty pretty s <> text name
  pretty (DatatypeT name tArgs pArgs) = text name <+> hsep (map (parens . pretty) tArgs) <+> hsep (map (angles . pretty) pArgs)

instance Pretty RBaseType where
  pretty IntT = text "Int"
  pretty BoolT = text "Bool"
  pretty (TypeVarT name) = text name -- if Map.null s then text name else hMapDoc pretty pretty s <> text name
  pretty (DatatypeT name tArgs pArgs) = text name <+> hsep (map (parens . pretty) tArgs) <+> hsep (map (angles . pretty) pArgs)

instance Show RBaseType where
  show = show . pretty

prettyCase :: (Pretty t) => Case t -> Doc
prettyCase cas = hang 2 $ text (constructor cas) <+> hsep (map text $ argNames cas) <+> text "->" </> prettyProgram (expr cas)

prettyProgram :: (Pretty t) => Program t -> Doc
prettyProgram (Program p typ) = case p of
    PSymbol s -> text s
    PApp f x -> let
      optParens p = case p of
        Program (PSymbol _) _ -> prettyProgram p
        Program PHole _ -> prettyProgram p
        _ -> parens (prettyProgram p)
      prefix = hang 2 $ prettyProgram f </> optParens x
      in case content f of
          PApp g y -> case content g of
            PSymbol name -> if name `elem` Map.elems binOpTokens
                              then hang 2 $ optParens y </> text name </> optParens x -- Binary operator: use infix notation
                              else prefix
            _ -> prefix
          _ -> prefix
    PFun x e -> nest 2 $ text "\\" <> text x <+> text "." </> prettyProgram e
    PIf c t e -> hang 2 $ text "if" <+> prettyProgram c $+$ (text "then" </> prettyProgram t) $+$ (text "else" </> prettyProgram e)
    PMatch l cases -> hang 2 $ text "match" <+> prettyProgram l <+> text "with" $+$ vsep (map prettyCase cases)
    PFix fs e -> prettyProgram e
    PLet x e e' -> align $ hang 2 (text "let" <+> text x <+> text "=" </> prettyProgram e </> text "in") $+$ prettyProgram e'
    PHole -> if show (pretty typ) == dontCare then text "??" else parens $ text "?? ::" <+> pretty typ

instance (Pretty t) => Pretty (Program t) where
  pretty = prettyProgram

instance (Pretty t) => Show (Program t) where
  show = show . pretty

prettySType :: SType -> Doc
prettySType (ScalarT base _) = pretty base
prettySType (FunctionT _ t1 t2) = parens (pretty t1 <+> text "->" <+> pretty t2)
prettySType AnyT = text "_"

instance Pretty SType where
  pretty = prettySType

instance Show SType where
 show = show . pretty

prettyType :: RType -> Doc
prettyType (ScalarT base (BoolLit True)) = pretty base
prettyType (ScalarT base fml) = braces (pretty base <> text "|" <> pretty fml)
prettyType (FunctionT x t1 t2) = parens (text x <> text ":" <> pretty t1 <+> text "->" <+> pretty t2)
prettyType AnyT = text "_"

instance Pretty RType where
  pretty = prettyType

instance Show RType where
 show = show . pretty

instance Pretty SSchema where
  pretty sch = case sch of
    Monotype t -> pretty t
    ForallT a sch' -> angles (text a) <+> text "." <+> pretty sch'
    ForallP p sorts sch' -> angles (text p <+> text "::" <+> hsep (map (\s -> pretty s <+> text "->") sorts) <+> pretty BoolS) <+> text "." <+> pretty sch'

instance Show SSchema where
 show = show . pretty

instance Pretty RSchema where
  pretty sch = case sch of
    Monotype t -> pretty t
    ForallT a sch' -> angles (text a) <+> text "." <+> pretty sch'
    ForallP p sorts sch' -> angles (text p <+> text "::" <+> hsep (map (\s -> pretty s <+> text "->") sorts) <+> pretty BoolS) <+> text "." <+> pretty sch'

instance Show RSchema where
  show = show . pretty

instance Pretty TypeSubstitution where
  pretty = hMapDoc text pretty

prettyBinding (name, typ) = text name <+> text "::" <+> pretty typ

prettyAssumptions env = commaSep (map pretty (Set.toList $ env ^. assumptions))
prettyBindings env = commaSep (map pretty (Map.keys $ removeDomain (env ^. constants) (allSymbols env)))
-- prettyBindings env = hMapDoc pretty pretty (removeDomain (env ^. constants) (allSymbols env))
-- prettyBindings env = empty
prettyGhosts env = hMapDoc pretty pretty (env ^. ghosts)

instance Pretty Environment where
  pretty env = prettyBindings env <+> prettyGhosts env <+> prettyAssumptions env

prettyConstraint :: Constraint -> Doc
prettyConstraint (Subtype env t1 t2 False) = prettyBindings env <+> prettyAssumptions env <+> text "|-" <+> pretty t1 <+> text "<:" <+> pretty t2
prettyConstraint (Subtype env t1 t2 True) = prettyBindings env <+> prettyAssumptions env <+> text "|-" <+> pretty t1 <+> text "/\\" <+> pretty t2
prettyConstraint (WellFormed env t) = prettyBindings env <+> text "|-" <+> pretty t
prettyConstraint (WellFormedCond env c) = prettyBindings env <+> text "|-" <+> pretty c
prettyConstraint (WellFormedMatchCond env c) = prettyBindings env <+> text "|- (match)" <+> pretty c
prettyConstraint (WellFormedPredicate _ sorts p) = text "|-" <+> pretty p <+> text "::" <+> hsep (map (\s -> pretty s <+> text "->") sorts) <+> pretty BoolS

instance Pretty Constraint where
  pretty = prettyConstraint

instance Show Constraint where
  show = show . pretty

instance Pretty Candidate where
  pretty (Candidate sol valids invalids label) = text label <> text ":" <+> pretty sol <+> parens (pretty (Set.size valids) <+> pretty (Set.size invalids))

instance Show Candidate where
  show = show . pretty

instance Pretty Goal where
  pretty (Goal name env spec impl) = pretty env <+> text "|-" <+> text name <+> text "::" <+> pretty spec $+$ text name <+> text "=" <+> pretty impl

instance Show Goal where
  show = show. pretty

{- Input language -}

instance Pretty ConstructorSig where
  pretty (ConstructorSig name t) = text name <+> text "::" <+> pretty t

instance Pretty PredSig where
  pretty (PredSig p sorts) = angles $ text p <+> text "::" <+> hsep (map (\s -> pretty s <+> text "->") sorts) <+> pretty BoolS
  
instance Pretty MeasureCase where
  pretty (MeasureCase name args body) = text name <+> hsep (map text args) <+> text "->" <+> pretty body

instance Pretty Declaration where
  pretty (TypeDecl name tvs t) = text "type" <+> text name <+> hsep (map text tvs) <+> text "=" <+> pretty t
  pretty (QualifierDecl fmls) = text "qualifier" <+> braces (commaSep $ map pretty fmls)
  pretty (FuncDecl name t) = text name <+> text "::" <+> pretty t
  pretty (DataDecl name typeVars predParams ctors) = hang 2 $ 
    text "data" <+> text name <+> hsep (map text typeVars) <+> hsep (map pretty predParams) <+> text "where" 
    $+$ vsep (map pretty ctors)
  pretty (MeasureDecl name inSort outSort post cases isTermination) = hang 2 $ 
    if isTermination then text "termination" else empty
    <+> text "measure" <+> text name <+> text "::" <+> pretty inSort <+> text "->"
    <+> if post == ftrue then pretty outSort else braces (pretty outSort <+> text "|" <+> pretty post) <+> text "where"
    $+$ vsep (map pretty cases)                                                        
  pretty (SynthesisGoal name impl) = text name <+> text "=" <+> pretty impl

{- AST node counting -}

-- | 'fmlNodeCount' @fml@ : size of @fml@ (in AST nodes)
fmlNodeCount :: Formula -> Int
fmlNodeCount (SetLit _ args) = 1 + sum (map fmlNodeCount args)
fmlNodeCount (Unary _ e) = 1 + fmlNodeCount e
fmlNodeCount (Binary _ l r) = 1 + fmlNodeCount l + fmlNodeCount r
fmlNodeCount (Ite c l r) = 1 + fmlNodeCount c + fmlNodeCount l + fmlNodeCount r
fmlNodeCount (Measure _ _ e) = 1 + fmlNodeCount e
fmlNodeCount (Cons _ _ args) = 1 + sum (map fmlNodeCount args)
fmlNodeCount (Pred _ args) = 1 + sum (map fmlNodeCount args)
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
  PFix _ e -> 1 + programNodeCount e
  PLet x e e' -> 1 + programNodeCount e + programNodeCount e'
  PHole -> 0
