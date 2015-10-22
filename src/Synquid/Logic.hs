{-# LANGUAGE TemplateHaskell, Rank2Types #-}

-- | Formulas of the refinement logic
module Synquid.Logic where

import Synquid.Util

import Data.Tuple
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Lens hiding (both)
import Control.Monad

-- | Identifiers
type Id = String

-- | Sorts
data Sort = BoolS | IntS | UninterpretedS Id | UnknownS | SetS Sort
  deriving (Eq, Ord)
  
isSetS (SetS _) = True
isSetS _ = False

{- Formulas of the refinement logic -}

-- | Unary operators
data UnOp = Neg | Not
  deriving (Eq, Ord)

-- | Binary operators  
data BinOp = 
    Times | Plus | Minus |          -- ^ Int -> Int -> Int     
    Eq | Neq |                      -- ^ a -> a -> Bool
    Lt | Le | Gt | Ge |             -- ^ Int -> Int -> Bool
    And | Or | Implies | Iff |      -- ^ Bool -> Bool -> Bool
    Union | Intersect | Diff |      -- ^ Set -> Set -> Set
    Member | Subset                 -- ^ Int/Set -> Set -> Bool
  deriving (Eq, Ord)
  
-- | Variable substitution  
type Substitution = Map Id Formula

-- | 'inverse' @s@ : inverse of substitution @s@, provided that the range of @s@ only contains variables
inverse :: Substitution -> Substitution
inverse s = Map.fromList [(y, Var b x) | (x, Var b y) <- Map.toList s]

-- | Formulas of the refinement logic
data Formula =
  BoolLit Bool |                      -- ^ Boolean literal  
  IntLit Integer |                    -- ^ Integer literal
  SetLit Sort [Formula] |             -- ^ Set literal
  Var Sort Id |                       -- ^ Input variable (universally quantified first-order variable)
  Unknown Substitution Id |           -- ^ Predicate unknown (with a pending substitution)
  Unary UnOp Formula |                -- ^ Unary expression  
  Binary BinOp Formula Formula |      -- ^ Binary expression
  Measure Sort Id Formula             -- ^ Measure application
  deriving (Eq, Ord)
  
valueVarName = "_v"
unknownName (Unknown _ name) = name
varName (Var _ name) = name
varType (Var t _) = t
  
ftrue = BoolLit True
ffalse = BoolLit False
boolVar = Var BoolS
valBool = boolVar valueVarName
intVar = Var IntS
valInt = intVar valueVarName
vartVar n = Var (UninterpretedS n)
valVart n = vartVar n valueVarName
fneg = Unary Neg
fnot = Unary Not
(|*|) = Binary Times
(|+|) = Binary Plus
(|-|) = Binary Minus
(|=|) = Binary Eq
(|/=|) = Binary Neq
(|<|) = Binary Lt
(|<=|) = Binary Le
(|>|) = Binary Gt
(|>=|) = Binary Ge
(|&|) = Binary And
(|||) = Binary Or
(|=>|) = Binary Implies
(|<=>|) = Binary Iff

andClean l r = if l == ftrue then r else (if r == ftrue then l else l |&| r)    
orClean l r = if l == ffalse then r else (if r == ffalse then l else l ||| r)    
conjunction fmls = foldr andClean ftrue (Set.toList fmls)
disjunction fmls = foldr orClean ffalse (Set.toList fmls)

(/+/) = Binary Union
(/*/) = Binary Intersect
(/-/) = Binary Diff
fin = Binary Member
(/<=/) = Binary Subset

infixl 9 |*|
infixl 8 |+|, |-|, /+/, /-/, /*/
infixl 7 |=|, |/=|, |<|, |<=|, |>|, |>=|, /<=/
infixl 6 |&|, |||
infixr 5 |=>|
infix 4 |<=>|
  
-- | 'varsOf' @fml@ : set of all input variables of @fml@
varsOf :: Formula -> Set Formula
varsOf (SetLit _ elems) = Set.unions $ map varsOf elems
varsOf v@(Var _ _) = Set.singleton v
varsOf (Unary _ e) = varsOf e
varsOf (Binary _ e1 e2) = varsOf e1 `Set.union` varsOf e2
varsOf (Measure _ _ e) = varsOf e
varsOf _ = Set.empty

-- | 'unknownsOf' @fml@ : set of all predicate unknowns of @fml@
unknownsOf :: Formula -> Set Formula
unknownsOf u@(Unknown _ _) = Set.singleton u
unknownsOf (Unary Not e) = unknownsOf e
unknownsOf (Binary _ e1 e2) = Set.union (unknownsOf e1) (unknownsOf e2 )
unknownsOf _ = Set.empty

-- | 'posNegUnknowns' @fml@: sets of positive and negative predicate unknowns in @fml@
posNegUnknowns :: Formula -> (Set Id, Set Id)
posNegUnknowns (Unknown _ u) = (Set.singleton u, Set.empty)
posNegUnknowns (Unary Not e) = swap $ posNegUnknowns e
posNegUnknowns (Binary Implies e1 e2) = both2 Set.union (swap $ posNegUnknowns e1) (posNegUnknowns e2)
posNegUnknowns (Binary Iff e1 e2) = both2 Set.union (posNegUnknowns $ Binary Implies e1 e2) (posNegUnknowns $ Binary Implies e2 e1)
posNegUnknowns (Binary _ e1 e2) = both2 Set.union (posNegUnknowns e1) (posNegUnknowns e2)
posNegUnknowns _ = (Set.empty, Set.empty)

posUnknowns = fst . posNegUnknowns
negUnknowns = snd . posNegUnknowns

-- | 'leftHandSide' @fml@ : left-hand side of a binary expression
leftHandSide (Binary _ l _) = l
-- | 'rightHandSide' @fml@ : right-hand side of a binary expression
rightHandSide (Binary _ _ r) = r

conjunctsOf (Binary And l r) = conjunctsOf l `Set.union` conjunctsOf r
conjunctsOf f = Set.singleton f

-- | Base type of a term in the refinement logic
sortOf :: Formula -> Maybe Sort
sortOf (BoolLit _)                            = Just BoolS
sortOf (IntLit _)                             = Just IntS
sortOf (SetLit b es)                          = mapM_ (\e -> sortOf e >>= guard . (== b)) es >> return (SetS b)  
sortOf (Var s _ )                             = Just s
sortOf (Unknown _ _)                          = Just BoolS
sortOf (Unary op e)
  | op == Neg                                 = (sortOf e >>= guard . (== IntS)) >> return IntS
  | otherwise                                 = (sortOf e >>= guard . (== BoolS)) >> return BoolS
sortOf (Binary op e1 e2)
  | op == Times || op == Plus || op == Minus            = do l <- sortOf e1; guard (l == IntS); r <- sortOf e2; guard (r == IntS); return IntS
  | op == Eq  || op == Neq                              = do l <- sortOf e1; r <- sortOf e2; guard (l == r); return BoolS
  -- | op == Lt || op == Le || op == Gt || op == Ge        = do l <- sortOf e1; guard (l == IntS); r <- sortOf e2; guard (r == IntS); return BoolS
  | op == Lt || op == Le || op == Gt || op == Ge        = do l <- sortOf e1; r <- sortOf e2; guard (l == r); return BoolS -- make comparisons generic
  | op == And || op == Or || op == Implies || op == Iff = do l <- sortOf e1; guard (l == BoolS); r <- sortOf e2; guard (r == BoolS); return BoolS
  | op == Union || op == Intersect || op == Diff        = do l <- sortOf e1; guard (isSetS l); r <- sortOf e2; guard (r == l); return l
  | op == Member                                        = do l <- sortOf e1; r <- sortOf e2; guard (r == SetS l); return BoolS 
  | op == Subset                                        = do l <- sortOf e1; guard (isSetS l); r <- sortOf e2; guard (r == l); return BoolS
sortOf (Measure s _ _)                    = Just $ s
  
-- | 'substitute' @subst fml@: Replace first-order variables in @fml@ according to @subst@
substitute :: Substitution -> Formula -> Formula
substitute subst fml = case fml of
  SetLit b elems -> SetLit b $ map (substitute subst) elems
  Var _ name -> case Map.lookup name subst of
    Just f -> f
    Nothing -> fml
  Unknown s name -> Unknown (s `compose` subst) name 
  Unary op fml' -> Unary op (substitute subst fml')
  Binary op fml1 fml2 -> Binary op (substitute subst fml1) (substitute subst fml2)
  Measure b name arg -> Measure b name (substitute subst arg)
  otherwise -> fml
  where
    compose old new = if Map.null old
      then new
      else if Map.null new
        then old
        else  let ((x, Var b y), old') = Map.deleteFindMin old
              in case Map.lookup y new of
                Nothing -> Map.insert x (Var b y) $ compose old' new
                Just (Var b' v) -> if b == b' 
                  then Map.insert x (Var b v) $ compose old' (Map.delete y new)
                  else error "Base type mismatch when composing pending substitutions"
                  
extractPrimitiveConst v@(Var IntS name) = case reads name of
  [] -> v
  (i, _):_ -> IntLit i
extractPrimitiveConst v = v                    
                  
{- Qualifiers -}

-- | Search space for valuations of a single unknown
data QSpace = QSpace {
    _qualifiers :: [Formula],         -- ^ Qualifiers 
    _maxCount :: Int                  -- ^ Maximum number of qualifiers in a valuation
  }

makeLenses ''QSpace  

emptyQSpace = QSpace [] 0
  
-- | Mapping from unknowns to their search spaces
type QMap = Map Id QSpace

-- | 'lookupQuals' @quals g u@: get @g@ component of the search space for unknown @u@ in @quals@
lookupQuals :: QMap -> Getter QSpace a -> Formula -> a
lookupQuals quals g (Unknown _ u) = case Map.lookup u quals of
  Just qs -> view g qs
  Nothing -> error $ unwords ["lookupQuals: missing qualifiers for unknown", u]
  
lookupQualsSubst :: QMap -> Formula -> [Formula]
lookupQualsSubst quals u@(Unknown s _) = concatMap go $ lookupQuals quals (to (over qualifiers (map (substitute s))) . qualifiers) u
  where
    go u@(Unknown _ _) = lookupQualsSubst quals u
    go fml = [fml]
  
  
{- Solutions -}  

-- | Valuation of a predicate unknown as a set of qualifiers
type Valuation = Set Formula

-- | Mapping from predicate unknowns to their valuations
type Solution = Map Id Valuation
  
-- | 'topSolution' @qmap@ : top of the solution lattice (maps every unknown in the domain of @qmap@ to the empty set of qualifiers)
topSolution :: QMap -> Solution
topSolution quals = constMap (Map.keysSet quals) Set.empty

-- | 'valuation' @sol u@ : valuation of @u@ in @sol@
valuation :: Solution -> Formula -> Valuation
valuation sol (Unknown s u) = case Map.lookup u sol of
  Just quals -> Set.map (substitute s) quals
  Nothing -> error $ unwords ["valuation: no value for unknown", u]

-- | 'applySolution' @sol fml@ : Substitute solutions from sol for all predicate variables in fml
applySolution :: Solution -> Formula -> Formula   
applySolution sol fml = case fml of
  Unknown s ident -> case Map.lookup ident sol of
    Just quals -> substitute s $ conjunction quals
    Nothing -> fml
  Unary op fml' -> Unary op (applySolution sol fml')
  Binary op fml1 fml2 -> Binary op (applySolution sol fml1) (applySolution sol fml2)
  otherwise -> fml
      
-- | 'merge' @sol sol'@ : element-wise conjunction of @sol@ and @sol'@
merge :: Solution -> Solution -> Solution      
merge sol sol' = Map.unionWith Set.union sol sol'

{- Solution Candidates -}

-- | Solution candidate
data Candidate = Candidate {
    solution :: Solution,
    validConstraints :: Set Formula,
    invalidConstraints :: Set Formula,
    label :: String
  } deriving (Eq, Ord)
