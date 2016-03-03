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
data Sort = BoolS | IntS | VarS Id | DataS Id [Sort] | SetS Sort | AnyS
  deriving (Eq, Ord)
  
isSetS (SetS _) = True
isSetS _ = False
isData (DataS _ _) = True
isData _ = False

{- Formulas of the refinement logic -}

-- | Unary operators
data UnOp = Neg | Abs | Not
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
  Ite Formula Formula Formula |       -- ^ If-then-else expression
  Pred Sort Id [Formula] |            -- ^ Logic function application
  Cons Sort Id [Formula] |            -- ^ Constructor application
  All Formula Formula                 -- ^ Universal quantification
  deriving (Eq, Ord)
  
dontCare = "_"  
valueVarName = "_v"
unknownName (Unknown _ name) = name
varName (Var _ name) = name
varType (Var t _) = t

isVar (Var _ _) = True
isVar _ = False
isCons (Cons _ _ _) = True
isCons _ = False
  
ftrue = BoolLit True
ffalse = BoolLit False
boolVar = Var BoolS
valBool = boolVar valueVarName
intVar = Var IntS
valInt = intVar valueVarName
vartVar n = Var (VarS n)
valVart n = vartVar n valueVarName
fneg = Unary Neg
fabs = Unary Abs
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

andClean l r = if l == ftrue then r else (if r == ftrue then l else (if l == ffalse || r == ffalse then ffalse else l |&| r))    
orClean l r = if l == ffalse then r else (if r == ffalse then l else (if l == ftrue || r == ftrue then ftrue else l ||| r))    
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
varsOf (Ite e0 e1 e2) = varsOf e0 `Set.union` varsOf e1 `Set.union` varsOf e2
varsOf (Pred _ _ es) = Set.unions $ map varsOf es
varsOf (Cons _ _ es) = Set.unions $ map varsOf es
varsOf (All x e) = Set.delete x (varsOf e)
varsOf _ = Set.empty

-- | 'unknownsOf' @fml@ : set of all predicate unknowns of @fml@
unknownsOf :: Formula -> Set Formula
unknownsOf u@(Unknown _ _) = Set.singleton u
unknownsOf (Unary Not e) = unknownsOf e
unknownsOf (Binary _ e1 e2) = unknownsOf e1 `Set.union` unknownsOf e2
unknownsOf (Ite e0 e1 e2) = unknownsOf e0 `Set.union` unknownsOf e1 `Set.union` unknownsOf e2
unknownsOf _ = Set.empty

-- | 'posNegUnknowns' @fml@: sets of positive and negative predicate unknowns in @fml@
posNegUnknowns :: Formula -> (Set Id, Set Id)
posNegUnknowns (Unknown _ u) = (Set.singleton u, Set.empty)
posNegUnknowns (Unary Not e) = swap $ posNegUnknowns e
posNegUnknowns (Binary Implies e1 e2) = both2 Set.union (swap $ posNegUnknowns e1) (posNegUnknowns e2)
posNegUnknowns (Binary Iff e1 e2) = both2 Set.union (posNegUnknowns $ e1 |=>| e2) (posNegUnknowns $ e2 |=>| e1)
posNegUnknowns (Binary _ e1 e2) = both2 Set.union (posNegUnknowns e1) (posNegUnknowns e2)
posNegUnknowns (Ite e e1 e2) = both2 Set.union (posNegUnknowns $ e |=>| e1) (posNegUnknowns $ fnot e |=>| e2)
posNegUnknowns _ = (Set.empty, Set.empty)

posUnknowns = fst . posNegUnknowns
negUnknowns = snd . posNegUnknowns

predsOf :: Formula -> Set Id
predsOf (Pred _ p es) = Set.insert p (Set.unions $ map predsOf es)
predsOf (SetLit _ elems) = Set.unions $ map predsOf elems
predsOf (Unary _ e) = predsOf e
predsOf (Binary _ e1 e2) = predsOf e1 `Set.union` predsOf e2
predsOf (Ite e0 e1 e2) = predsOf e0 `Set.union` predsOf e1 `Set.union` predsOf e2
predsOf (All x e) = predsOf e
predsOf _ = Set.empty

-- | 'leftHandSide' @fml@ : left-hand side of a binary expression
leftHandSide (Binary _ l _) = l
-- | 'rightHandSide' @fml@ : right-hand side of a binary expression
rightHandSide (Binary _ _ r) = r

conjunctsOf (Binary And l r) = conjunctsOf l `Set.union` conjunctsOf r
conjunctsOf f = Set.singleton f

-- | Base type of a term in the refinement logic
sortOf :: Formula -> Sort
sortOf (BoolLit _)                               = BoolS
sortOf (IntLit _)                                = IntS
sortOf (SetLit b _)                              = SetS b
sortOf (Var s _ )                                = s
sortOf (Unknown _ _)                             = BoolS
sortOf (Unary op _)
  | op == Neg || op == Abs                       = IntS
  | otherwise                                    = BoolS
sortOf (Binary op e1 _)
  | op == Times || op == Plus || op == Minus     = IntS
  | op == Union || op == Intersect || op == Diff = sortOf e1
  | otherwise                                    = BoolS
sortOf (Ite _ e1 _)                              = sortOf e1
sortOf (Pred s _ _)                              = s
sortOf (Cons s _ _)                              = s
sortOf (All _ _)                                 = BoolS

isExecutable :: Formula -> Bool
isExecutable (SetLit _ _) = False
isExecutable (Unary _ e) = isExecutable e
isExecutable (Binary _ e1 e2) = isExecutable e1 && isExecutable e2
isExecutable (Ite e0 e1 e2) = False
isExecutable (Pred _ _ _) = False
isExecutable (All _ _) = False
isExecutable _ = True
  
-- | 'substitute' @subst fml@: Replace first-order variables in @fml@ according to @subst@
substitute :: Substitution -> Formula -> Formula
substitute subst fml = case fml of
  SetLit b elems -> SetLit b $ map (substitute subst) elems
  Var _ name -> case Map.lookup name subst of
    Just f -> f
    Nothing -> fml
  Unknown s name -> Unknown (s `compose` subst) name 
  Unary op e -> Unary op (substitute subst e)
  Binary op e1 e2 -> Binary op (substitute subst e1) (substitute subst e2)
  Ite e0 e1 e2 -> Ite (substitute subst e0) (substitute subst e1) (substitute subst e2)
  Pred b name args -> Pred b name $ map (substitute subst) args
  Cons b name args -> Cons b name $ map (substitute subst) args  
  All v@(Var _ x) e -> if x `Map.member` subst
                            then error $ unwords ["Scoped variable clashes with substitution variable", x]
                            else All v (substitute subst e)
  otherwise -> fml
  where
    compose old new = if Map.null old
      then new
      else if Map.null new
        then old
        else  case Map.deleteFindMin old of
                ((x, Var b y), old') -> case Map.lookup y new of
                    Nothing -> Map.insert x (Var b y) $ compose old' new
                    Just (Var b' v) -> if b == b' 
                      then Map.insert x (Var b v) $ compose old' (Map.delete y new)
                      else error "Base type mismatch when composing pending substitutions"
                _ -> compose (Map.deleteMin old) new
                  
deBrujns = map (\i -> dontCare ++ show i) [0..] 
                  
substitutePredicate :: Substitution -> Formula -> Formula
substitutePredicate pSubst fml = case fml of
  Pred b name args -> case Map.lookup name pSubst of
                      Nothing -> Pred b name (map (substitutePredicate pSubst) args)
                      Just value -> substitute (Map.fromList $ zip deBrujns args) (substitutePredicate pSubst value)
  Unary op e -> Unary op (substitutePredicate pSubst e)
  Binary op e1 e2 -> Binary op (substitutePredicate pSubst e1) (substitutePredicate pSubst e2)
  Ite e0 e1 e2 -> Ite (substitutePredicate pSubst e0) (substitutePredicate pSubst e1) (substitutePredicate pSubst e2)
  All v@(Var _ x) e -> All v (substitutePredicate pSubst e)
  _ -> fml

{- Qualifiers -}

-- | Search space for valuations of a single unknown
data QSpace = QSpace {
    _qualifiers :: [Formula],         -- ^ Qualifiers 
    _maxCount :: Int                  -- ^ Maximum number of qualifiers in a valuation
  } deriving (Eq, Ord)

makeLenses ''QSpace  

emptyQSpace = QSpace [] 0

toSpace quals = QSpace quals (length quals)
  
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
    
type ExtractAssumptions = Formula -> Set Formula
  
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
  Unary op e -> Unary op (applySolution sol e)
  Binary op e1 e2 -> Binary op (applySolution sol e1) (applySolution sol e2)
  Ite e0 e1 e2 -> Ite (applySolution sol e0) (applySolution sol e1) (applySolution sol e2)
  All x fml' -> All x (applySolution sol fml')
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
  }
  
instance Eq Candidate where
  (==) c1 c2 = Map.filter (not . Set.null) (solution c1) == Map.filter (not . Set.null) (solution c2) &&
               validConstraints c1 == validConstraints c2 &&
               invalidConstraints c1 == invalidConstraints c2 

instance Ord Candidate where
  (<=) c1 c2 = Map.filter (not . Set.null) (solution c1) <= Map.filter (not . Set.null) (solution c2) &&
               validConstraints c1 <= validConstraints c2 &&
               invalidConstraints c1 <= invalidConstraints c2 
               