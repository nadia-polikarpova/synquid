{-# LANGUAGE TemplateHaskell, Rank2Types #-}

-- | Formulas of the refinement logic
module Synquid.Logic where

import Synquid.Util

import Data.Tuple
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Lens

-- | Identifiers
type Id = String

{- Formulas of the refinement logic -}

-- | Unary operators
data UnOp = Neg | Not
  deriving (Eq, Ord)

-- | Binary operators  
data BinOp = Times | Plus | Minus | Eq | Neq | Lt | Le | Gt | Ge | And | Or | Implies | Iff
  deriving (Eq, Ord)
  
-- | Variable substitution  
type Substitution = Map Id Formula

-- | 'inverse' @s@ : inverse of substitution @s@, provided that the range of @s@ only contains variables
inverse :: Substitution -> Substitution
inverse s = Map.fromList [(y, Var x) | (x, Var y) <- Map.toList s]

-- | Formulas of the refinement logic
data Formula =
  BoolLit Bool |                      -- ^ Boolean literal  
  IntLit Integer |                    -- ^ Integer literal
  Var Id |                            -- ^ Input variable (universally quantified first-order variable)
  Unknown Substitution Id |           -- ^ Predicate unknown (with a pending substitution)
  Unary UnOp Formula |                -- ^ Unary expression  
  Binary BinOp Formula Formula        -- ^ Binary expression
  deriving (Eq, Ord)
  
valueVarName = "_v"
dontCare = "_"
  
ftrue = BoolLit True
ffalse = BoolLit False
valueVar = Var valueVarName
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
conjunction fmls = if Set.null fmls then ftrue else foldr1 (|&|) (Set.toList fmls)
disjunction fmls = if Set.null fmls then ffalse else foldr1 (|||) (Set.toList fmls)

infixl 9 |*|
infixl 8 |+|, |-|
infixl 7 |=|, |/=|, |<|, |<=|, |>|, |>=|
infixl 6 |&|, |||
infixr 5 |=>|
infix 4 |<=>|
  
-- | 'varsOf' @fml@ : set of all input variables of @fml@
varsOf :: Formula -> Set Id
varsOf (Var ident) = Set.singleton ident
varsOf (Unary _ e) = varsOf e
varsOf (Binary _ e1 e2) = varsOf e1 `Set.union` varsOf e2
varsOf _ = Set.empty

-- | 'unknownsOf' @fml@ : set of all predicate unknowns of @fml@
unknownsOf :: Formula -> Set Formula
unknownsOf u@(Unknown _ _) = Set.singleton u
unknownsOf (Unary Not e) = unknownsOf e
unknownsOf (Binary _ e1 e2) = Set.union (unknownsOf e1) (unknownsOf e2 )
unknownsOf _ = Set.empty

-- | 'leftHandSide' @fml@ : left-hand side of a binary expression
leftHandSide (Binary _ l _) = l
-- | 'rightHandSide' @fml@ : right-hand side of a binary expression
rightHandSide (Binary _ _ r) = r

conjunctsOf (Binary And l r) = conjunctsOf l `Set.union` conjunctsOf r
conjunctsOf f = Set.singleton f

-- | 'substitute' @subst fml@: Replace first-order variables in @fml@ according to @subst@
substitute :: Substitution -> Formula -> Formula
substitute subst fml = case fml of
  Var name -> case Map.lookup name subst of
    Just f -> f
    Nothing -> fml
  Unknown s name -> Unknown (subst `Map.union` s) name 
  Unary op fml' -> Unary op (substitute subst fml')
  Binary op fml1 fml2 -> Binary op (substitute subst fml1) (substitute subst fml2)
  otherwise -> fml

{- Qualifiers -}

-- | Search space for valuations of a single unknown
data QSpace = QSpace {
    _qualifiers :: [Formula],         -- Qualifiers 
    _maxCount :: Int                  -- Maximum number of qualifiers in a valuation
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

-- | 'applySolution' @sol fml@ : Substitute solutions from sol for all predicate variables in e
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

-- | Mapping from first-order variables to their valuations
type SMTModel = Map Id Integer 
