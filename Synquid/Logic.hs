{-# LANGUAGE TemplateHaskell #-}

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

-- | Unary operators
data UnOp = Neg | Not
  deriving (Eq, Ord)

-- | Binary operators  
data BinOp = Times | Plus | Minus | Eq | Neq | Lt | Le | Gt | Ge | And | Or | Implies | Iff
  deriving (Eq, Ord)

-- | Formulas of the refinement logic
data Formula =
  BoolLit Bool |                      -- ^ Boolean literal  
  IntLit Integer |                    -- ^ Integer literal
  Var Id |                            -- ^ Integer unknown
  Unknown Id |                        -- ^ Predicate unknown
  Unary UnOp Formula |                -- ^ Unary expression  
  Binary BinOp Formula Formula |      -- ^ Binary expression
  Angelic Id                          -- ^ Existentially quantified first-order variable
  deriving (Eq, Ord)
  
ftrue = BoolLit True
ffalse = BoolLit False
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

infixl 9 |*|
infixl 8 |+|, |-|
infixl 7 |=|, |/=|, |<|, |<=|, |>|, |>=|
infixl 6 |&|, |||
infixr 5 |=>|
infix 4 |<=>|

conjunction fmls = if Set.null fmls then ftrue else foldr1 (|&|) (Set.toList fmls)
  
-- | varsOf fml : set of all fist-order variables of fml 
varsOf :: Formula -> Set Id
varsOf (Var ident) = Set.singleton ident
varsOf (Unary _ e) = varsOf e
varsOf (Binary _ e1 e2) = varsOf e1 `Set.union` varsOf e2
varsOf _ = Set.empty

-- | unknownsOf fml : sets of predicate unknowns of fml
unknownsOf :: Formula -> Set Id
unknownsOf (Unknown ident) = Set.singleton ident
unknownsOf (Unary Not e) = unknownsOf e
unknownsOf (Binary _ e1 e2) = Set.union (unknownsOf e1) (unknownsOf e2 )
unknownsOf _ = Set.empty

-- | angelicsOf fml : set of all angelic variables of fml 
angelicsOf :: Formula -> Set Id
angelicsOf (Angelic ident) = Set.singleton ident
angelicsOf (Unary _ e) = angelicsOf e
angelicsOf (Binary _ e1 e2) = angelicsOf e1 `Set.union` angelicsOf e2
angelicsOf _ = Set.empty

leftHandSide (Binary _ l _) = l
rightHandSide (Binary _ _ r) = r

-- | Solution space for a single unknown  
data QSpace = QSpace {
    _qualifiers :: [Formula],
    _maxCount :: Int
  }

makeLenses ''QSpace  
  
type QMap = Map Id QSpace

-- | 'lookupQuals' @quals u@: lookup the search space for unknown @u@ in @quals@
lookupQuals :: QMap -> Id -> QSpace
lookupQuals quals u = case Map.lookup u quals of
  Just qs -> qs
  Nothing -> error $ "lookupQuals: missing qualifiers for unknown " ++ u

-- | Valuation of a predicate unknown as a set of qualifiers
type Valuation = Set Formula

isStrongerThan :: Valuation -> Valuation -> Bool
isStrongerThan = flip Set.isSubsetOf

-- | Valuations for predicate unknowns
type Solution = Map Id Valuation

valuation :: Solution -> Id -> Valuation
valuation sol var = case Map.lookup var sol of
  Just quals -> quals
  Nothing -> error $ "valuation: no value for unknown " ++ var
  
-- | Top of the solution lattice (maps every unknown in unknowns to the empty set of qualifiers)
topSolution :: QMap -> Solution
topSolution quals = constMap (Map.keysSet quals) Set.empty

-- | isSolutionStrongerThan poss negs s1 s2: is s1 stronger (more optimal) than s2 on positive unknowns poss and negative unknowns negs?
isSolutionStrongerThan :: [Id] -> [Id] -> Solution -> Solution -> Bool
isSolutionStrongerThan poss negs s1 s2 = 
  all (\var -> valuation s2 var `isStrongerThan` valuation s1 var) negs && 
  all (\var -> valuation s1 var `isStrongerThan` valuation s2 var) poss

-- | substitute sol e: Substitute solutions from sol for all predicate variables in e
substitute :: Solution -> Formula -> Formula   
substitute sol e = case e of
  Unknown ident -> case Map.lookup ident sol of
    Just quals -> conjunction quals
    Nothing -> e
  Unary op e' -> Unary op (substitute sol e')
  Binary op e1 e2 -> Binary op (substitute sol e1) (substitute sol e2)
  otherwise -> e
  
-- | Valuations for first-order variables
type SMTModel = Map Id Integer  
  
-- | substituteVars sol e: Substitute solutions from sol for all first-order variables in e  
substituteVars :: SMTModel -> Formula -> Formula
substituteVars sol e = case e of
  Var ident -> case Map.lookup ident sol of
    Just i -> IntLit i
    Nothing -> e
  Angelic ident -> case Map.lookup ident sol of
    Just i -> IntLit i
    Nothing -> e
  Unary op e' -> Unary op (substituteVars sol e')
  Binary op e1 e2 -> Binary op (substituteVars sol e1) (substituteVars sol e2)
  otherwise -> e