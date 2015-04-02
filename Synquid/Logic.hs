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

-- | Formulas of the refinement logic
data Formula =
  BoolLit Bool |                      -- ^ Boolean literal  
  IntLit Integer |                    -- ^ Integer literal
  Var Id |                            -- ^ Input variable (universally quantified first-order variable)
  Parameter Id |                      -- ^ Parameter (existentially quantified first-order variable)
  Unknown Id Id |                     -- ^ Predicate unknown
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

-- | 'paramsOf' @fml@ : set of all parameters of @fml@ 
paramsOf :: Formula -> Set Id
paramsOf (Parameter ident) = Set.singleton ident
paramsOf (Unary _ e) = paramsOf e
paramsOf (Binary _ e1 e2) = paramsOf e1 `Set.union` paramsOf e2
paramsOf _ = Set.empty

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
substitute :: Map Id Formula -> Formula -> Formula
substitute subst fml = case fml of
  Var name -> case Map.lookup name subst of
    Just f -> f
    Nothing -> fml
  Parameter name -> case Map.lookup name subst of
    Just f -> f
    Nothing -> fml
  Unary op fml' -> Unary op (substitute subst fml')
  Binary op fml1 fml2 -> Binary op (substitute subst fml1) (substitute subst fml2)
  otherwise -> fml

substituteV x = substitute (Map.singleton valueVarName (Var x))

unknownName (Unknown _ u) = u 

{- Qualifiers -}

-- | Search space for valuations of a single unknown
data QSpace = QSpace {
    _qualifiers :: [Formula],         -- Qualifiers 
    _maxCount :: Int                  -- Maximum number of qualifiers in a valuation
  }

makeLenses ''QSpace  
  
-- | Mapping from unknowns to their search spaces
type QMap = Map Id QSpace

-- | 'lookupQuals' @quals g u@: get @g@ component of the search space for unknown @u@ in @quals@
lookupQuals :: QMap -> Getter QSpace a -> Formula -> a
lookupQuals quals g (Unknown _ u) = case Map.lookup u quals of
  Just qs -> view g qs
  Nothing -> error $ "lookupQuals: missing qualifiers for unknown " ++ u
  
lookupQualsSubst :: QMap -> Formula -> [Formula]
lookupQualsSubst quals u@(Unknown x _) = concatMap go $ lookupQuals quals (to (over qualifiers (map (substituteV x))) . qualifiers) u
  where
    go u@(Unknown _ _) = lookupQualsSubst quals u
    go fml = [fml]
  
  
{- Solutions -}  

-- | Valuation of a predicate unknown as a set of qualifiers
type Valuation = Set Formula

-- | 'isStrongerThan' @v1 v2@ : is @v1@ syntactically stronger than @v2@?
isStrongerThan :: Valuation -> Valuation -> Bool
isStrongerThan = flip Set.isSubsetOf

-- | Mapping from predicate unknowns to their valuations
type Solution = Map Id Valuation
  
-- | Mapping from first-order variables to their valuations
type SMTModel = Map Id Integer  

-- | 'trivialModel' @vars@ : model where domain is @vars@ and range is immaterial
trivialModel vars = constMap vars 0

-- | 'substituteModel' @model fml@: substitute solutions from @model@ for all first-order variables in @fml@
substituteModel :: SMTModel -> Formula -> Formula
substituteModel model = substitute (Map.map IntLit model)

-- | Solution that possibly includes parametrized qualifiers, together with an instantiation of those parameters 
data PSolution = PSolution {
  _solution :: Solution,
  _model :: SMTModel
} deriving Eq

makeLenses ''PSolution

-- | 'parametrize' @sol@ : convert from simple to parametrized solution (with an empty parameter model)
parametrize :: Solution -> PSolution
parametrize sol = PSolution sol Map.empty

-- | 'instantiate' @psol@: convert form parametrized to simple solution (substitute parameter values)
instantiate :: PSolution -> Solution
instantiate psol = Map.map (Set.map (substituteModel $ psol ^. model)) (psol ^. solution)
  
-- | 'topSolution' @qmap@ : top of the solution lattice (maps every unknown in the domain of @qmap@ to the empty set of qualifiers
topSolution :: QMap -> PSolution
topSolution quals = parametrize $ constMap (Map.keysSet quals) Set.empty

-- | 'pValuation' @sol u@ : valuation of @u@ in @sol@ (parameters uninstantiated)
pValuation :: PSolution -> Formula -> Valuation
pValuation sol (Unknown x u) = case Map.lookup u (sol ^. solution) of
  Just quals -> Set.map (substituteV x) quals
  Nothing -> error $ "valuation: no value for unknown " ++ u
  
-- | 'instValuation' @sol u@ : valuation of @u@ in @sol@ (parameters instantiated)  
instValuation :: PSolution -> Formula -> Valuation
instValuation sol u = Set.map (substituteModel $ sol ^. model) $ pValuation sol u

-- | 'pValuation' @sol u@ : valuation of @u@ in @sol@
valuation :: Solution -> Formula -> Valuation
valuation sol = pValuation (parametrize sol)

-- | 'applySolution' @sol fml@ : Substitute solutions from sol for all predicate variables in e
applySolution :: PSolution -> Formula -> Formula   
applySolution psol fml = go fml
  where
    sol = instantiate psol
    go fml = case fml of
      Unknown x ident -> case Map.lookup ident sol of
        Just quals -> substituteV x $ conjunction quals
        Nothing -> fml
      Unary op fml' -> Unary op (go fml')
      Binary op fml1 fml2 -> Binary op (go fml1) (go fml2)
      otherwise -> fml
      
-- | 'merge' @sol sol'@ : element-wise conjunction of @sol@ and @sol'@ (with disjoint parameters)
merge :: PSolution -> PSolution -> PSolution      
merge sol sol' = PSolution (Map.unionWith Set.union (sol ^. solution) (sol' ^. solution)) (Map.union (sol ^. model) (sol' ^. model))
