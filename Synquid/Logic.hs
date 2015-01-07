-- | Formulas of the refinement logic
module Synquid.Logic where

import Data.Tuple
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

-- | Identifiers
type Id = String

-- | Unary operators
data UnOp = Neg | Not
  deriving (Eq, Ord)

instance Show UnOp where
  show Neg = "-"
  show Not = "!" 

-- | Binary operators  
data BinOp = Plus | Minus | Eq | Neq | Lt | Le | Gt | Ge | And | Or | Implies
  deriving (Eq, Ord)

instance Show BinOp where
  show Plus = "+"
  show Minus = "-"
  show Eq = "=="
  show Neq = "/="
  show Lt = "<"
  show Le = "<="
  show Gt = ">"
  show Ge = ">="
  show And = "&&"
  show Or = "||"
  show Implies = "==>"

-- | Formulas of the refinement logic
data Formula =
  BoolLit Bool |                      -- ^ Boolean literal  
  IntLit Integer |                    -- ^ Integer literal
  Var Id |                            -- ^ Integer unknown
  Unknown Id |                        -- ^ Predicate unknown
  Unary UnOp Formula |                -- ^ Unary expression  
  Binary BinOp Formula Formula        -- ^ Binary expression
  deriving (Eq, Ord)
  
ftrue = BoolLit True
ffalse = BoolLit False
fneg = Unary Neg
fnot = Unary Not
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

conjunction fmls = if null fmls then ftrue else foldr1 (|&|) fmls

instance Show Formula where
  show (BoolLit b) = show b
  show (IntLit i) = show i
  show (Var ident) = ident
  show (Unknown ident) = "?" ++ ident
  show (Unary op e) = show op ++ "(" ++ show e ++ ") "
  show (Binary op e1 e2) = "(" ++ show e1 ++ ") " ++ show op ++ " (" ++ show e2 ++ ")"
  
-- | vars fml : set of all fist-order variables of fml 
vars :: Formula -> Set Id
vars (Var ident) = Set.singleton ident
vars (Unary _ e) = vars e
vars (Binary _ e1 e2) = vars e1 `Set.union` vars e2
vars _ = Set.empty

-- | posNegUnknowns fml : sets of positive and negative predicate unknowns of e
posNegUnknowns :: Formula -> (Set Id, Set Id)
posNegUnknowns (Unknown ident) = (Set.singleton ident, Set.empty)
posNegUnknowns (Unary Not e) = swap $ posNegUnknowns e
posNegUnknowns (Binary And e1 e2) = let 
    (e1pos, e1neg) = posNegUnknowns e1
    (e2pos, e2neg) = posNegUnknowns e2 
  in (Set.union e1pos e2pos, Set.union e1neg e2neg)
posNegUnknowns (Binary Or e1 e2) = let 
    (e1pos, e1neg) = posNegUnknowns e1
    (e2pos, e2neg) = posNegUnknowns e2 
  in (Set.union e1pos e2pos, Set.union e1neg e2neg)
posNegUnknowns (Binary Implies e1 e2) = let 
    (e1pos, e1neg) = posNegUnknowns e1
    (e2pos, e2neg) = posNegUnknowns e2 
  in (Set.union e1neg e2pos, Set.union e1pos e2neg)
posNegUnknowns _ = (Set.empty, Set.empty)

-- | (Candidate) solutions for predicate unknowns
type Solution = Map Id (Set Formula)

valuation :: Solution -> Id -> Set Formula
valuation sol var = case Map.lookup var sol of
  Just quals -> quals
  Nothing -> error $ "No value for unknown " ++ var ++ " in solution " ++ show sol
  
isStrongerThan :: Set Formula -> Set Formula -> Bool
isStrongerThan = flip Set.isSubsetOf

-- | isSolutionStrongerThan poss negs s1 s2: is s1 stronger (more optimal) than s2 on positive unknowns poss and negative unknowns negs?
isSolutionStrongerThan :: [Id] -> [Id] -> Solution -> Solution -> Bool
isSolutionStrongerThan poss negs s1 s2 = 
  all (\var -> valuation s2 var `isStrongerThan` valuation s1 var) negs && 
  all (\var -> valuation s1 var `isStrongerThan` valuation s2 var) poss

-- | substitute sol e: Substitute solutions from sol for all predicate variables in e
substitute :: Solution -> Formula -> Formula   
substitute sol e = case e of
  Unknown ident -> case Map.lookup ident sol of
    Just quals -> conjunction $ Set.toList quals
    Nothing -> e
  Unary op e' -> Unary op (substitute sol e')
  Binary op e1 e2 -> Binary op (substitute sol e1) (substitute sol e2)
  otherwise -> e
  
type QMap = Map Id [Formula]
  
-- | Results of calls to an SMT solver  
data SMTResult = Sat | Unsat
  deriving Show