-- | Formulas of the refinement logic
module Synquid.Logic where

import Synquid.Util

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
  Binary BinOp Formula Formula |      -- ^ Binary expression
  AnyVar                              -- ^ Can be replaces with any variable (only used in qualifiers)
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

conjunction fmls = if Set.null fmls then ftrue else foldr1 (|&|) (Set.toList fmls)

instance Show Formula where
  show (BoolLit b) = show b
  show (IntLit i) = show i
  show (Var ident) = ident
  show (Unknown ident) = "?" ++ ident
  show (Unary op e) = show op ++ "(" ++ show e ++ ") "
  show (Binary op e1 e2) = "(" ++ show e1 ++ ") " ++ show op ++ " (" ++ show e2 ++ ")"
  show (AnyVar) = "*"
  
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

allUnknowns fml = let (poss, negs) = posNegUnknowns fml in poss `Set.union` negs

-- | 'instantiateVars' @idents fml@: instantiate every occurrence of * in @fml@ with all variables from @idents@
instantiateVars :: [Id] -> Formula -> [Formula]
instantiateVars idents AnyVar = map Var idents
instantiateVars idents (Unary op e) = Unary op `fmap` instantiateVars idents e
instantiateVars idents (Binary op e1 e2) = do
  e1' <- instantiateVars idents e1
  e2' <- instantiateVars idents e2
  return $ Binary op e1' e2'
instantiateVars idents fml = [fml]

-- | Valuation of a predicate unknown as a set of qualifiers
type Valuation = Set Formula

isStrongerThan :: Valuation -> Valuation -> Bool
isStrongerThan = flip Set.isSubsetOf

-- | (Candidate) solutions for predicate unknowns
type Solution = Map Id Valuation

valuation :: Solution -> Id -> Valuation
valuation sol var = case Map.lookup var sol of
  Just quals -> quals
  Nothing -> error $ "No value for unknown " ++ var ++ " in solution " ++ show sol
  
-- | Top of the solution lattice (maps every unknown in unknowns to the empty set of qualifiers)
topSolution :: QMap -> Solution
topSolution quals = constMap (Map.keysSet quals) Set.empty

-- | Bottom of the solution lattice (maps every unknown to all its qualifiers) 
botSolution :: QMap -> Solution
botSolution quals = Map.map Set.fromList quals

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
  
type QMap = Map Id [Formula]
  
-- | Results of calls to an SMT solver  
data SMTResult = Sat | Unsat
  deriving Show