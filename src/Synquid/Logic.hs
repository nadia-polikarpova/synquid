{-# LANGUAGE TemplateHaskell, Rank2Types #-}

-- | Formulas of the refinement logic
module Synquid.Logic where

import Synquid.Util

import Data.Tuple
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Lens hiding (both)
import Control.Monad

{- Sorts -}

-- | Sorts
data Sort = BoolS | IntS | VarS Id | DataS Id [Sort] | SetS Sort | AnyS
  deriving (Show, Eq, Ord)

isSetS (SetS _) = True
isSetS _ = False
elemSort (SetS s) = s
isData (DataS _ _) = True
isData _ = False
sortArgsOf (DataS _ sArgs) = sArgs
varSortName (VarS name) = name

-- | 'typeVarsOfSort' @s@ : all type variables in @s@
typeVarsOfSort :: Sort -> Set Id
typeVarsOfSort (VarS name) = Set.singleton name
typeVarsOfSort (DataS _ sArgs) = Set.unions (map typeVarsOfSort sArgs)
typeVarsOfSort (SetS s) = typeVarsOfSort s
typeVarsOfSort _ = Set.empty

-- Mapping from type variables to sorts
type SortSubstitution = Map Id Sort

sortSubstitute :: SortSubstitution -> Sort -> Sort
sortSubstitute subst s@(VarS a) = case Map.lookup a subst of
  Just s' -> sortSubstitute subst s'
  Nothing -> s
sortSubstitute subst (DataS name args) = DataS name (map (sortSubstitute subst) args)
sortSubstitute subst (SetS el) = SetS (sortSubstitute subst el)
sortSubstitute _ s = s

distinctTypeVars = map (\i -> "A" ++ show i) [0..]

noncaptureSortSubst :: [Id] -> [Sort] -> Sort -> Sort
noncaptureSortSubst sVars sArgs s =
  let sFresh = sortSubstitute (Map.fromList $ zip sVars (map VarS distinctTypeVars)) s
  in sortSubstitute (Map.fromList $ zip distinctTypeVars sArgs) sFresh

unifySorts :: Set Id -> [Sort] -> [Sort] -> Either (Sort, Sort) SortSubstitution
unifySorts boundTvs = unifySorts' Map.empty
  where
    unifySorts' subst [] []
      = Right subst
    unifySorts' subst (x : xs) (y : ys) | x == y
      = unifySorts' subst xs ys
    unifySorts' subst (SetS x : xs) (SetS y : ys)
      = unifySorts' subst (x:xs) (y:ys)
    unifySorts' subst (DataS name args : xs) (DataS name' args' :ys)
      = if name == name'
          then unifySorts' subst (args ++ xs) (args' ++ ys)
          else Left (DataS name [], DataS name' [])
    unifySorts' subst (AnyS : xs) (_ : ys) = unifySorts' subst xs ys
    unifySorts' subst (_ : xs) (AnyS : ys) = unifySorts' subst xs ys
    unifySorts' subst (VarS x : xs) (y : ys)
      | not (Set.member x boundTvs)
      = case Map.lookup x subst of
            Just s -> unifySorts' subst (s : xs) (y : ys)
            Nothing -> if x `Set.member` typeVarsOfSort y
              then Left (VarS x, y)
              else unifySorts' (Map.insert x y subst) xs ys
    unifySorts' subst (x : xs) (VarS y : ys)
      | not (Set.member y boundTvs)
      = unifySorts' subst (VarS y : ys) (x:xs)
    unifySorts' subst (x: _) (y: _)
      = Left (x, y)

-- | Constraints generated during formula resolution
data SortConstraint = SameSort Sort Sort  -- Two sorts must be the same
  | IsOrd Sort                            -- Sort must have comparisons

-- | Predicate signature: name and argument sorts
data PredSig = PredSig {
  predSigName :: Id,
  predSigArgSorts :: [Sort],
  predSigResSort :: Sort
} deriving (Show, Eq, Ord)

{- Formulas of the refinement logic -}

-- | Unary operators
data UnOp = Neg | Not
  deriving (Show, Eq, Ord)

-- | Binary operators
data BinOp =
    Times | Plus | Minus |          -- ^ Int -> Int -> Int
    Eq | Neq |                      -- ^ a -> a -> Bool
    Lt | Le | Gt | Ge |             -- ^ Int -> Int -> Bool
    And | Or | Implies | Iff |      -- ^ Bool -> Bool -> Bool
    Union | Intersect | Diff |      -- ^ Set -> Set -> Set
    Member | Subset                 -- ^ Int/Set -> Set -> Bool
  deriving (Show, Eq, Ord)

-- | Variable substitution
type Substitution = Map Id Formula

-- | Formulas of the refinement logic
data Formula =
  BoolLit Bool |                      -- ^ Boolean literal
  IntLit Integer |                    -- ^ Integer literal
  SetLit Sort [Formula] |             -- ^ Set literal ([1, 2, 3])
  Var Sort Id |                       -- ^ Input variable (universally quantified first-order variable)
  Unknown Substitution Id |           -- ^ Predicate unknown (with a pending substitution)
  Unary UnOp Formula |                -- ^ Unary expression
  Binary BinOp Formula Formula |      -- ^ Binary expression
  Ite Formula Formula Formula |       -- ^ If-then-else expression
  Pred Sort Id [Formula] |            -- ^ Logic function application
  Cons Sort Id [Formula] |            -- ^ Constructor application
  All Formula Formula                 -- ^ Universal quantification
  deriving (Show, Eq, Ord)

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
setVar s = Var (SetS (VarS s))
valSet s = setVar s valueVarName
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
unknownsOf (Pred _ _ es) = Set.unions $ map unknownsOf es
unknownsOf (Cons _ _ es) = Set.unions $ map unknownsOf es
unknownsOf (All _ e) = unknownsOf e
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

posNegPreds :: Formula -> (Set Id, Set Id)
posNegPreds (Pred BoolS p es) = (Set.singleton p, Set.empty)
posNegPreds (Unary Not e) = swap $ posNegPreds e
posNegPreds (Binary Implies e1 e2) = both2 Set.union (swap $ posNegPreds e1) (posNegPreds e2)
posNegPreds (Binary Iff e1 e2) = both2 Set.union (posNegPreds $ e1 |=>| e2) (posNegPreds $ e2 |=>| e1)
posNegPreds (Binary _ e1 e2) = both2 Set.union (posNegPreds e1) (posNegPreds e2)
posNegPreds (Ite e e1 e2) = both2 Set.union (posNegPreds $ e |=>| e1) (posNegPreds $ fnot e |=>| e2)
posNegPreds _ = (Set.empty, Set.empty)

posPreds = fst . posNegPreds
negPreds = snd . posNegPreds

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
sortOf (SetLit s _)                              = SetS s
sortOf (Var s _ )                                = s
sortOf (Unknown _ _)                             = BoolS
sortOf (Unary op _)
  | op == Neg                                    = IntS
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
  Var s name -> case Map.lookup name subst of
    Just f -> f
    Nothing -> fml
  Unknown s name -> Unknown (s `composeSubstitutions` subst) name
  Unary op e -> Unary op (substitute subst e)
  Binary op e1 e2 -> Binary op (substitute subst e1) (substitute subst e2)
  Ite e0 e1 e2 -> Ite (substitute subst e0) (substitute subst e1) (substitute subst e2)
  Pred b name args -> Pred b name $ map (substitute subst) args
  Cons b name args -> Cons b name $ map (substitute subst) args
  All v@(Var _ x) e -> if x `Map.member` subst
                            then error $ unwords ["Scoped variable clashes with substitution variable", x]
                            else All v (substitute subst e)
  otherwise -> fml

-- | Compose substitutions
composeSubstitutions old new =
  let new' = removeId new
  in Map.map (substitute new') old `Map.union` new'
  where
    -- | Remove identity substitutions
    removeId = Map.filterWithKey (\x fml -> not $ isVar fml && varName fml == x)

deBrujns = map (\i -> dontCare ++ show i) [0..]

sortSubstituteFml :: SortSubstitution -> Formula -> Formula
sortSubstituteFml subst fml = case fml of
  SetLit el es -> SetLit (sortSubstitute subst el) (map (sortSubstituteFml subst) es)
  Var s name -> Var (sortSubstitute subst s) name
  Unknown s name -> Unknown (Map.map (sortSubstituteFml subst) s) name
  Unary op e -> Unary op (sortSubstituteFml subst e)
  Binary op l r -> Binary op (sortSubstituteFml subst l) (sortSubstituteFml subst r)
  Ite c l r -> Ite (sortSubstituteFml subst c) (sortSubstituteFml subst l) (sortSubstituteFml subst r)
  Pred s name es -> Pred (sortSubstitute subst s) name (map (sortSubstituteFml subst) es)
  Cons s name es -> Cons (sortSubstitute subst s) name (map (sortSubstituteFml subst) es)
  All x e -> All (sortSubstituteFml subst x) (sortSubstituteFml subst e)
  _ -> fml

noncaptureSortSubstFml :: [Id] -> [Sort] -> Formula -> Formula
noncaptureSortSubstFml sVars sArgs fml =
  let fmlFresh = sortSubstituteFml (Map.fromList $ zip sVars (map VarS distinctTypeVars)) fml
  in sortSubstituteFml (Map.fromList $ zip distinctTypeVars sArgs) fmlFresh

substitutePredicate :: Substitution -> Formula -> Formula
substitutePredicate pSubst fml = case fml of
  Pred b name args -> case Map.lookup name pSubst of
                      Nothing -> Pred b name (map (substitutePredicate pSubst) args)
                      Just value -> substitute (Map.fromList $ zip deBrujns args) (substitutePredicate pSubst value)
  Unary op e -> Unary op (substitutePredicate pSubst e)
  Binary op e1 e2 -> Binary op (substitutePredicate pSubst e1) (substitutePredicate pSubst e2)
  Ite e0 e1 e2 -> Ite (substitutePredicate pSubst e0) (substitutePredicate pSubst e1) (substitutePredicate pSubst e2)
  All v e -> All v (substitutePredicate pSubst e)
  _ -> fml

-- | Negation normal form of a formula:
-- no negation above boolean connectives, no boolean connectives except @&&@ and @||@
negationNF :: Formula -> Formula
negationNF fml = case fml of
  Unary Not e -> case e of
    Unary Not e' -> negationNF e'
    Binary And e1 e2 -> negationNF (fnot e1) ||| negationNF (fnot e2)
    Binary Or e1 e2 -> negationNF (fnot e1) |&| negationNF (fnot e2)
    Binary Implies e1 e2 -> negationNF e1 |&| negationNF (fnot e2)
    Binary Iff e1 e2 -> (negationNF e1 |&| negationNF (fnot e2)) ||| (negationNF (fnot e1) |&| negationNF e2)
    _ -> fml
  Binary Implies e1 e2 -> negationNF (fnot e1) ||| negationNF e2
  Binary Iff e1 e2 -> (negationNF e1 |&| negationNF e2) ||| (negationNF (fnot e1) |&| negationNF (fnot e2))
  Binary op e1 e2
    | op == And || op == Or -> Binary op (negationNF e1) (negationNF e2)
    | otherwise -> fml
  Ite cond e1 e2 -> (negationNF cond |&| negationNF e1) ||| (negationNF (fnot cond) |&| negationNF e2)
  _ -> fml

-- | Disjunctive normal form for unknowns (known predicates treated as atoms)
uDNF :: Formula -> [Formula]
uDNF = dnf' . negationNF
  where
    dnf' e@(Binary Or e1 e2) = if (Set.null $ unknownsOf e1) && (Set.null $ unknownsOf e2)
                                then return e
                                else dnf' e1 ++ dnf' e2
    dnf' (Binary And e1 e2) = do
                                lClause <- dnf' e1
                                rClause <- dnf' e2
                                return $ lClause |&| rClause
    dnf' fml = [fml]

atomsOf fml = atomsOf' (negationNF fml)
  where
    atomsOf' (Binary And l r) = atomsOf' l `Set.union` atomsOf' r
    -- atomsOf' fml@(Binary Or l r) = Set.insert fml (atomsOf' l `Set.union` atomsOf' r)
    atomsOf' (Binary Or l r) = atomsOf' l `Set.union` atomsOf' r
    atomsOf' fml = Set.singleton fml

splitByPredicate :: Set Id -> Formula -> [Formula] -> Maybe (Map Id (Set Formula))
splitByPredicate preds arg fmls = foldM (\m fml -> checkFml fml m fml) Map.empty fmls
  where
    checkFml _ _ fml | fml == arg   = Nothing
    checkFml whole m fml = case fml of
      Pred _ name args ->
        if name `Set.member` preds && length args == 1 && head args == arg
          then return $ Map.insertWith Set.union name (Set.singleton whole) m
          else foldM (checkFml whole) m args
      SetLit _ args -> foldM (checkFml whole) m args
      Unary _ f -> checkFml whole m f
      Binary _ l r -> foldM (checkFml whole) m [l, r]
      Ite c t e -> foldM (checkFml whole) m [c, t, e]
      Cons _ _ args -> foldM (checkFml whole) m args
      _ -> return m


-- | 'setToPredicate' @x s@: predicate equivalent to @x in s@, which does not contain comprehensions
setToPredicate :: Formula -> Formula -> Formula
setToPredicate x (Binary Union sl sr) = Binary Or (setToPredicate x sl) (setToPredicate x sr)
setToPredicate x (Binary Intersect sl sr) = Binary And (setToPredicate x sl) (setToPredicate x sr)
setToPredicate x (Binary Diff sl sr) = Binary And (setToPredicate x sl) (Unary Not (setToPredicate x sr))
setToPredicate x (Ite c t e) = Ite c (setToPredicate x t) (setToPredicate x e)
setToPredicate x s = Binary Member x s

{- Qualifiers -}

-- | Search space for valuations of a single unknown
data QSpace = QSpace {
    _qualifiers :: [Formula],         -- ^ Qualifiers
    _maxCount :: Int                  -- ^ Maximum number of qualifiers in a valuation
  } deriving (Show, Eq, Ord)

makeLenses ''QSpace

emptyQSpace = QSpace [] 0

toSpace mbN quals = let quals' = nub quals in
  case mbN of
    Nothing -> QSpace quals' (length quals')
    Just n -> QSpace quals' n

-- | Mapping from unknowns to their search spaces
type QMap = Map Id QSpace

-- | 'lookupQuals' @qmap g u@: get @g@ component of the search space for unknown @u@ in @qmap@
lookupQuals :: QMap -> Getter QSpace a -> Formula -> a
lookupQuals qmap g (Unknown _ u) = case Map.lookup u qmap of
  Just qs -> view g qs
  Nothing -> error $ unwords ["lookupQuals: missing qualifiers for unknown", u]

lookupQualsSubst :: QMap -> Formula -> [Formula]
lookupQualsSubst qmap u@(Unknown s _) = concatMap go $ map (substitute s) (lookupQuals qmap qualifiers u)
  where
    go u@(Unknown _ _) = lookupQualsSubst qmap u
    go fml = [fml]

type ExtractAssumptions = Formula -> Set Formula

{- Solutions -}

-- | Valuation of a predicate unknown as a set of qualifiers
type Valuation = Set Formula

-- | Mapping from predicate unknowns to their valuations
type Solution = Map Id Valuation

-- | 'topSolution' @qmap@ : top of the solution lattice (maps every unknown in the domain of @qmap@ to the empty set of qualifiers)
topSolution :: QMap -> Solution
topSolution qmap = constMap (Map.keysSet qmap) Set.empty

-- | 'botSolution' @qmap@ : bottom of the solution lattice (maps every unknown in the domain of @qmap@ to all its qualifiers)
botSolution :: QMap -> Solution
botSolution qmap = Map.map (\(QSpace quals _) -> Set.fromList quals) qmap

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
  All x e -> All x (applySolution sol e)
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
  } deriving (Show)

initialCandidate = Candidate Map.empty Set.empty Set.empty "0"

instance Eq Candidate where
  (==) c1 c2 = Map.filter (not . Set.null) (solution c1) == Map.filter (not . Set.null) (solution c2) &&
               validConstraints c1 == validConstraints c2 &&
               invalidConstraints c1 == invalidConstraints c2

instance Ord Candidate where
  (<=) c1 c2 = Map.filter (not . Set.null) (solution c1) <= Map.filter (not . Set.null) (solution c2) &&
               validConstraints c1 <= validConstraints c2 &&
               invalidConstraints c1 <= invalidConstraints c2
