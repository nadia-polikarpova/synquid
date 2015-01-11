-- | Solver for second-order constraints
module Synquid.Solver where

import Synquid.Logic
import Synquid.Z3
import Synquid.Util

import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad

import Debug.Trace

-- | 'greatestFixPoint' @quals fmls@: weakest solution for a system of second-order constraints @fmls@ over qualifiers @quals@, if one exists;
-- | @fml@ must have the form "/\ u_i ==> fml'".
greatestFixPoint :: QMap -> [Formula] -> Maybe Solution
greatestFixPoint quals fmls = go [topSolution quals]
  where
    unknowns = Map.keysSet quals
    go (sol:sols) = traceShow (length sols + 1) $ let
        invalidConstraint = fromJust $ find (not . isValid . (substitute sol)) fmls
        modifiedConstraint = case invalidConstraint of
          Binary Implies lhs rhs -> Binary Implies lhs (substitute sol rhs)
          _ -> error $ "greatestFixPoint: encountered ill-formed constraint " ++ show invalidConstraint
        sols' = strengthen quals modifiedConstraint sol
      in case find (\s -> all (isValid . substitute s) fmls) sols' of
        Just s -> Just s -- Solution found
        Nothing -> go $ sols' ++ sols

-- | 'strengthen' @quals fml sol@: all minimal strengthenings of @sol@ using qualifiers from @quals@ that make @fml@ valid;
-- | @fml@ must have the form "/\ u_i ==> const".
strengthen :: QMap -> Formula -> Solution -> [Solution]
strengthen quals (Binary Implies lhs rhs) sol = let
    lhsQuals = setConcatMap (lookup') unknowns -- available qualifiers for the whole antecedent
    usedLhsQuals = setConcatMap (valuation sol) unknowns -- already used qualifiers for the whole antecedent
    lhsValuations = optimalValuations (Set.toList $ lhsQuals Set.\\ usedLhsQuals) (\val -> (conjunction usedLhsQuals |&| conjunction val) |=>| rhs) -- all minimal valid valuations of the whole antecedent
  in map merge $ concatMap splitLhsValuation lhsValuations
  where    
    unknowns = allUnknowns lhs
    unknownsList = Set.toList unknowns
    lookup' ident = case Map.lookup ident quals of
      Just qs -> Set.fromList qs
      Nothing -> error $ "strengthen: missing qualifiers for unknown " ++ ident
    merge sol' = Map.unionWith Set.union sol sol'
    
      -- | All possible valuations of @u@ that are subsets of $lhsVal@.
    singleUnknownCandidates lhsVal u = Set.toList $ subsets $ lookup' u `Set.intersection` lhsVal
    
      -- | All valid partitions of @lhsVal@ into solutions for multiple unknowns.
    splitLhsValuation :: Valuation -> [Solution]
    splitLhsValuation lhsVal = do
      unknownsVal <- mapM (singleUnknownCandidates lhsVal) unknownsList
      guard $ isPartition unknownsVal lhsVal -- ToDo: more efficient way to generate set partitions?
      return $ Map.fromList $ zip unknownsList unknownsVal
strengthen _ fml _ = error $ "strengthen: encountered ill-formed constraint " ++ show fml
 
-- | 'optimalValuations' @quals subst@: all smallest subsets of @quals@ that make @subst@ valid.
optimalValuations :: [Formula] -> (Valuation -> Formula) -> [Valuation]
optimalValuations quals subst = map qualsAt $ filterSubsets (\idxs -> isValid $ subst $ qualsAt idxs) (length quals)
  where
    qualsAt idxs = Set.map (quals !!) idxs
        
-- | 'filterSubsets' @check n@: all minimal subsets of indexes from [0..@n@) that satisfy @check@,
-- where @check@ is monotone (is a set satisfies check, then every superset also satisfies @check@);
-- performs breadth-first search.
filterSubsets :: (Set Int -> Bool) -> Int -> [Set Int]
filterSubsets check n = go [] [Set.empty] -- ToDo: we don't need the empty set
  where
    go solutions candidates = if null candidates 
      then solutions
      else let
          new = filter (\s -> not $ any (flip Set.isSubsetOf s) solutions) candidates
          (valids, invalids) = partition check new 
        in go (solutions ++ valids) (concatMap children invalids)      
    children idxs = let lower = if Set.null idxs then 0 else Set.findMax idxs + 1
      in map (flip Set.insert idxs) [lower..(n - 1)]

-- | Is a formula logically valid? (Calls an SMT solver)
isValid fml = case solveSMTConstraints [fnot fml] of
  Unsat -> True
  Sat -> False        
  