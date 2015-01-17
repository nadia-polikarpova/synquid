-- | Solver for second-order constraints
module Synquid.Solver where

import Synquid.Logic
import Synquid.SMTSolver
import Synquid.Util
import Synquid.Pretty

import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Monad
import Control.Applicative
import Control.Lens

import Debug.Trace

-- | 'greatestFixPoint' @quals fmls@: weakest solution for a system of second-order constraints @fmls@ over qualifiers @quals@, if one exists;
-- | @fml@ must have the form "/\ u_i ==> fml'".
greatestFixPoint :: SMTSolver m => QMap -> [Formula] -> m (Maybe Solution)
greatestFixPoint quals fmls = go [topSolution quals]
  where
    unknowns = Map.keysSet quals
    go (sol:sols) = do
        invalidConstraint <- fromJust <$> findM (liftM not . isValid . substitute sol) fmls
        let modifiedConstraint = case invalidConstraint of
                                    Binary Implies lhs rhs -> Binary Implies lhs (substitute sol rhs)
                                    _ -> error $ "greatestFixPoint: encountered ill-formed constraint " ++ show invalidConstraint        
        sols' <- debugOutput (length sols + 1) sol invalidConstraint modifiedConstraint $ strengthen quals modifiedConstraint sol
        validSolution <- findM (\s -> and <$> mapM (isValid . substitute s) (delete invalidConstraint fmls)) sols'
        case validSolution of
          Just s -> return $ Just s -- Solution found
          Nothing -> go $ sols' ++ sols
    debugOutput n sol inv mod = debug $ vsep [text "Candidate count:" <+> pretty n, text "Chosen candidate:" <+> pretty sol, text "Invalid Constraint:" <+> pretty inv, text "Strengthening:" <+> pretty mod]
    
-- | 'strengthen' @quals fml sol@: all minimal strengthenings of @sol@ using qualifiers from @quals@ that make @fml@ valid;
-- | @fml@ must have the form "/\ u_i ==> const".
strengthen :: SMTSolver m => QMap -> Formula -> Solution -> m [Solution]
strengthen quals (Binary Implies lhs rhs) sol = do
    lhsValuations <- optimalValuations (Set.toList $ lhsQuals Set.\\ usedLhsQuals) subst -- all minimal valid valuations of the whole antecedent
    let splitting = Map.filter (not . null) $ Map.fromList $ zip lhsValuations (map splitLhsValuation lhsValuations) -- map of lhsValuations with a non-empty split to their split
    pruned <- pruneValuations $ Map.keys splitting -- semantically optimal lhs valuations
    return $ map merge $ concatMap (splitting Map.!) pruned
  where    
    unknowns = allUnknowns lhs
    unknownsList = Set.toList unknowns
    lookupQuals u = case Map.lookup u quals of                                        -- search space for unknown @u@
      Just qs -> qs
      Nothing -> error $ "strengthen: missing qualifiers for unknown " ++ u
    lhsQuals = setConcatMap (Set.fromList . view qualifiers . lookupQuals) unknowns   -- available qualifiers for the whole antecedent
    usedLhsQuals = setConcatMap (valuation sol) unknowns                              -- already used qualifiers for the whole antecedent
    subst val = let n = Set.size val in if 1 <= n && n <= maxValSize                  -- substitution of @val@ into the constraint, if @val@ is within search space
      then Just $ (conjunction usedLhsQuals |&| conjunction val) |=>| rhs
      else Nothing        
    maxValSize = Set.foldl (\n u -> n + view maxCount (lookupQuals u)) 0 unknowns -   -- upper bound on the size of the lhs valuations
      Set.size usedLhsQuals
    merge sol' = Map.unionWith Set.union sol sol'                                     -- new part of the solution merged with @sol@
    
      -- | All possible additional valuations of @u@ that are subsets of $lhsVal@.
    singleUnknownCandidates lhsVal u = let 
          QSpace qs min max = lookupQuals u
          used = valuation sol u
          n = Set.size used
      in Set.toList $ boundedSubsets (min - n) (max - n) $ (Set.fromList qs Set.\\ used) `Set.intersection` lhsVal
    
      -- | All valid partitions of @lhsVal@ into solutions for multiple unknowns.
    splitLhsValuation :: Valuation -> [Solution]
    splitLhsValuation lhsVal = do
      unknownsVal <- mapM (singleUnknownCandidates lhsVal) unknownsList
      guard $ isPartition unknownsVal lhsVal
      return $ Map.fromList $ zip unknownsList unknownsVal
strengthen _ fml _ = error $ "strengthen: encountered ill-formed constraint " ++ show fml
 
-- | 'optimalValuations' @quals subst@: all smallest subsets of @quals@ that make @subst@ valid.
optimalValuations :: SMTSolver m => [Formula] -> (Valuation -> Maybe Formula) -> m [Valuation]
optimalValuations quals subst = map qualsAt <$> filterSubsets check (length quals)
  where
    qualsAt idxs = Set.map (quals !!) idxs
    check idxs = case subst $ qualsAt idxs of
      Nothing -> return False
      Just fml -> isValid fml    
      
-- | 'pruneValuations' @vals@: eliminate from @vals@ all valuations that are semantically stronger than another valuation @vals@ 
pruneValuations :: SMTSolver m => [Valuation] -> m [Valuation]
pruneValuations [] = return []
pruneValuations (val:vals) = pruneValuations' [] val vals
  where
    pruneValuations' lefts val [] = ifM (isSubsumed val lefts) (return lefts) (return $ val:lefts)
    pruneValuations' lefts val rights@(v:vs) = ifM (isSubsumed val (lefts ++ rights)) (pruneValuations' lefts v vs) (pruneValuations' (lefts ++ [val]) v vs)
    isSubsumed val vals = isJust <$> findM (\v -> isValid $ conjunction val |=>| conjunction v) vals      
        
-- | 'filterSubsets' @check n@: all minimal subsets of indexes from [0..@n@) that satisfy @check@,
-- where @check@ is monotone (is a set satisfies check, then every superset also satisfies @check@);
-- performs breadth-first search.
filterSubsets :: SMTSolver m => (Set Int -> m Bool) -> Int -> m [Set Int]
filterSubsets check n = go [] [Set.empty]
  where
    go solutions candidates = if null candidates 
      then return solutions
      else let new = filter (\s -> not $ any (flip Set.isSubsetOf s) solutions) candidates
        in do
          (valids, invalids) <- partitionM check new 
          go (solutions ++ valids) (concatMap children invalids)      
    children idxs = let lower = if Set.null idxs then 0 else Set.findMax idxs + 1
      in map (flip Set.insert idxs) [lower..(n - 1)]  