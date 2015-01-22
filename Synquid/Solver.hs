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
import Control.Monad.Reader
import Control.Applicative
import Control.Lens

-- | 'solveWithParams' @params quals fmls@: 'greatestFixPoint' @quals fmls@ with solver parameters @params@
solveWithParams :: SMTSolver m => SolverParams -> QMap -> [Formula] -> m (Maybe Solution)
solveWithParams params quals fmls = runReaderT go params
  where
    go = do
      quals' <- traverse (traverseOf qualifiers pruneQualifiers) quals -- remove redundant qualifiers
      debug3 (text "Original" $+$ pretty quals $+$ text "Pruned" $+$ pretty quals') $ greatestFixPoint quals' fmls
      
-- | Strategies for picking the next constraint to solve      
data ConstraintPickStrategy = PickFirst | PickSmallestSpace      

-- | Parameters of the fix point algorithm
data SolverParams = SolverParams {
  semanticPrune :: Bool,                            -- ^ After solving each constraints, remove semantically non-optimal solutions
  agressivePrune :: Bool,                           -- ^ Perform pruning on the LHS-valuation of as opposed to per-variable valuations
  overlappingSplits :: Bool,                        -- ^ When splitting an LHS valuation into variable valuations, allow them to share qualifiers
  constraintPickStrategy :: ConstraintPickStrategy  -- ^ How should the next constraint to solve be picked
}
    
type FixPointSolver m a = ReaderT SolverParams m a
  
-- | 'greatestFixPoint' @quals fmls@: weakest solution for a system of second-order constraints @fmls@ over qualifiers @quals@, if one exists;
-- | @fml@ must have the form "/\ u_i ==> fml'".
greatestFixPoint :: SMTSolver m => QMap -> [Formula] -> FixPointSolver m (Maybe Solution)
greatestFixPoint quals fmls = go [topSolution quals]
  where
    unknowns = Map.keysSet quals
    go :: SMTSolver m => [Solution] -> FixPointSolver m (Maybe Solution)
    go (sol:sols) = do
        invalidConstraint <- asks constraintPickStrategy >>= pickConstraint sol        
        let modifiedConstraint = case invalidConstraint of
                                    Binary Implies lhs rhs -> Binary Implies lhs (substitute sol rhs)
                                    _ -> error $ "greatestFixPoint: encountered ill-formed constraint " ++ show invalidConstraint        
        sols' <- debugOutput (sol:sols) sol invalidConstraint modifiedConstraint $ strengthen quals modifiedConstraint sol
        validSolution <- findM (\s -> and <$> mapM (isValidFml . substitute s) (delete invalidConstraint fmls)) sols'
        case validSolution of
          Just s -> return $ Just s -- Solution found
          Nothing -> go $ sols' ++ sols
    go [] = return Nothing
    pickConstraint sol PickFirst = fromJust <$> findM (liftM not . isValidFml . substitute sol) fmls
    pickConstraint sol PickSmallestSpace  = do
      invalids <- filterM (liftM not . isValidFml . substitute sol) fmls
      let spaceSize fml = maxValSize quals sol (unknownsOf fml)
      return $ minimumBy (\x y -> compare (spaceSize x) (spaceSize y)) invalids
    debugOutput sols sol inv mod = debug1 $ vsep [
      nest 2 $ text "Candidates" <+> parens (pretty $ length sols) $+$ (vsep $ map pretty sols), 
      text "Chosen candidate:" <+> pretty sol, 
      text "Invalid Constraint:" <+> pretty inv, 
      text "Strengthening:" <+> pretty mod]
    
-- | 'strengthen' @quals fml sol@: all minimal strengthenings of @sol@ using qualifiers from @quals@ that make @fml@ valid;
-- | @fml@ must have the form "/\ u_i ==> const".
strengthen :: SMTSolver m => QMap -> Formula -> Solution -> FixPointSolver m [Solution]
strengthen quals (Binary Implies lhs rhs) sol = do
    lhsValuations <- optimalValuations (Set.toList $ lhsQuals Set.\\ usedLhsQuals) subst -- all minimal valid valuations of the whole antecedent
    overlap <- asks overlappingSplits
    let splitting = Map.filter (not . null) $ Map.fromList $ zip lhsValuations (map (splitLhsValuation overlap) lhsValuations) -- map of lhsValuations with a non-empty split to their split
    let allSolutions = concat $ Map.elems splitting
    pruned <- ifM (asks semanticPrune) 
      (ifM (asks agressivePrune)
        (concatMap (splitting Map.!) <$> pruneValuations (Map.keys splitting))  -- Prune LHS valuations and then return the splits of only optimal valuations
        (pruneSolutions unknownsList allSolutions))                             -- Prune per-variable
      (return allSolutions) 
    return $ map merge pruned
  where    
    unknowns = unknownsOf lhs
    unknownsList = Set.toList unknowns
    lhsQuals = setConcatMap (Set.fromList . view qualifiers . lookupQuals quals) unknowns   -- available qualifiers for the whole antecedent
    usedLhsQuals = setConcatMap (valuation sol) unknowns                                    -- already used qualifiers for the whole antecedent
    subst val = let n = Set.size val in if 1 <= n && n <= maxValSize quals sol unknowns     -- substitution of @val@ into the constraint, if @val@ is within search space
      then Just $ (conjunction usedLhsQuals |&| conjunction val) |=>| rhs
      else Nothing        
    merge sol' = Map.unionWith Set.union sol sol'                                     -- new part of the solution merged with @sol@
    
      -- | All possible additional valuations of @u@ that are subsets of $lhsVal@.
    singleUnknownCandidates lhsVal u = let 
          QSpace qs min max = lookupQuals quals u
          used = valuation sol u
          n = Set.size used
      in Set.toList $ boundedSubsets (min - n) (max - n) $ (Set.fromList qs Set.\\ used) `Set.intersection` lhsVal
    
      -- | All valid partitions of @lhsVal@ into solutions for multiple unknowns.
    splitLhsValuation :: Bool -> Valuation -> [Solution]
    splitLhsValuation overlap lhsVal = do
      unknownsVal <- mapM (singleUnknownCandidates lhsVal) unknownsList
      let isValidsplit ss s = if overlap
                                then Set.unions ss == s -- If overlapping splits are allowed, only check that the split covers the whole lhsVal
                                else Set.unions ss == s && sum (map Set.size ss) == Set.size s  -- Otherwise, also check that they are disjoint
      guard $ isValidsplit unknownsVal lhsVal
      return $ Map.fromList $ zip unknownsList unknownsVal
          
strengthen _ fml _ = error $ "strengthen: encountered ill-formed constraint " ++ show fml

-- | 'maxValSize' @quals sol unknowns@: Upper bound on the size of valuations of a conjunction of @unknowns@ when strengthening @sol@ 
maxValSize quals sol unknowns = let 
    usedQuals = setConcatMap (valuation sol) unknowns
  in Set.foldl (\n u -> n + view maxCount (lookupQuals quals u)) 0 unknowns - Set.size usedQuals
 
-- | 'optimalValuations' @quals subst@: all smallest subsets of @quals@ that make @subst@ valid.
optimalValuations :: SMTSolver m => [Formula] -> (Valuation -> Maybe Formula) -> FixPointSolver m [Valuation]
optimalValuations quals subst = map qualsAt <$> filterSubsets check (length quals)
  where
    qualsAt idxs = Set.map (quals !!) idxs
    check idxs = case subst $ qualsAt idxs of
      Nothing -> return False
      Just fml -> isValidFml fml    
            
-- | 'pruneSolutions' @sols@: eliminate from @sols@ all solutions that are semantically stronger on all unknowns than another solution in @sols@ 
pruneSolutions :: SMTSolver m => [Id] -> [Solution] -> FixPointSolver m [Solution]
pruneSolutions unknowns = let isSubsumed sol sols = anyM (\s -> allM (\u -> isValidFml $ conjunction (valuation sol u) |=>| conjunction (valuation s u)) unknowns) sols
  in prune isSubsumed
  
-- | 'pruneValuations' @vals@: eliminate from @vals@ all valuations that are semantically stronger than another valuation in @vals@   
pruneValuations :: SMTSolver m => [Valuation] -> FixPointSolver m [Valuation] 
pruneValuations = let isSubsumed val vals = anyM (\v -> isValidFml $ conjunction val |=>| conjunction v) vals
  in prune isSubsumed
  
-- | 'pruneQualifiers' @quals@: eliminate logical duplicates from @quals@
pruneQualifiers :: SMTSolver m => [Formula] -> FixPointSolver m [Formula]   
pruneQualifiers = let isSubsumed qual quals = anyM (\q -> isValidFml $ qual |<=>| q) quals
  in prune isSubsumed
  
prune :: SMTSolver m => (a -> [a] -> FixPointSolver m Bool) -> [a] -> FixPointSolver m [a]
prune isSubsumed [] = return []
prune isSubsumed (x:xs) = prune' [] x xs
  where
    prune' lefts x [] = ifM (isSubsumed x lefts) (return lefts) (return $ x:lefts)
    prune' lefts x rights@(y:ys) = ifM (isSubsumed x (lefts ++ rights)) (prune' lefts y ys) (prune' (lefts ++ [x]) y ys)  
        
-- | 'filterSubsets' @check n@: all minimal subsets of indexes from [0..@n@) that satisfy @check@,
-- where @check@ is monotone (is a set satisfies check, then every superset also satisfies @check@);
-- performs breadth-first search.
filterSubsets :: SMTSolver m => (Set Int -> FixPointSolver m Bool) -> Int -> FixPointSolver m [Set Int]
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
      
-- | 'isValid' lifted to FixPointSolver      
isValidFml :: SMTSolver m => Formula -> FixPointSolver m Bool
isValidFml = lift . isValid      
