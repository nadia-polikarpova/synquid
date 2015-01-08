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

-- | 'greatestFixPoint' @quals fmls@: weakest solution for a system of second-order constraints @fmls@ over qualifiers @quals@, if one exists;
-- all @fmls@ must be implications.
greatestFixPoint :: QMap -> [Formula] -> Maybe Solution
greatestFixPoint = fixPoint topSolution newConstraint
  where
    newConstraint (Binary Implies lhs rhs) cand = (lhs |=>| substitute cand rhs) |&| (lhs |=>| substitute cand lhs)
    newConstraint fml _ = error $ "greatestFixPoint encountered non-implication constraint " ++ show fml
              
-- | 'leastFixPoint' @quals fmls@: strongest solution for a system of second-order constraints @fmls@ over qualifiers @quals@, if one exists;
-- all @fmls@ must be implications.
leastFixPoint :: QMap -> [Formula] -> Maybe Solution
leastFixPoint = fixPoint botSolution newConstraint
  where
    newConstraint (Binary Implies lhs rhs) cand = (substitute cand lhs |=>| rhs) |&| (substitute cand rhs |=>| rhs)
    newConstraint fml _ = error $ "leastFixPoint encountered non-implication constraint " ++ show fml

fixPoint initSolution newConstraint quals fmls = go [initSolution quals]
  where
    unknowns = Map.keysSet quals 
    go candidates = if null candidates
      then Nothing -- No solution
      else case filter (\c -> all (isValid . (substitute c)) fmls) candidates of        
        sol:_ -> Just sol -- Solution found
        [] -> let
                c:cs = candidates
                invalidConstraint = head $ filter (not . isValid . (substitute c)) fmls                
              in go $ cs ++ [Map.union sol' c | sol' <- optimalSolutions quals (newConstraint invalidConstraint c)]              
    
-- | 'optimalSolutions' @quals fml@: all optimal solutions for a second-order constraint @fml@ over the qualifiers in @quals@;
-- in @fml@ each unknown must occur only once.
optimalSolutions :: QMap -> Formula -> [Solution]
optimalSolutions quals fml = let 
    (poss, negs) = mapBoth Set.toList $ posNegUnknowns fml
    ss = singletonOptimalSolutions poss negs -- optimal solutions where each positive unknown maps to a single qualifier
    rs = nub [makeOptimal poss negs sol ss | sol <- ss] -- merge solutions that match on negative unknowns
  in mergePosAndNeg poss negs ss rs -- merge on both positive and negative
  where
    -- | 'singletonOptimalSolutions' @poss negs@: all optimal solutions for fml in which every positive unknown from poss is mapped to exactly one qualifier
    singletonOptimalSolutions :: [Id] -> [Id] -> [Solution]
    singletonOptimalSolutions poss negs = do
      qs <- mapM lookup' poss
      let s = Map.fromList $ zip poss (map Set.singleton qs)
      t <- optimalNegativeSolutions (substitute s fml) negs
      return $ s `Map.union` t  
  
    -- | 'optimalNegativeSolutions' @fml negs@: all optimal solutions for fml with negative unknowns negs and no positive unknowns
    optimalNegativeSolutions :: Formula -> [Id] -> [Solution]
    optimalNegativeSolutions fml' [] = if isValid fml'
      then [Map.empty]
      else []
    optimalNegativeSolutions fml' [neg] = let ts = lookup' neg in
      map (solutionFromIndexes neg) $ filterSubsets (\idxs -> isValid $ substitute (solutionFromIndexes neg idxs) fml') (length ts)
    optimalNegativeSolutions fml' negs = error $ "optimalNegativeSolutions for " ++ show (length negs) ++ " unknowns not implemented"
    
    -- | 'makeOptimal' @poss negs sol ss@: make @sol@ stronger by merging with other solutions from @ss@ that match on negative variables
    makeOptimal :: [Id] -> [Id] -> Solution -> [Solution] -> Solution
    makeOptimal poss negs sol ss = let 
        ts = [sol' | sol' <- ss, all (\var -> valuation sol var `isStrongerThan` valuation sol' var) negs] -- solutions that are weaker than sol in all negative variables
        update s s' = case merge poss negs s s' ss of
          Nothing -> s
          Just s'' -> s''
      in foldl update sol ts
      
    -- | 'merge' @poss negs s1 s2 ss@: point-wise conjunction of @s1@ and @s2@ if possible
    merge :: [Id] -> [Id] -> Solution -> Solution -> [Solution] -> Maybe Solution
    merge poss negs s1 s2 ss = let
        sol = Map.unionWith Set.union s1 s2 -- Conjunction of s1 and s2
        ts = [sol' | sol' <- ss, all (\var -> valuation sol var `isStrongerThan` valuation sol' var) negs] -- Solutions that are weaker than sol in all negative variables
        conds = do
          qs <- mapM (Set.toList . valuation sol) poss -- For all combinations of qualifiers mapped to positive unknowns in sol
          return $ any (\sol' -> all (\idx -> valuation sol' (poss !! idx) == Set.singleton (qs !! idx)) [0..(length poss - 1)]) ts -- whether there is a solution in ts where all positive unknowns map to just that qualifier 
      in if and conds then Just sol else Nothing
      
    -- | 'mergePosAndNeg' @poss negs ss rs@: add more solutions to @rs@ by merging its members pairwise  
    mergePosAndNeg poss negs ss rs = let
        sols = catMaybes [merge poss negs s1 s2 ss | s1 <- rs, s2 <- rs]
        isStronger = isSolutionStrongerThan poss negs
        isSubsumed s rs' = any (`isStronger` s) rs'        
        add s rs' = if not $ isSubsumed s rs' then makeOptimal poss negs s ss : rs' else rs'
        rsNew = foldr add rs sols
      in if length rsNew == length rs then rs else mergePosAndNeg poss negs ss rsNew
    
    lookup' ident = case Map.lookup ident quals of
      Just q -> q
      Nothing -> error $ "optimalSolutions: missing qualifiers for unknown " ++ ident
    
    -- | A solution that maps var to the qualifiers with given indexes
    solutionFromIndexes :: Id -> Set Int -> Solution
    solutionFromIndexes var idxs = let ts = lookup' var in 
      Map.singleton var $ Set.map (ts !!) idxs
    
-- | Is a formula logically valid? (Calls an SMT solver)
isValid fml = case solveSMTConstraints [fnot fml] of
  Unsat -> True
  Sat -> False    

-- | 'filterSubsets' @check n@: all minimal subsets of indexes from [0..@n@) that satisfy @check@,
-- where @check@ is monotone (is a set satisfies check, then every superset also satisfies @check@).
filterSubsets :: (Set Int -> Bool) -> Int -> [Set Int]
filterSubsets check n = go [] [Set.empty]
  where
    go solutions candidates = if null candidates 
      then solutions
      else let 
          new = filter (\s -> not $ any (flip Set.isSubsetOf s) solutions) candidates
          (valids, invalids) = partition check new 
        in go (solutions ++ valids) (concatMap children invalids)      
    children idxs = let lower = if Set.null idxs then 0 else Set.findMax idxs + 1
      in map (flip Set.insert idxs) [lower..(n - 1)]
    
  