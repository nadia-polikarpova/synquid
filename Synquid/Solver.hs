-- | Solver for second-order constraints
module Synquid.Solver where

import Synquid.Logic
import Synquid.Z3
import Synquid.Util

import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Debug.Trace

-- | optimalSolutions fml quals: all optimal solutions for a second-order constraint fml over the qualifiers in quals;
-- in fml each unknown must occur only once.
optimalSolutions :: Formula -> QMap -> [Solution]
optimalSolutions fml quals = let (poss, negs) = mapBoth Set.toList $ posNegUnknowns fml
  in do
    qs <- mapM lookup' poss
    let s = Map.fromList $ zip poss qs    
    t <- optimalNegativeSolutions (substitute s fml) negs
    return $ s `Map.union` t
  where
    -- | optimalNegativeSolutions fml negs: all optimal solutions for fml with negative unknowns negs and no positive unknowns
    optimalNegativeSolutions :: Formula -> [Id] -> [Solution]
    optimalNegativeSolutions fml' [] = if isValid fml'
      then [Map.empty]
      else []
    optimalNegativeSolutions fml' [neg] = let ts = lookup' neg in
      map (solutionFromIndexes neg) $ filterSubsets (\idxs -> isValid $ substitute (solutionFromIndexes neg idxs) fml') (length ts)
    optimalNegativeSolutions fml' negs = error $ "optimalNegativeSolutions for " ++ show (length negs) ++ " unknowns not implemented"
    
    lookup' ident = case Map.lookup ident quals of
      Just q -> q
      Nothing -> error $ "optimalSolutions: missing qualifiers for unknown " ++ ident
    
    -- | A solution that maps var to the conjunction of its qualifiers with given indexes
    solutionFromIndexes :: Id -> Set Int -> Solution
    solutionFromIndexes var idxs = let ts = lookup' var in 
      Map.singleton var $ conjunction (map (ts !!) (Set.toList idxs))
      
    isValid fml' = case solveSMTConstraints [fnot fml'] of
      Unsat -> True
      Sat -> False    

-- | filterSubsets check n: all minimal subsets of indexes from [0..n) that satisfy check,
-- where check is monotone (is a set satisfies check, then every superset also satisfies check).
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
    
  