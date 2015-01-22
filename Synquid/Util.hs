-- | Helper functions
module Synquid.Util where

import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Applicative

import Debug.Trace

mapBoth f (a, b) = (f a, f b)

-- | 'restrictDomain' @keys m@ : map @m@ restricted on the set of keys @keys@
restrictDomain :: Ord k => Set k -> Map k a -> Map k a
restrictDomain keys m = fst $ partitionDomain keys m

-- | 'removeDomain' @keys m@ : map @m@ with the set of keys @keys@ removed from its domain
removeDomain :: Ord k => Set k -> Map k a -> Map k a
removeDomain keys m = snd $ partitionDomain keys m

-- | 'partitionDomain' @keys m@ : map @m@ partitioned into two maps, restricted to @keys@ and the rest
partitionDomain :: Ord k => Set k -> Map k a -> (Map k a, Map k a)
partitionDomain keys m = Map.partitionWithKey (\k _ -> k `Set.member` keys) m

-- | 'constMap' @keys val@ : map that maps each of @keys@ to @val@
constMap :: Ord k => Set k -> a -> Map k a
constMap keys val = Set.fold (\k m -> Map.insert k val m) Map.empty keys

-- | Analogue of 'concatMap' for sets.
setConcatMap :: (Ord a, Ord b) => (a -> Set b) -> Set a -> Set b
setConcatMap f s = Set.foldr Set.union Set.empty (Set.map f s)

-- | 'subsets' @s@: all subsets of @s@.
subsets :: Ord k => Set k -> Set (Set k)
subsets s = let ss = if Set.null s 
                        then Set.empty
                        else setConcatMap subsets $ Set.map (flip Set.delete s) s
  in Set.insert s ss
        
-- | 'boundedSubsets' @min max s@: all subsets of @s@ of sizes between @min@ and @max@.
boundedSubsets :: Ord k => Int -> Int -> Set k -> Set (Set k)
boundedSubsets min max s = Set.filter (\s -> let n = Set.size s in min <= n && n <= max) (subsets s)
  
-- | Monadic equivalent of 'partition'
partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM f [] = return ([], [])
partitionM f (x:xs) = do
  res <- f x
  (ys, zs) <- partitionM f xs
  return (if res then (x:ys, zs) else (ys, x:zs))
  
-- | Monadic version of 'any'
anyM :: (Functor m, Monad m) => (a -> m Bool) -> [a] -> m Bool
anyM pred xs = isJust <$> findM pred xs
  
-- | Monadic version of 'all'
allM :: (Functor m, Monad m) => (a -> m Bool) -> [a] -> m Bool
allM pred xs = isNothing <$> findM (\x -> not <$> pred x) xs
  
-- | Monadic version of 'find' (finds the first element in a list for which a computation evaluates to True) 
findM :: (Functor m, Monad m) => (a -> m Bool) -> [a] -> m (Maybe a)
findM _ [] = return Nothing
findM pred (x : xs) = do
  res <- pred x
  if res then return (Just x) else findM pred xs  
    
-- | Monadic version of if-then-else  
ifM ::(Functor m, Monad m) => m Bool -> m a -> m a -> m a
ifM cond t e = cond >>= (\res -> if res then t else e)  

-- | Debug output
debug1 s = traceShow s
-- debug1 s = id
debug2 s = traceShow s
-- debug2 s = id
-- debug3 s = traceShow s
debug3 s = id