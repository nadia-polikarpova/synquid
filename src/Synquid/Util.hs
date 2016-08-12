-- | Common types and helper functions
module Synquid.Util where

import Data.Maybe
import Data.Either
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Char

import Control.Applicative
import Control.Monad
import Control.Lens hiding (both)

import Debug.Trace

-- | Identifiers
type Id = String

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z

fromRight (Right x) = x
fromLeft (Left x) = x

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f (Left x) = Left $ f x
mapLeft _ (Right x) = Right x

mapRight :: (a -> b) -> Either c a -> Either c b
mapRight _ (Left x) = Left x
mapRight f (Right x) = Right $ f x

-- | `mappedCompare` @f x y@ : compare @f x@ and @f y@
mappedCompare :: Ord b => (a -> b) -> a -> a -> Ordering
mappedCompare f x y = f x `compare` f y

-- | Map a function on a pair
both :: (a -> b) -> (a, a) -> (b, b)
both f (x1, x2) = (f x1, f x2)

-- | Map a two-argument function on two pairs
both2 :: (a -> b -> c) -> (a, a) -> (b, b) -> (c, c)
both2 f (x1, x2) (y1, y2) = (f x1 y1, f x2 y2)

-- | Map a monadic action on a pair
bothM :: Monad m => (a -> m b) -> (a, a) -> m (b, b)
bothM f (x1, x2) = do
  y1 <- f x1
  y2 <- f x2
  return (y1, y2)
  
setCompare :: Ord a => Set a -> Set a -> Ordering  
setCompare x y = case compare (Set.size x) (Set.size y) of
                  EQ -> compare x y
                  res -> res

-- | 'disjoint' @s1 s2@ : are @s1@ and @s2@ disjoint?
disjoint :: Ord a => Set a -> Set a -> Bool
disjoint s1 s2 = Set.null $ s1 `Set.intersection` s2

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

-- | 'boundedSubsets' @n s@: all subsets of @s@ of sizes no greater than @n@
boundedSubsets :: Ord k => Int -> Set k -> Set (Set k)
boundedSubsets 0 _ = Set.singleton Set.empty
boundedSubsets n s
  | Set.null s = Set.singleton Set.empty
  | otherwise = let (x, xs) = Set.deleteFindMin s in
      Set.map (Set.insert x) (boundedSubsets (n - 1) xs) `Set.union` boundedSubsets n xs -- x is in or x is out
      
-- | Partition a set-valued map into sub-maps where value non-disjoint value sets are grouped together
toDisjointGroups :: (Ord k, Ord v) => Map k (Set v) -> [(Set k, Set v)]
toDisjointGroups m = toDisjointGroups' m []
  where
    toDisjointGroups' :: (Ord k, Ord v) => Map k (Set v) -> [(Set k, Set v)] -> [(Set k, Set v)]
    toDisjointGroups' m acc
      | Map.null m  = acc
      | otherwise   = let ((key, vals), m') = Map.deleteFindMin m in
                      let (keys', vals') = close (Set.singleton key) vals m' in
                      let m'' = removeDomain keys' m' in
                      toDisjointGroups' m'' ((keys', vals'):acc)
         
    close :: (Ord k, Ord v) => Set k -> Set v -> Map k (Set v) -> (Set k, Set v)
    close keys vals m = 
      let (mDisj, mNonDisj) = Map.partition (disjoint vals) m in
      if Map.null mNonDisj
        then (keys, vals)
        else close (keys `Set.union` Map.keysSet mNonDisj) (vals `Set.union` (Set.unions $ Map.elems mNonDisj)) mDisj
    
      
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
  
-- | Monadic version of 'find' (finds the first element in a list for which a computation evaluates to True) 
findJustM :: (Functor m, Monad m) => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
findJustM _ [] = return Nothing
findJustM f (x : xs) = do
  resMb <- f x
  case resMb of
    Nothing -> findJustM f xs
    Just res -> return $ Just res
    
-- | Monadic version of if-then-else  
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM cond t e = cond >>= (\res -> if res then t else e)  

-- | Monadic equivalent of 'Set.partition'
setPartitionM :: (Ord a, Monad m) => (a -> m Bool) -> Set a -> m (Set a, Set a)
setPartitionM f s = both Set.fromList `liftM` partitionM f (Set.toList s)

-- | 'pairGetter' @g1 g2@ : combine two getters into one that gets a pair
pairGetter g1 g2 = to (\x -> (view g1 x, view g2 x))

asInteger :: String -> Maybe Integer
asInteger s = if all isDigit s then Just $ read s else Nothing

{- Debug output -}

-- | 'debugOutLevel' : Level above which debug output is ignored
debugOutLevel = 1

-- | 'debug' @level msg@ : output @msg@ at level @level@ 
debug level msg = if level <= debugOutLevel then traceShow msg else id
