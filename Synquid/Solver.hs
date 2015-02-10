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

{- Interface -}

evalFixPointSolver = runReaderT

-- | 'solveWithParams' @params quals fmls@: 'greatestFixPoint' @quals fmls@ with solver parameters @params@
solveWithParams :: SMTSolver m => SolverParams -> QMap -> [Formula] -> m (Maybe Solution)
solveWithParams params quals fmls = evalFixPointSolver go params
  where
    go = do      
      quals' <- ifM (asks pruneQuals)
        (traverse (traverseOf qualifiers pruneQualifiers) quals) -- remove redundant qualifiers
        (return quals)
      greatestFixPoint quals' fmls
      
-- | Strategies for picking the next candidate solution to strengthen
data CandidatePickStrategy = FirstCandidate | UniformCandidate | UniformStrongCandidate
      
-- | Strategies for picking the next constraint to solve      
data ConstraintPickStrategy = FirstConstraint | SmallSpaceConstraint      

-- | Parameters of the fix point algorithm
data SolverParams = SolverParams {
  pruneQuals :: Bool,                               -- ^ Should redundant qualifiers be removed before solving constraints?
  semanticPrune :: Bool,                            -- ^ After solving each constraints, remove semantically non-optimal solutions
  agressivePrune :: Bool,                           -- ^ Perform pruning on the LHS-pValuation of as opposed to per-variable valuations
  candidatePickStrategy :: CandidatePickStrategy,   -- ^ How should the next candidate solution to strengthen be picked?
  constraintPickStrategy :: ConstraintPickStrategy, -- ^ How should the next constraint to solve be picked?
  maxCegisIterations :: Int                         -- ^ Maximum number of CEGIS iterations for parametrized qualifiers (unbounded if negative)
}
 
-- | Fix point solver execution 
type FixPointSolver m a = ReaderT SolverParams m a

{- Implementation -}
  
-- | 'greatestFixPoint' @quals fmls@: weakest solution for a system of second-order constraints @fmls@ over qualifiers @quals@, if one exists;
-- | @fml@ must have the form "/\ u_i ==> fml'"
greatestFixPoint :: SMTSolver m => QMap -> [Formula] -> FixPointSolver m (Maybe Solution)
greatestFixPoint quals fmls = debug 1 (nest 2 $ text "Constraints" $+$ vsep (map pretty fmls)) $ go [topSolution quals]
  where
    go :: SMTSolver m => [PSolution] -> FixPointSolver m (Maybe Solution)
    go [] = return Nothing
    go sols = do
        (sol, rest) <- pickCandidate sols <$> asks candidatePickStrategy
        invalidConstraint <- asks constraintPickStrategy >>= pickConstraint sol        
        let modifiedConstraint = case invalidConstraint of
                                    Binary Implies lhs rhs -> Binary Implies lhs (applySolution sol rhs)
                                    _ -> error $ "greatestFixPoint: encountered ill-formed constraint " ++ show invalidConstraint        
        sols' <- debugOutput sols sol invalidConstraint modifiedConstraint $ strengthen quals modifiedConstraint sol
        validSolution <- findM (\s -> and <$> mapM (isValidFml . applySolution s) (delete invalidConstraint fmls)) sols'
        case validSolution of
          Just sol' -> return $ Just $ instantiate sol' -- Solution found
          Nothing -> go $ sols' ++ rest  
          
    strength = Set.size . Set.unions . Map.elems . view solution    -- total number of qualifiers in a solution
    maxQCount = maximum . map Set.size . Map.elems . view solution  -- maximum number of qualifiers mapped to an unknown
    minQCount = minimum . map Set.size . Map.elems . view solution  -- minimum number of qualifiers mapped to an unknown          
          
    pickCandidate :: [PSolution] -> CandidatePickStrategy -> (PSolution, [PSolution])
    pickCandidate (sol:rest) FirstCandidate = (sol, rest)
    pickCandidate sols UniformCandidate = let
        res = minimumBy (mappedCompare $ \s -> maxQCount s - minQCount s) sols  -- minimize the difference
      in (res, delete res sols)
    pickCandidate sols UniformStrongCandidate = let 
        res = maximumBy (mappedCompare $ \s -> (strength s, minQCount s - maxQCount s)) sols  -- maximize the total number and minimize the difference
      in (res, delete res sols)
      
    pickConstraint sol FirstConstraint = fromJust <$> findM (liftM not . isValidFml . applySolution sol) fmls
    pickConstraint sol SmallSpaceConstraint = do
      invalids <- filterM (liftM not . isValidFml . applySolution sol) fmls
      let spaceSize fml = maxValSize quals sol (unknownsOf fml)
      return $ minimumBy (\x y -> compare (spaceSize x) (spaceSize y)) invalids
      
    debugOutput sols sol inv model = debug 1 $ vsep [
      nest 2 $ text "Candidates" <+> parens (pretty $ length sols) $+$ (vsep $ map pretty sols), 
      text "Chosen candidate:" <+> pretty sol, 
      text "Invalid Constraint:" <+> pretty inv, 
      text "Strengthening:" <+> pretty model]
    
-- | 'strengthen' @quals fml sol@: all minimal strengthenings of @sol@ using qualifiers from @quals@ that make @fml@ valid;
-- | @fml@ must have the form "/\ u_i ==> const".
strengthen :: SMTSolver m => QMap -> Formula -> PSolution -> FixPointSolver m [PSolution]
strengthen quals fml@(Binary Implies lhs rhs) sol = do
    lhsValuations <- optimalValuations (Set.toList $ lhsQuals Set.\\ usedLhsQuals) check -- all minimal valid valuations of the whole antecedent
    let splitting = Map.filter (not . null) $ Map.fromList $ zip lhsValuations (map splitLhsValuation lhsValuations) -- map of lhsValuations with a non-empty split to their split
    let allSolutions = concat $ Map.elems splitting
    pruned <- ifM (asks semanticPrune) 
      (ifM (asks agressivePrune)
        (concatMap (splitting Map.!) <$> pruneValuations (Map.keys splitting))  -- Prune LHS valuations and then return the splits of only optimal valuations
        (pruneSolutions unknownsList allSolutions))                             -- Prune per-variable
      (return allSolutions) 
    return $ map (merge sol) pruned
  where    
    unknowns = unknownsOf lhs
    unknownsList = Set.toList unknowns
    lhsQuals = setConcatMap (Set.fromList . lookupQuals quals qualifiers) unknowns   -- available qualifiers for the whole antecedent
    usedLhsQuals = setConcatMap (pValuation sol) unknowns                            -- already used qualifiers for the whole antecedent
    rhsVars = varsOf rhs
    ins = Map.unions [lookupQuals quals inputVars u | u <- unknownsList]
    
    check val = let 
                  n = Set.size val 
                  lhs' = conjunction usedLhsQuals |&| conjunction val                  
      in if 1 <= n && n <= maxValSize quals sol unknowns
            -- then if rhsVars `Set.isSubsetOf` varsOf lhs'
              then findParams (lhs' |=>| rhs) ins                                                                   -- all variables of rhs are contained in lhs': nontrivial solution possible
              -- else ifM (isValidFml $ fnot lhs') (return $ Just $ trivialModel (paramsOf lhs')) (return Nothing)     -- rhs has more variables: if lhs' is unsat, return any solution, and otherwise no solution
              -- else return Nothing
            else return Nothing        
    
      -- | All possible additional valuations of @u@ that are subsets of $lhsVal@.
    singleUnknownCandidates lhsVal u = let           
          (qs, max) = lookupQuals quals (pairGetter qualifiers maxCount) u
          used = pValuation sol u
          n = Set.size used
      in Set.toList $ boundedSubsets (max - n) $ (Set.fromList qs Set.\\ used) `Set.intersection` lhsVal
    
      -- | All valid partitions of @lhsVal@ into solutions for multiple unknowns.
    splitLhsValuation :: (Valuation, SMTModel) -> [PSolution]
    splitLhsValuation (lhsVal, m) = do
      unknownsVal <- mapM (singleUnknownCandidates lhsVal) unknownsList
      let isValidsplit ss s = Set.unions ss == s && sum (map Set.size ss) == Set.size s
      guard $ isValidsplit unknownsVal lhsVal
      return $ PSolution (Map.fromList $ zip unknownsList unknownsVal) m
          
strengthen _ fml _ = error $ "strengthen: encountered ill-formed constraint " ++ show fml

-- | 'maxValSize' @quals sol unknowns@: Upper bound on the size of valuations of a conjunction of @unknowns@ when strengthening @sol@ 
maxValSize :: QMap -> PSolution -> Set Id -> Int 
maxValSize quals sol unknowns = let 
    usedQuals = setConcatMap (pValuation sol) unknowns
  in Set.foldl (\n u -> n + lookupQuals quals maxCount u) 0 unknowns - Set.size usedQuals
 
-- | 'optimalValuations' @quals check@: all smallest subsets of @quals@ for which @check@ returns a solution.
optimalValuations :: SMTSolver m => [Formula] -> (Valuation -> FixPointSolver m (Maybe SMTModel)) -> FixPointSolver m [(Valuation, SMTModel)]
optimalValuations quals check = map (over _1 qualsAt) <$> filterSubsets (check . qualsAt) (length quals)
  where
    qualsAt = Set.map (quals !!)
      
-- | 'filterSubsets' @check n@: all minimal subsets of indexes from [0..@n@) for which @check@ returns a model,
-- where @check@ is monotone (if a set has a model, then every superset also has a model);
-- performs breadth-first search.
filterSubsets :: SMTSolver m => (Set Int -> FixPointSolver m (Maybe SMTModel)) -> Int -> FixPointSolver m [(Set Int, SMTModel)]
filterSubsets check n = go [] [Set.empty]
  where
    go solutions candidates = if null candidates 
      then return solutions
      else let new = filter (\s -> not $ any (flip Set.isSubsetOf s) (map fst solutions)) candidates
        in do
          results <- zip new <$> mapM check new
          let (valids, invalids) = partition (isJust . snd) results
          go (solutions ++ map (over _2 fromJust) valids) (concatMap children (map fst invalids))      
    children idxs = let lower = if Set.null idxs then 0 else Set.findMax idxs + 1
      in map (flip Set.insert idxs) [lower..(n - 1)]      
            
-- | 'pruneSolutions' @sols@: eliminate from @sols@ all solutions that are semantically stronger on all unknowns than another solution in @sols@ 
pruneSolutions :: SMTSolver m => [Id] -> [PSolution] -> FixPointSolver m [PSolution]
pruneSolutions unknowns = let isSubsumed sol sols = anyM (\s -> allM 
                                (\u -> isValidFml $ (conjunction $ instValuation sol u) |=>| (conjunction $ instValuation s u)) unknowns) sols
  in prune isSubsumed
  
-- | 'pruneValuations' @vals@: eliminate from @vals@ all valuations that are semantically stronger than another pValuation in @vals@   
pruneValuations :: SMTSolver m => [(Valuation, SMTModel)] -> FixPointSolver m [(Valuation, SMTModel)] 
pruneValuations = let isSubsumed (val, model) vals = 
                       let fml = substituteModel model (conjunction val) in anyM (\(v, m) -> isValidFml $ fml |=>| substituteModel m (conjunction v)) vals
  in prune isSubsumed
  
-- | 'pruneQualifiers' @quals@: eliminate logical duplicates from @quals@
pruneQualifiers :: SMTSolver m => [Formula] -> FixPointSolver m [Formula]   
pruneQualifiers = let isSubsumed qual quals = anyM (\q -> isValidFml $ qual |<=>| q) quals
  in prune isSubsumed
  
-- | 'prune' @isSubsumed xs@ : prune all elements of @xs@ subsumed by another element according to @isSubsumed@  
prune :: SMTSolver m => (a -> [a] -> FixPointSolver m Bool) -> [a] -> FixPointSolver m [a]
prune _ [] = return []
prune isSubsumed (x:xs) = prune' [] x xs
  where
    prune' lefts x [] = ifM (isSubsumed x lefts) (return lefts) (return $ x:lefts)
    prune' lefts x rights@(y:ys) = ifM (isSubsumed x (lefts ++ rights)) (prune' lefts y ys) (prune' (lefts ++ [x]) y ys)  
              
-- | 'isValid' lifted to FixPointSolver      
isValidFml :: SMTSolver m => Formula -> FixPointSolver m Bool
isValidFml = lift . isValid

-- | 'findParams' @fml@: solve exists params :: forall vars :: lhs (params, vars) ==> rhs (vars)
findParams :: SMTSolver m => Formula -> Map Id (Set Id) -> FixPointSolver m (Maybe SMTModel)
findParams fml@(Binary Implies lhs rhs) ins = if Set.null params 
    then ifM (isValidFml fml) (return $ Just Map.empty) (return Nothing)
    else do 
      max <- asks maxCegisIterations
      debug 1 (text "Solving" <+> pretty fml $+$ text "Outs" <+> pretty (Set.toList outs)) $ go max [trivialModel vars]
  where
    params = paramsOf fml
    vars = varsOf fml
    outs = vars Set.\\ (Set.unions $ Map.elems $ restrictDomain params ins) -- angelically chosen variables
    
    fromExample ex i = let -- part of the synthesis constraint derived from counter-example @ex@ at position @i@        
        negative = fnot (substituteModel ex lhs) -- negative example (use all inputs)
        positive' = substituteModel (removeDomain outs ex) (lhs |&| rhs) -- positive example (use only independent inputs and treat dependent ones angelically)
        positive = Set.foldr (\dep -> substitute $ Map.singleton dep (Var $ dep ++ show i)) positive' outs -- rename outs to be different in different examples
      in if i == 0 
            then Set.singleton positive  -- no negative example from the first input, since it is not necessarily a counter-example
            else Set.fromList [negative, positive]
    toSolve examples = let l = length examples in conjunction $ Set.unions $ zipWith fromExample examples [l - 1, l - 2 .. 0]
            
    go 0 _ = return Nothing -- Maximum number of iterations reached: exit
    go n examples = do
      solMb <- lift $ modelOf $ toSolve examples -- ToDo: have two solvers, so that we can just add constraints to the first one
      case solMb of
        Nothing -> return Nothing   -- No solution: exit
        Just sol -> do              -- Solution found: verify
          let candidate = restrictDomain params sol
          counterExampleMb <- lift $ modelOf $ fnot $ substituteModel candidate fml
          case counterExampleMb of
            Nothing -> return $ Just candidate                              -- No counter-example: solution found
            Just counterExample -> go (n - 1) $ counterExample : examples   -- Counter-example: add to list of examples and continue
                        
findParams fml _ = error $ "findParams: encountered ill-formed constraint " ++ show fml              
