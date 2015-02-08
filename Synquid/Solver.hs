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
      quals' <- ifM (asks pruneQuals)
        (traverse (traverseOf qualifiers pruneQualifiers) quals) -- remove redundant qualifiers
        (return quals)
      greatestFixPoint quals' fmls
      
-- | Strategies for picking the next constraint to solve      
data ConstraintPickStrategy = PickFirst | PickSmallestSpace      

-- | Parameters of the fix point algorithm
data SolverParams = SolverParams {
  pruneQuals :: Bool,                               -- ^ Should redundant qualifiers be removed before solving constraints?
  semanticPrune :: Bool,                            -- ^ After solving each constraints, remove semantically non-optimal solutions
  agressivePrune :: Bool,                           -- ^ Perform pruning on the LHS-valuation of as opposed to per-variable valuations
  constraintPickStrategy :: ConstraintPickStrategy, -- ^ How should the next constraint to solve be picked
  maxCegisIterations :: Int                         -- ^ Maximum number of CEGIS iterations for parametrized qualifiers (unbounded if negative)
}
    
type FixPointSolver m a = ReaderT SolverParams m a
  
-- | 'greatestFixPoint' @quals fmls@: weakest solution for a system of second-order constraints @fmls@ over qualifiers @quals@, if one exists;
-- | @fml@ must have the form "/\ u_i ==> fml'".
greatestFixPoint :: SMTSolver m => QMap -> [Formula] -> FixPointSolver m (Maybe Solution)
greatestFixPoint quals fmls = debug1 (nest 2 $ text "Constraints" $+$ vsep (map pretty fmls)) $ go [topSolution quals]
  where
    go :: SMTSolver m => [(Solution, SMTModel)] -> FixPointSolver m (Maybe Solution)
    go (sol:sols) = do
        invalidConstraint <- asks constraintPickStrategy >>= pickConstraint sol        
        let modifiedConstraint = case invalidConstraint of
                                    Binary Implies lhs rhs -> Binary Implies lhs (substituteSolution sol rhs)
                                    _ -> error $ "greatestFixPoint: encountered ill-formed constraint " ++ show invalidConstraint        
        sols' <- debugOutput (sol:sols) sol invalidConstraint modifiedConstraint $ strengthen quals modifiedConstraint sol
        validSolution <- findM (\s -> and <$> mapM (isValidFml . substituteSolution s) (delete invalidConstraint fmls)) sols'
        case validSolution of
          Just (s, m) -> return $ Just $ simpleSolution s m -- Solution found
          Nothing -> go $ sols' ++ sols
    go [] = return Nothing
    pickConstraint (sol, model) PickFirst = fromJust <$> findM (liftM not . isValidFml . substituteSolution (sol, model)) fmls
    pickConstraint (sol, model) PickSmallestSpace  = do
      invalids <- filterM (liftM not . isValidFml . substituteSolution (sol, model)) fmls
      let spaceSize fml = maxValSize quals sol (unknownsOf fml)
      return $ minimumBy (\x y -> compare (spaceSize x) (spaceSize y)) invalids
    debugOutput sols sol inv model = debug1 $ vsep [
      nest 2 $ text "Candidates" <+> parens (pretty $ length sols) $+$ (vsep $ map pretty sols), 
      text "Chosen candidate:" <+> pretty sol, 
      text "Invalid Constraint:" <+> pretty inv, 
      text "Strengthening:" <+> pretty model]
    
-- | 'strengthen' @quals fml sol@: all minimal strengthenings of @sol@ using qualifiers from @quals@ that make @fml@ valid;
-- | @fml@ must have the form "/\ u_i ==> const".
strengthen :: SMTSolver m => QMap -> Formula -> (Solution, SMTModel) -> FixPointSolver m [(Solution, SMTModel)]
strengthen quals fml@(Binary Implies lhs rhs) (sol, model) = do
    lhsValuations <- optimalValuations (Set.toList $ lhsQuals Set.\\ usedLhsQuals) check -- all minimal valid valuations of the whole antecedent
    let splitting = Map.filter (not . null) $ Map.fromList $ zip lhsValuations (map splitLhsValuation lhsValuations) -- map of lhsValuations with a non-empty split to their split
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
    rhsVars = varsOf rhs
    ins = Map.unions [view pQualInputs (lookupQuals quals u) | u <- unknownsList]
    check val = let 
                  n = Set.size val 
                  lhs' = conjunction usedLhsQuals |&| conjunction val                  
      in if 1 <= n && n <= maxValSize quals sol unknowns
            then if rhsVars `Set.isSubsetOf` varsOf lhs'
              then findAngelics (lhs' |=>| rhs) ins                                                                   -- all variables of rhs are contained in lhs': nontrivial solution possible
              else ifM (isValidFml $ fnot lhs') (return $ Just $ trivialModel (angelicsOf lhs')) (return Nothing)     -- rhs has more variables: if lhs' is unsat, return any solution, and otherwise no solution
              -- else return Nothing
            else return Nothing        
    merge (sol', mod') = (Map.unionWith Set.union sol sol', Map.union model mod')           -- new part of the solution merged with @sol@
    
      -- | All possible additional valuations of @u@ that are subsets of $lhsVal@.
    singleUnknownCandidates lhsVal u = let 
          QSpace qs max _ = lookupQuals quals u
          used = valuation sol u
          n = Set.size used
      in Set.toList $ boundedSubsets (max - n) $ (Set.fromList qs Set.\\ used) `Set.intersection` lhsVal
    
      -- | All valid partitions of @lhsVal@ into solutions for multiple unknowns.
    splitLhsValuation :: (Valuation, SMTModel) -> [(Solution, SMTModel)]
    splitLhsValuation (lhsVal, m) = do
      unknownsVal <- mapM (singleUnknownCandidates lhsVal) unknownsList
      let isValidsplit ss s = Set.unions ss == s && sum (map Set.size ss) == Set.size s
      guard $ isValidsplit unknownsVal lhsVal
      return (Map.fromList $ zip unknownsList unknownsVal, m)
          
strengthen _ fml _ = error $ "strengthen: encountered ill-formed constraint " ++ show fml

-- | 'maxValSize' @quals sol unknowns@: Upper bound on the size of valuations of a conjunction of @unknowns@ when strengthening @sol@ 
maxValSize :: QMap -> Solution -> Set Id -> Int 
maxValSize quals sol unknowns = let 
    usedQuals = setConcatMap (valuation sol) unknowns
  in Set.foldl (\n u -> n + view maxCount (lookupQuals quals u)) 0 unknowns - Set.size usedQuals
 
-- | 'optimalValuations' @quals check@: all smallest subsets of @quals@ that make @subst@ valid.
optimalValuations :: SMTSolver m => [Formula] -> (Valuation -> FixPointSolver m (Maybe SMTModel)) -> FixPointSolver m [(Valuation, SMTModel)]
optimalValuations quals check = map (over _1 qualsAt) <$> filterSubsets (check . qualsAt) (length quals)
  where
    qualsAt idxs = Set.map (quals !!) idxs
    -- getModel idxs = case subst $ qualsAt idxs of
      -- Nothing -> return Nothing
      -- Just fml -> findAngelics fml ins
      
-- | 'filterSubsets' @getModel n@: all minimal subsets of indexes from [0..@n@) fro which @getModel@ returns a model,
-- where @getModel@ is monotone (if a set has a model, then every superset also has a model);
-- performs breadth-first search.
filterSubsets :: SMTSolver m => (Set Int -> FixPointSolver m (Maybe SMTModel)) -> Int -> FixPointSolver m [(Set Int, SMTModel)]
filterSubsets getModel n = go [] [Set.empty]
  where
    go solutions candidates = if null candidates 
      then return solutions
      else let new = filter (\s -> not $ any (flip Set.isSubsetOf s) (map fst solutions)) candidates
        in do
          results <- zip new <$> mapM getModel new
          let (valids, invalids) = partition (isJust . snd) results
          go (solutions ++ map (over _2 fromJust) valids) (concatMap children (map fst invalids))      
    children idxs = let lower = if Set.null idxs then 0 else Set.findMax idxs + 1
      in map (flip Set.insert idxs) [lower..(n - 1)]      
            
-- | 'pruneSolutions' @sols@: eliminate from @sols@ all solutions that are semantically stronger on all unknowns than another solution in @sols@ 
pruneSolutions :: SMTSolver m => [Id] -> [(Solution, SMTModel)] -> FixPointSolver m [(Solution, SMTModel)]
pruneSolutions unknowns = let isSubsumed (sol, model) sols = anyM (\(s, m) -> allM 
                                (\u -> isValidFml $ substituteModel model (conjunction $ valuation sol u) |=>| substituteModel m (conjunction $ valuation s u)) unknowns) sols
  in prune isSubsumed
  
-- | 'pruneValuations' @vals@: eliminate from @vals@ all valuations that are semantically stronger than another valuation in @vals@   
pruneValuations :: SMTSolver m => [(Valuation, SMTModel)] -> FixPointSolver m [(Valuation, SMTModel)] 
pruneValuations = let isSubsumed (val, model) vals = 
                       let fml = substituteModel model (conjunction val) in anyM (\(v, m) -> isValidFml $ fml |=>| substituteModel m (conjunction v)) vals
  in prune isSubsumed
  
-- | 'pruneQualifiers' @quals@: eliminate logical duplicates from @quals@
pruneQualifiers :: SMTSolver m => [Formula] -> FixPointSolver m [Formula]   
pruneQualifiers = let isSubsumed qual quals = anyM (\q -> isValidFml $ qual |<=>| q) quals
  in prune isSubsumed
  
prune :: SMTSolver m => (a -> [a] -> FixPointSolver m Bool) -> [a] -> FixPointSolver m [a]
prune _ [] = return []
prune isSubsumed (x:xs) = prune' [] x xs
  where
    prune' lefts x [] = ifM (isSubsumed x lefts) (return lefts) (return $ x:lefts)
    prune' lefts x rights@(y:ys) = ifM (isSubsumed x (lefts ++ rights)) (prune' lefts y ys) (prune' (lefts ++ [x]) y ys)  
              
-- | 'isValid' lifted to FixPointSolver      
isValidFml :: SMTSolver m => Formula -> FixPointSolver m Bool
isValidFml = lift . isValid

-- | 'findAngelics' @fml@: solve exists angelics :: forall vars :: lhs (angelics, vars) ==> rhs (vars)
findAngelics :: SMTSolver m => Formula -> Map Id (Set Id) -> FixPointSolver m (Maybe SMTModel)
findAngelics fml@(Binary Implies lhs rhs) ins = if Set.null angelics 
    then ifM (isValidFml fml) (return $ Just Map.empty) (return Nothing)
    else do 
      max <- asks maxCegisIterations
      debug1 (text "Solving" <+> pretty fml $+$ text "Outs" <+> pretty (Set.toList outs)) $ go max [trivialModel vars]
  where
    angelics = angelicsOf fml -- existentially quantified variables
    vars = varsOf fml -- universally quantified variables
    outs = vars Set.\\ (Set.unions $ Map.elems $ restrictDomain angelics ins)
    
    fromExample ex i = let -- part of the synthesis constraint derived from counter-example @ex@ at position @i@        
        negative = fnot (substituteModel ex lhs) -- negative example (use all inputs)
        positive' = substituteModel (removeDomain outs ex) (lhs |&| rhs) -- positive example (use only independent inputs and treat dependent ones angelically)
        positive = Set.foldr (\dep -> substituteExpr dep (Var $ dep ++ show i)) positive' outs -- rename outs to be different in different examples
      in if i == 0 
            then Set.singleton positive  -- no negative example from the first input, since it is not necessarily a counter-example
            else Set.fromList [negative, positive]
    toSolve examples = let l = length examples in conjunction $ Set.unions $ zipWith fromExample examples [l - 1, l - 2 .. 0]
            
    go 0 _ = return Nothing
    go n examples = do
      solMb <- lift $ modelOf $ toSolve examples -- ToDo: have two solvers, so that we can just add constraints to the first one
      case solMb of
        Nothing -> return Nothing
        Just sol -> do                                                                        -- Solution found: verify
          let candidate = restrictDomain angelics sol
          counterExampleMb <- lift $ modelOf $ fnot $ substituteModel candidate fml
          case counterExampleMb of
            Nothing -> return $ Just candidate
            Just counterExample -> go (n - 1) $ counterExample : examples
                        
findAngelics fml _ = error $ "findAngelics: encountered ill-formed constraint " ++ show fml              
