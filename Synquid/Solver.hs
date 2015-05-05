-- | Solver for second-order constraints
module Synquid.Solver where

import Synquid.Logic
import Synquid.SMTSolver
import Synquid.Util
import Synquid.Pretty

import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Foldable as F

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Control.Applicative
import Control.Lens

{- Interface -}

evalFixPointSolver = runReaderT

-- | 'solveWithParams' @params quals constraints@: 'greatestFixPoint' @quals constraints@ with solver parameters @params@
solveWithParams :: SMTSolver s => SolverParams -> QMap -> [Clause] -> s (Maybe Solution)
solveWithParams params quals constraints = evalFixPointSolver go params
  where
    go = do      
      quals' <- ifM (asks pruneQuals)
        (traverse (traverseOf qualifiers pruneQualifiers) quals) -- remove redundant qualifiers
        (return quals)
      greatestFixPoint quals' constraints
      
-- | Strategies for picking the next candidate solution to strengthen
data CandidatePickStrategy = FirstCandidate | UniformCandidate | InitializedCandidate
      
-- | Strategies for picking the next constraint to solve      
data ConstraintPickStrategy = FirstConstraint | SmallSpaceConstraint

-- | MUS search strategies
data OptimalValuationsStrategy = BFSValuations | UnsatCoreValuations | MarcoValuations

-- | Parameters of the fix point algorithm
data SolverParams = SolverParams {
  pruneQuals :: Bool,                                     -- ^ Should redundant qualifiers be removed before solving constraints?
  optimalValuationsStrategy :: OptimalValuationsStrategy, -- ^ How should we find optimal left-hand side valuations?
  semanticPrune :: Bool,                                  -- ^ After solving each constraints, remove semantically non-optimal solutions
  agressivePrune :: Bool,                                 -- ^ Perform pruning on the LHS-pValuation of as opposed to per-variable valuations
  candidatePickStrategy :: CandidatePickStrategy,         -- ^ How should the next candidate solution to strengthen be picked?
  constraintPickStrategy :: ConstraintPickStrategy        -- ^ How should the next constraint to solve be picked?
}
 
-- | Fix point solver execution 
type FixPointSolver s a = ReaderT SolverParams s a

{- Implementation -}

-- | 'greatestFixPoint' @quals constraints@: weakest solution for a system of second-order constraints @constraints@ over qualifiers @quals@.
greatestFixPoint :: SMTSolver s => QMap -> [Clause] -> FixPointSolver s (Maybe Solution)
greatestFixPoint quals constraints = do
    debug 1 (nest 2 $ text "Constraints" $+$ vsep (map pretty constraints)) $ return ()
    let sol0 = topSolution quals
    (valids, invalids) <- partitionM (isValidClause . clauseApplySolution sol0) constraints
    if null invalids
      then return $ Just sol0
      else go [Candidate sol0 (Set.fromList valids) (Set.fromList invalids)]
  where
    go [] = return Nothing
    go candidates = do
        (cand@(Candidate sol valids invalids), rest) <- pickCandidate candidates <$> asks candidatePickStrategy
        constraint <- asks constraintPickStrategy >>= pickConstraint cand
        let otherInvalids = Set.delete constraint invalids
        case constraint of
          Disjunctive disjuncts -> do
            debugOutputSplit candidates cand constraint $ return ()
            let newCandidates = map ((\invs -> cand { invalidConstraints = invs }) . Set.union otherInvalids . Set.fromList . map Horn) disjuncts
            go $ newCandidates ++ rest
          Horn fml -> do
            let modifiedConstraint = instantiateRhs sol fml
            debugOutput candidates cand fml modifiedConstraint $ return ()
            sols' <- strengthen quals modifiedConstraint sol
                        
            newCandidates <- mapM (updateCandidate constraint otherInvalids valids sol) sols'            
            case find (Set.null . invalidConstraints) newCandidates of
              Just cand' -> return $ Just (solution cand') -- Solution found
              Nothing -> go $ newCandidates ++ rest
              
    instantiateRhs sol fml = case fml of
      Binary Implies lhs rhs -> Binary Implies lhs (applySolution sol rhs)
      _ -> error $ unwords ["greatestFixPoint: encountered ill-formed constraint", show fml]              
              
    -- | Re-evaluate affected clauses in @valids@ and @otherInvalids@ after solution has been strengthened from @sol@ to @sol'@ in order to fix @constraint@
    updateCandidate constraint otherInvalids valids sol sol' = do
      let modifiedUnknowns = Map.keysSet $ Map.filter (not . Set.null) $ Map.unionWith Set.difference sol' sol
      let (unaffectedValids, affectedValids) = Set.partition (\c -> clausePosUnknowns c `disjoint` modifiedUnknowns) valids
      let (unaffectedInvalids, affectedInvalids) = Set.partition (\c -> clauseNegUnknowns c `disjoint` modifiedUnknowns) otherInvalids
      (newValids, newInvalids) <- setPartitionM (isValidClause . clauseApplySolution sol') $ affectedValids `Set.union` affectedInvalids
      return $ Candidate sol' (Set.insert constraint $ unaffectedValids `Set.union` newValids) (unaffectedInvalids `Set.union` newInvalids)            

    nontrivCount = Map.size . Map.filter (not . Set.null) -- number of unknowns with a non-top valuation
    maxQCount = maximum . map Set.size . Map.elems    -- maximum number of qualifiers mapped to an unknown
    minQCount = minimum . map Set.size . Map.elems    -- minimum number of qualifiers mapped to an unknown          
          
    pickCandidate :: [Candidate] -> CandidatePickStrategy -> (Candidate, [Candidate])
    pickCandidate (cand:rest) FirstCandidate = (cand, rest)
    pickCandidate sols UniformCandidate = let
        res = minimumBy (mappedCompare $ \(Candidate s valids invalids) -> (Set.size valids + Set.size invalids, maxQCount s - minQCount s)) sols  -- minimize the difference
      in (res, delete res sols)
    pickCandidate cands InitializedCandidate = let 
        res = maximumBy (mappedCompare $ \(Candidate s valids invalids) -> nontrivCount s) cands  -- maximize the total number and minimize the difference
      in (res, delete res cands)
      
    pickConstraint (Candidate sol valids invalids) strategy = do
      let (ds, hs) = Set.partition isDisjunctive invalids
      if Set.null hs
        then return $ Set.findMin ds
        else case strategy of
          FirstConstraint -> return $ Set.findMin hs
          SmallSpaceConstraint -> do
            -- let spaceSize c = maxValSize quals sol (Set.map (Unknown Map.empty) $ clauseNegUnknowns c)
            let spaceSize (Horn fml) = maxValSize quals sol (unknownsOf fml)
            return $ minimumBy (\x y -> compare (spaceSize x) (spaceSize y)) (Set.toList hs)

    debugOutput cands cand inv modified = debug 1 $ vsep [
      nest 2 $ text "Candidates" <+> parens (pretty $ length cands) $+$ (vsep $ map pretty cands), 
      text "Chosen candidate:" <+> pretty cand, 
      text "Invalid Constraint:" <+> pretty inv, 
      text "Strengthening:" <+> pretty modified]
      
    debugOutputSplit cands cand inv = debug 1 $ vsep [
      nest 2 $ text "Candidates" <+> parens (pretty $ length cands) $+$ (vsep $ map pretty cands), 
      text "Chosen candidate:" <+> pretty cand, 
      text "Splitting Invalid Constraint:" <+> pretty inv]      
    
-- | 'strengthen' @quals fml sol@: all minimal strengthenings of @sol@ using qualifiers from @quals@ that make @fml@ valid;
-- | @fml@ must have the form "/\ u_i ==> const".
strengthen :: SMTSolver s => QMap -> Formula -> Solution -> FixPointSolver s [Solution]
strengthen quals fml@(Binary Implies lhs rhs) sol = do
    let n = maxValSize quals sol unknowns
    lhsValuations <- optimalValuations n (lhsQuals Set.\\ usedLhsQuals) usedLhsQuals rhs -- all minimal valid valuations of the whole antecedent
    debug 1 (text "Optimal valuations:" $+$ vsep (map pretty lhsValuations)) $ return ()
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
    knownConjuncts = conjunctsOf lhs Set.\\ unknowns
    unknownsList = Set.toList unknowns
    lhsQuals = setConcatMap (Set.fromList . lookupQualsSubst quals) unknowns   -- available qualifiers for the whole antecedent
    usedLhsQuals = setConcatMap (valuation sol) unknowns `Set.union` knownConjuncts      -- already used qualifiers for the whole antecedent
    rhsVars = varsOf rhs
        
      -- | All possible additional valuations of @u@ that are subsets of $lhsVal@.
    singleUnknownCandidates lhsVal u = let           
          qs = lookupQualsSubst quals u
          max = lookupQuals quals maxCount u
          used = valuation sol u
          n = Set.size used
      in Set.toList $ boundedSubsets (max - n) $ (Set.fromList qs Set.\\ used) `Set.intersection` lhsVal
    
      -- | All valid partitions of @lhsVal@ into solutions for multiple unknowns.
    splitLhsValuation :: Valuation -> [Solution]
    splitLhsValuation lhsVal = do
      unknownsVal <- mapM (singleUnknownCandidates lhsVal) unknownsList
      let isValidsplit ss s = Set.unions ss == s && sum (map Set.size ss) == Set.size s
      guard $ isValidsplit unknownsVal lhsVal
      return $ Map.fromList $ zipWith unsubst unknownsList unknownsVal
      
    unsubst u@(Unknown s name) quals = (name, Set.map (substitute (inverse s)) quals)
          
strengthen _ fml _ = error $ unwords ["strengthen: encountered ill-formed constraint", show fml]

-- | 'maxValSize' @quals sol unknowns@: Upper bound on the size of valuations of a conjunction of @unknowns@ when strengthening @sol@ 
maxValSize :: QMap -> Solution -> Set Formula -> Int 
maxValSize quals sol unknowns = let 
    usedQuals = setConcatMap (valuation sol) unknowns
  in Set.foldl (\n u -> n + lookupQuals quals maxCount u) 0 unknowns - Set.size usedQuals
  
optimalValuations :: SMTSolver s => Int -> Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
optimalValuations maxSize quals lhs rhs = do
  strategy <- asks optimalValuationsStrategy
  case strategy of
    BFSValuations -> optimalValuationsBFS maxSize quals lhs rhs
    UnsatCoreValuations -> optimalValuationsUnsatCore quals lhs rhs    
    MarcoValuations -> optimalValuationsMarco quals lhs rhs    
    
-- | 'optimalValuations' @quals check@: all smallest subsets of @quals@ for which @check@ returns a solution.
optimalValuationsBFS :: SMTSolver s => Int -> Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
optimalValuationsBFS maxSize quals lhs rhs = map qualsAt <$> filterSubsets (check . qualsAt) (length qualsList)
  where
    qualsList = Set.toList quals
    qualsAt = Set.map (qualsList !!)
    check val = let 
                  n = Set.size val 
                  lhs' = conjunction lhs |&| conjunction val                  
      in if 1 <= n && n <= maxSize
          then isValidFml $ lhs' |=>| rhs
          else return False
  
optimalValuationsUnsatCore :: SMTSolver s => Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
optimalValuationsUnsatCore quals lhs rhs = Set.toList <$> go Set.empty Set.empty [quals]
  where
    lhsList = Set.toList lhs
    notRhs = fnot rhs
    
    go sols _ [] = return $ Set.map snd sols
    go sols unsats (c : cs) = let
        isSubsumed = any (c `Set.isSubsetOf`) cs -- is @c@ is represented by a candidate later in the queue?
        isCovered = F.any (\(r, s) -> c `Set.isSubsetOf` s || (s `Set.isSubsetOf` c && c `Set.isSubsetOf` r)) (sols `Set.union` unsats) -- is @c@ on the path from a prior request to the corresponding solution?
      in if isSubsumed || isCovered
        then go sols unsats cs -- all solutions we could get from @c@ we either already got or are covered by remaining candidates: skip
        else do
          coreMb <- lift $ unsatCore lhsList [notRhs] (Set.toList c)
          case coreMb of
            UCSat -> debug 2 (pretty (conjunction c) <+> text "INVALID") $ go sols unsats cs -- @c@ is SAT
            UCBad preds -> do
              let core = Set.fromList preds
              debug 2 (pretty (conjunction c) <+> text "UNSAT" <+> pretty (conjunction core)) $ go sols (Set.insert (c, core) unsats) (parents c preds ++ cs)              
            UCGood preds -> do
              let core = Set.fromList preds
              debug 2 (pretty (conjunction c) <+> text "SOLUTION" <+> pretty (conjunction core)) $ go (Set.insert (c, core) sols) unsats (parents c preds ++ cs)
              
    parents candidate preds = map (flip Set.delete candidate) preds -- subsets of @candidate@ that together cover all potential remaining solutions    
    
optimalValuationsMarco :: SMTSolver s => Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
optimalValuationsMarco quals lhs rhs = do
    map (Set.delete fixedRhs) . filter (fixedRhs `Set.member`) . map Set.fromList <$> lift (allUnsatCores fixedLhs (fixedRhs : qualsList))
  where
    qualsList = Set.toList quals
    fixedLhs = conjunction lhs
    fixedRhs = fnot rhs

                            
-- | 'filterSubsets' @check n@: all minimal subsets of indexes from [0..@n@) that satisfy @check@,
-- where @check@ is monotone (if a set satisfies @check@, then every superset also satisfies @check@);
-- performs breadth-first search.
filterSubsets :: SMTSolver s => (Set Int -> FixPointSolver s Bool) -> Int -> FixPointSolver s [Set Int]
filterSubsets check n = go [] [Set.empty]
  where
    go solutions candidates = if null candidates 
      then return solutions
      else let new = filter (\c -> not $ any (`Set.isSubsetOf` c) solutions) candidates
        in do
          results <- zip new <$> mapM check new
          let (valids, invalids) = partition snd results
          go (solutions ++ map fst valids) (concatMap children (map fst invalids))      
    children idxs = let lower = if Set.null idxs then 0 else Set.findMax idxs + 1
      in map (`Set.insert` idxs) [lower..(n - 1)]      
            
-- | 'pruneSolutions' @sols@: eliminate from @sols@ all solutions that are semantically stronger on all unknowns than another solution in @sols@ 
pruneSolutions :: SMTSolver s => [Formula] -> [Solution] -> FixPointSolver s [Solution]
pruneSolutions unknowns = let isSubsumed sol sols = anyM (\s -> allM 
                                (\u -> isValidFml $ (conjunction $ valuation sol u) |=>| (conjunction $ valuation s u)) unknowns) sols
  in prune isSubsumed
  
-- | 'pruneValuations' @vals@: eliminate from @vals@ all valuations that are semantically stronger than another pValuation in @vals@   
pruneValuations :: SMTSolver s => [Valuation] -> FixPointSolver s [Valuation] 
pruneValuations = let isSubsumed val vals = let fml = conjunction val in anyM (\v -> isValidFml $ fml |=>| conjunction v) vals
  in prune isSubsumed
  
-- | 'pruneQualifiers' @quals@: eliminate logical duplicates from @quals@
pruneQualifiers :: SMTSolver s => [Formula] -> FixPointSolver s [Formula]   
pruneQualifiers = let isSubsumed qual quals = anyM (\q -> isValidFml $ qual |<=>| q) quals
  in prune isSubsumed
  
-- | 'prune' @isSubsumed xs@ : prune all elements of @xs@ subsumed by another element according to @isSubsumed@  
prune :: SMTSolver s => (a -> [a] -> FixPointSolver s Bool) -> [a] -> FixPointSolver s [a]
prune _ [] = return []
prune isSubsumed (x:xs) = prune' [] x xs
  where
    prune' lefts x [] = ifM (isSubsumed x lefts) (return lefts) (return $ x:lefts)
    prune' lefts x rights@(y:ys) = ifM (isSubsumed x (lefts ++ rights)) (prune' lefts y ys) (prune' (lefts ++ [x]) y ys)  
              
-- | 'isValid' lifted to FixPointSolver      
isValidFml :: SMTSolver s => Formula -> FixPointSolver s Bool
isValidFml = lift . isValid

-- | 'isValidClause' @c@: is @c@ logically valid? 
isValidClause :: SMTSolver s => Clause -> FixPointSolver s Bool
isValidClause (Horn fml) = isValidFml fml
isValidClause (Disjunctive disjuncts) = or <$> mapM (isValidFml . conjunction . Set.fromList) disjuncts