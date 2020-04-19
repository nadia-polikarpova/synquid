{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

-- | Solver for second-order constraints
module Synquid.HornSolver (
    CandidatePickStrategy (..)
  , ConstraintPickStrategy (..)
  , OptimalValuationsStrategy (..)
  , HornSolverParams (..)
  , FixPointSolver
  , evalFixPointSolver
  ) where

import Synquid.Logic
import Synquid.SolverMonad
import Synquid.Util
import Synquid.Pretty

import Data.Function
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
import Control.Lens hiding (both)

import Debug.Trace

{- Interface -}

-- | Strategies for picking the next candidate solution to strengthen
data CandidatePickStrategy = FirstCandidate | ValidWeakCandidate | InitializedWeakCandidate
      
-- | Strategies for picking the next constraint to solve      
data ConstraintPickStrategy = FirstConstraint | SmallSpaceConstraint

-- | MUS search strategies
data OptimalValuationsStrategy = BFSValuations | MarcoValuations

-- | Parameters of the fix point algorithm
data HornSolverParams = HornSolverParams {
  pruneQuals :: Bool,                                     -- ^ Should redundant qualifiers be removed before solving constraints?
  isLeastFixpoint :: Bool,                                -- ^ Should the solver look for the least fixpoint (as opposed to greatest)?
  optimalValuationsStrategy :: OptimalValuationsStrategy, -- ^ How should we find optimal left-hand side valuations?
  semanticPrune :: Bool,                                  -- ^ After solving each constraints, remove semantically non-optimal solutions
  agressivePrune :: Bool,                                 -- ^ Perform pruning on the LHS-pValuation of as opposed to per-variable valuations
  candidatePickStrategy :: CandidatePickStrategy,         -- ^ How should the next candidate solution to strengthen be picked?
  constraintPickStrategy :: ConstraintPickStrategy,       -- ^ How should the next constraint to solve be picked?
  solverLogLevel :: Int                                   -- ^ How verbose logging is
}

-- | Fix point solver execution 
type FixPointSolver s = ReaderT HornSolverParams s

evalFixPointSolver = runReaderT

instance MonadSMT s => MonadHorn (FixPointSolver s) where
  initHornSolver env = do
    lift (initSolver env)
    return initialCandidate
    
  preprocessConstraint = preprocess
    
  checkCandidates = check
    
  refineCandidates = refine
  
  pruneQualifiers quals = ifM (asks pruneQuals) (pruneQSpace quals) (return quals)  
  
 
{- Implementation -}

initialSolution :: MonadSMT s => QMap -> FixPointSolver s Solution
initialSolution qmap = ifM (asks isLeastFixpoint) (return $ botSolution qmap) (return $ topSolution qmap)  

preprocess :: MonadSMT s => Formula -> FixPointSolver s [Formula]
preprocess (Binary Implies lhs rhs) = ifM (asks isLeastFixpoint) (return preprocessLFP) (return preprocessGFP)
  where
    preprocessLFP = 
      -- ToDo: split conjuncts
      let 
        rDisjuncts = Set.fromList $ uDNF rhs
        (noUnknowns, withUnknowns) = Set.partition (Set.null . unknownsOf) rDisjuncts
      in if Set.size withUnknowns > 1
        then error $ unwords ["Least fixpoint solver got a disjunctive right-hand-side:", show rhs]
        else -- Only one disjuncts with unknowns: split into all conjuncts with unknowns into separate constraints
          let
            lhs' = conjunction $ Set.insert lhs (Set.map fnot noUnknowns)
            rConjuncts = conjunctsOf (disjunction withUnknowns)
            (conjNoUnknowns, conjWithUnknowns) = Set.partition (Set.null . unknownsOf) rConjuncts
            rhss = (if Set.null conjNoUnknowns then [] else [conjunction conjNoUnknowns]) ++ Set.toList conjWithUnknowns
          in map (lhs' |=>|) rhss

    preprocessGFP = map (|=>| rhs) (uDNF lhs) -- Remove disjunctions of unknowns on the left
    
preprocess fml = error $ unwords ["preprocess: encountered ill-formed constraint", show fml]

-- | 'refine' @constraints quals extractAssumptions cands@ : solve @constraints@ using @quals@ starting from initial candidates @cands@;
-- use @extractAssumptions@ to extract axiom instantiations from formulas;
-- if there is no solution, produce an empty list of candidates; otherwise the first candidate in the list is a complete solution
refine :: MonadSMT s => [Formula] -> QMap -> ExtractAssumptions -> [Candidate] -> FixPointSolver s [Candidate]
refine constraints quals extractAssumptions cands = do
    writeLog 3 (vsep [nest 2 $ text "Constraints" $+$ vsep (map pretty constraints), nest 2 $ text "QMap" $+$ pretty quals])
    let constraints' = filter isNew constraints
    cands' <- mapM (addConstraints constraints') cands
    case find (Set.null . invalidConstraints) cands' of
      Just c -> return $ c : delete c cands'
      Nothing -> ifM (asks isLeastFixpoint)
                    (leastFixPoint extractAssumptions cands')
                    (greatestFixPoint quals extractAssumptions cands')
  where      
    isNew c = not (c `Set.member` validConstraints (head cands)) && not (c `Set.member` invalidConstraints (head cands))
      
    addConstraints constraints (Candidate sol valids invalids label) = do
      initSol <- initialSolution quals
      let sol' = Map.union sol initSol -- Add new unknowns (since map-union is left-biased, old solutions are preserved for old unknowns)
      (valids', invalids') <- partitionM (isValidFml . hornApplySolution extractAssumptions sol') constraints -- Evaluate new constraints
      return $ Candidate sol' (valids `Set.union` Set.fromList valids') (invalids `Set.union` Set.fromList invalids') label

-- | 'check' @consistency fmls extractAssumptions cands@ : return those candidates from @cands@ under which all @fmls@ are either valid or satisfiable, depending on @consistency@;
-- use @extractAssumptions@ to extract axiom instantiations from formulas
check :: MonadSMT s => Bool -> [Formula] ->  ExtractAssumptions -> [Candidate] -> FixPointSolver s [Candidate]
check consistency fmls extractAssumptions cands = do    
    writeLog 3 (vsep [
      nest 2 $ (if consistency then text "Checking consistency" else text "Checking validity") $+$ vsep (map pretty fmls), 
      nest 2 $ text "Candidates" <+> parens (pretty $ length cands) $+$ (vsep $ map pretty cands)])
    cands' <- filterM checkCand cands
    writeLog 3 (nest 2 $ text "Remaining Candidates" <+> parens (pretty $ length cands') $+$ (vsep $ map pretty cands'))
    return cands'
  where
    apply sol fml = let fml' = applySolution sol fml in fml' |&| conjunction (extractAssumptions fml')      
    checkCand (Candidate sol valids invalids label) = if consistency
      then allM isSatFml (map (apply sol) fmls)
      else allM isValidFml (map (hornApplySolution extractAssumptions sol) fmls)

-- | 'greatestFixPoint' @quals constraints@: weakest solution for a system of second-order constraints @constraints@ over qualifiers @quals@.
greatestFixPoint :: MonadSMT s => QMap -> ExtractAssumptions -> [Candidate] -> FixPointSolver s [Candidate]
greatestFixPoint _ _ [] = return []
greatestFixPoint quals extractAssumptions candidates = do
    (cand@(Candidate sol _ _ _), rest) <- pickCandidate candidates <$> asks candidatePickStrategy
    fml <- asks constraintPickStrategy >>= pickConstraint cand
    let modifiedConstraint = instantiateRhs sol fml 
    debugOutput candidates cand fml modifiedConstraint
    diffs <- strengthen quals extractAssumptions modifiedConstraint sol                        
    (newCandidates, rest') <- if length diffs == 1
      then do -- Propagate the diff to all equivalent candidates
        let unknowns = Set.map unknownName $ unknownsOf fml
        let (equivs, nequivs) = partition (\(Candidate s valids invalids _) -> restrictDomain unknowns s == restrictDomain unknowns sol && Set.member fml invalids) rest
        nc <- mapM (\c -> updateCandidate fml c diffs (head diffs)) (cand : equivs)
        return (nc, nequivs)
      else do -- Only update the current candidate
        nc <- mapM (updateCandidate fml cand diffs) diffs
        return (nc, rest)
    case find (Set.null . invalidConstraints) newCandidates of
      Just cand' -> return $ cand' : (delete cand' newCandidates ++ rest')  -- Solution found
      Nothing -> greatestFixPoint quals extractAssumptions (newCandidates ++ rest')

  where
    instantiateRhs sol (Binary Implies lhs rhs) = Binary Implies lhs (applySolution sol rhs)
              
    -- | Re-evaluate affected clauses in @valids@ and @otherInvalids@ after solution has been strengthened from @sol@ to @sol'@ in order to fix @fml@
    updateCandidate fml (Candidate sol valids invalids label) diffs diff = do
      let sol' = merge sol diff
      let modifiedUnknowns = Map.keysSet $ Map.filter (not . Set.null) diff
      let (unaffectedValids, affectedValids) = Set.partition (\fml -> posUnknowns fml `disjoint` modifiedUnknowns) (Set.insert fml valids) -- fml should be re-evaluated if it happens to have the same unknowns also on the right
      let (unaffectedInvalids, affectedInvalids) = Set.partition (\fml -> negUnknowns fml `disjoint` modifiedUnknowns) (Set.delete fml invalids)
      (newValids, newInvalids) <- setPartitionM (isValidFml . hornApplySolution extractAssumptions sol') $ affectedValids `Set.union` affectedInvalids
      let newLabel = if length diffs == 1 then label else label ++ "." ++ show (fromJust $ elemIndex diff diffs)
      return $ Candidate sol' (unaffectedValids `Set.union` newValids) (unaffectedInvalids `Set.union` newInvalids) newLabel
      
    nontrivCount = Map.size . Map.filter (not . Set.null) -- number of unknowns with a non-top valuation
    totalQCount = sum . map Set.size . Map.elems          -- total number of qualifiers in a solution
          
    pickCandidate :: [Candidate] -> CandidatePickStrategy -> (Candidate, [Candidate])
    pickCandidate (cand:rest) FirstCandidate = (cand, rest)
    pickCandidate cands ValidWeakCandidate = let 
        res = maximumBy (mappedCompare $ \(Candidate s valids invalids _) -> (- Set.size invalids, - totalQCount s, nontrivCount s)) cands  -- maximize correctness and minimize strength
      in (res, delete res cands)
    pickCandidate cands InitializedWeakCandidate = let 
        res = maximumBy (mappedCompare $ \(Candidate s valids invalids _) -> (nontrivCount s, - totalQCount s)) cands  -- maximize the number of initialized unknowns and minimize strength
      in (res, delete res cands)
      
    pickConstraint (Candidate sol valids invalids _) strategy = case strategy of
      FirstConstraint -> return $ Set.findMin invalids
      SmallSpaceConstraint -> do
        let spaceSize fml = maxValSize quals sol (unknownsOf (leftHandSide fml))
        return $ minimumBy (\x y -> compare (spaceSize x) (spaceSize y)) (Set.toList invalids)
        
    debugOutput cands cand inv modified =
      writeLog 3 (vsep [
        nest 2 $ text "Candidates" <+> parens (pretty $ length cands) $+$ (vsep $ map pretty cands), 
        text "Chosen candidate:" <+> pretty cand,
        text "Invalid Constraint:" <+> pretty inv,
        text "Strengthening:" <+> pretty modified])        
        
hornApplySolution extractAssumptions sol (Binary Implies lhs rhs) = 
    let
     lhs' = applySolution sol lhs
     rhs' = applySolution sol rhs
     assumptions = extractAssumptions lhs' `Set.union` extractAssumptions rhs'
    in Binary Implies (lhs' `andClean` conjunction assumptions) rhs'
    
-- | 'strengthen' @qmap fml sol@: all minimal strengthenings of @sol@ using qualifiers from @qmap@ that make @fml@ valid;
-- | @fml@ must have the form "/\ u_i ==> const".
strengthen :: MonadSMT s => QMap -> ExtractAssumptions -> Formula -> Solution -> FixPointSolver s [Solution]
strengthen qmap extractAssumptions fml@(Binary Implies lhs rhs) sol = do
    let n = maxValSize qmap sol unknowns
    writeLog 3 (text "Instantiated axioms:" $+$ commaSep (map pretty $ Set.toList assumptions))
    let allAssumptions = usedLhsQuals `Set.union` assumptions
    lhsValuations <- optimalValuations n (lhsQuals Set.\\ usedLhsQuals) allAssumptions rhs -- all minimal valid valuations of the whole antecedent
    writeLog 3 (text "Optimal valuations:" $+$ vsep (map pretty lhsValuations))    
    let splitVals vals = nub $ concatMap splitLhsValuation vals 
    pruned <- ifM (asks semanticPrune) 
      (ifM (asks agressivePrune)
        (do
          let pruneAssumptions = if rhs == ffalse then Set.empty else allAssumptions -- TODO: is this dangerous??? the result might not cover the pruned alternatives in a different context!
          valuations' <- pruneValuations (conjunction pruneAssumptions) lhsValuations
          writeLog 3 (text "Pruned valuations:" $+$ vsep (map pretty valuations'))
          return $ splitVals valuations')   -- Prune LHS valuations and then return the splits of only optimal valuations
        (pruneSolutions unknownsList (splitVals lhsValuations)))           -- Prune per-variable
      (return $ splitVals lhsValuations)
    writeLog 3 (text "Diffs:" <+> parens (pretty $ length pruned) $+$ vsep (map pretty pruned))
    return pruned
  where
    unknowns = unknownsOf lhs
    knownConjuncts = conjunctsOf lhs Set.\\ unknowns
    unknownsList = Set.toList unknowns
    lhsQuals = setConcatMap (Set.fromList . lookupQualsSubst qmap) unknowns   -- available qualifiers for the whole antecedent
    usedLhsQuals = setConcatMap (valuation sol) unknowns `Set.union` knownConjuncts      -- already used qualifiers for the whole antecedent
    rhsVars = Set.map varName $ varsOf rhs
    assumptions = setConcatMap extractAssumptions lhsQuals `Set.union`
                  setConcatMap extractAssumptions knownConjuncts `Set.union`
                  extractAssumptions rhs
        
      -- | All possible additional valuations of @u@ that are subsets of $lhsVal@.
    singleUnknownCandidates lhsVal u = let           
          qs = lookupQualsSubst qmap u
          max = lookupQuals qmap maxCount u
          used = valuation sol u
          n = Set.size used
      in Set.toList $ boundedSubsets (max - n) $ (Set.fromList qs Set.\\ used) `Set.intersection` lhsVal
    
      -- | All valid partitions of @lhsVal@ into solutions for multiple unknowns.
    splitLhsValuation :: Valuation -> [Solution]
    splitLhsValuation lhsVal = do
      unknownsVal <- mapM (singleUnknownCandidates lhsVal) unknownsList
      let isValidsplit ss s = Set.unions ss == s && sum (map Set.size ss) == Set.size s
      guard $ isValidsplit unknownsVal lhsVal
      Map.fromListWith Set.union <$> zipWithM unsubst unknownsList unknownsVal

    -- | Given an unknown @[subst]u@ and its valuation @val@, get all possible valuations of @u@
    unsubst :: Formula -> Set Formula -> [(Id, Set Formula)]
    unsubst u@(Unknown s name) val = do
      option <- mapM (unsubstQual u) (Set.toList val)
      return (name, Set.fromList option)
    
    unsubstQual :: Formula -> Formula -> [Formula]
    unsubstQual u@(Unknown s name) qual = [q | q <- lookupQuals qmap qualifiers u, substitute s q == qual]

-- | 'maxValSize' @qmap sol unknowns@: Upper bound on the size of valuations of a conjunction of @unknowns@ when strengthening @sol@ 
maxValSize :: QMap -> Solution -> Set Formula -> Int 
maxValSize qmap sol unknowns = let 
    usedQuals = setConcatMap (valuation sol) unknowns
  in Set.foldl (\n u -> n + lookupQuals qmap maxCount u) 0 unknowns - Set.size usedQuals
  
optimalValuations :: MonadSMT s => Int -> Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
optimalValuations maxSize quals lhs rhs = do
  strategy <- asks optimalValuationsStrategy
  case strategy of
    BFSValuations -> optimalValuationsBFS maxSize quals lhs rhs
    MarcoValuations -> optimalValuationsMarco quals lhs rhs    
    
-- | 'optimalValuations' @quals check@: all smallest subsets of @quals@ for which @check@ returns a solution.
optimalValuationsBFS :: MonadSMT s => Int -> Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
optimalValuationsBFS maxSize quals lhs rhs = map qualsAt <$> filterSubsets (check . qualsAt) (length qualsList)
  where
    qualsList = Set.toList quals
    qualsAt = Set.map (qualsList !!)
    check val = let 
                  n = Set.size val 
                  lhs' = conjunction lhs `andClean` conjunction val                  
      in if 1 <= n && n <= maxSize
          then isValidFml $ lhs' |=>| rhs
          else return False
    
optimalValuationsMarco :: MonadSMT s => Set Formula -> Set Formula -> Formula -> FixPointSolver s [Valuation]
optimalValuationsMarco quals lhs rhs = map Set.fromList <$> lift (allUnsatCores assumption mustHave qualsList)
  where
    qualsList = Set.toList $ Set.filter (\q -> not $ q `Set.member` lhs || fnot q `Set.member` lhs) quals
    fixedLhs = conjunction lhs
    fixedRhs = fnot rhs
    (assumption, mustHave) = if rhs == ffalse then (ftrue, fixedLhs) else (fixedLhs, fixedRhs) -- When RHS is literally false, then inconsistent LHSs are acceptable
                            
-- | 'filterSubsets' @check n@: all minimal subsets of indexes from [0..@n@) that satisfy @check@,
-- where @check@ is monotone (if a set satisfies @check@, then every superset also satisfies @check@);
-- performs breadth-first search.
filterSubsets :: MonadSMT s => (Set Int -> FixPointSolver s Bool) -> Int -> FixPointSolver s [Set Int]
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


-- | 'leastFixPoint' @constraints@: strongest solution for a system of second-order constraints @constraints@.
leastFixPoint :: MonadSMT s => ExtractAssumptions -> [Candidate] -> FixPointSolver s [Candidate]
leastFixPoint _ [] = return []
leastFixPoint extractAssumptions (cand@(Candidate sol _ _ _):rest) = do
    fml <- asks constraintPickStrategy >>= pickConstraint cand
    let (Binary Implies lhs rhs) = fml
    let lhs' = applySolution sol lhs
    let assumptions = extractAssumptions lhs' `Set.union` extractAssumptions (applySolution sol rhs)
    
    let modifiedConstraint = Binary Implies (conjunction $ Set.insert lhs' assumptions) rhs
    
    debugOutput cand fml modifiedConstraint
    solMb' <- weaken modifiedConstraint sol
    case solMb' of
      Nothing -> do
                  writeLog 3 (text "All constraints:" $+$ vsep (map pretty (Set.toList $ validConstraints cand `Set.union` invalidConstraints cand)))
                  leastFixPoint extractAssumptions rest -- No way to weaken this candidate, see if there are more
      Just sol' -> do
                      cand' <- updateCandidate fml cand sol'
                      if (Set.null . invalidConstraints) cand'
                        then return $ cand' : rest -- Solution found
                        else leastFixPoint extractAssumptions (cand' : rest)
  where
    -- | Re-evaluate affected clauses in @valids@ and @otherInvalids@ after solution has been strengthened from @sol@ to @sol'@ in order to fix @fml@
    updateCandidate fml (Candidate sol valids invalids label) sol' = do
      -- let modifiedUnknowns = Map.keysSet $ Map.differenceWith (\v1 v2 -> if v1 == v2 then Nothing else Just v2) sol sol'
      let modifiedUnknowns = posUnknowns $ rightHandSide fml
      let (unaffectedValids, affectedValids) = Set.partition (\fml -> negUnknowns fml `disjoint` modifiedUnknowns) (Set.insert fml valids) -- fml should be re-evaluated if it happens to have the same unknowns also on the right
      let (unaffectedInvalids, affectedInvalids) = Set.partition (\fml -> posUnknowns fml `disjoint` modifiedUnknowns) (Set.delete fml invalids)
      (newValids, newInvalids) <- setPartitionM (isValidFml . hornApplySolution extractAssumptions sol') $ affectedValids `Set.union` affectedInvalids
      return $ Candidate sol' (unaffectedValids `Set.union` newValids) (unaffectedInvalids `Set.union` newInvalids) label
      
      
    pickConstraint (Candidate sol valids invalids _) strategy = case strategy of
      FirstConstraint -> return $ Set.findMin invalids
      SmallSpaceConstraint -> do
        let spaceSize fml = Set.size (unknownsOf (rightHandSide fml))
        return $ minimumBy (\x y -> compare (spaceSize x) (spaceSize y)) (Set.toList invalids)              
        
    debugOutput cand inv modified =
      writeLog 3 (vsep [
        text "Candidate:" <+> pretty cand,
        text "Invalid Constraint:" <+> pretty inv,
        text "Weakening:" <+> pretty modified])        
        
-- | 'weaken' @fml sol@: a minimal weakening of @sol@ that make @fml@ valid;
-- | @fml@ must have the form "const ==> const && /\ Ui" or "const ==> Ui".
weaken :: MonadSMT s => Formula -> Solution -> FixPointSolver s (Maybe Solution)
weaken (Binary Implies lhs (Unknown subst u)) sol = do
  let quals = Set.toList (sol Map.! u)
  quals' <- filterM (\q -> isValidFml (Binary Implies lhs (substitute subst q))) quals  
  writeLog 3 (text "Weakened" <+> text u <+> text "to" <+> pretty quals')
  return (Just $ Map.insert u (Set.fromList quals') sol)
weaken (Binary Implies lhs _) sol = return Nothing
            
-- | 'pruneSolutions' @sols@: eliminate from @sols@ all solutions that are semantically stronger on all unknowns than another solution in @sols@ 
pruneSolutions :: MonadSMT s => [Formula] -> [Solution] -> FixPointSolver s [Solution]
pruneSolutions unknowns solutions = 
  let isSubsumed sol = anyM (\s -> allM (\u -> isValidFml $ (conjunction $ valuation sol u) |=>| (conjunction $ valuation s u)) unknowns)
  in prune isSubsumed solutions
  
-- | 'pruneValuations' @vals@: eliminate from @vals@ all valuations that are semantically stronger than another pValuation in @vals@   
pruneValuations :: MonadSMT s => Formula -> [Valuation] -> FixPointSolver s [Valuation] 
pruneValuations assumption vals = 
  let 
      strictlyImplies ls rs = do
        let l = conjunction ls
        let r = conjunction rs
        res1 <- isValidFml $ (assumption |&| l) |=>| r
        res2 <- isValidFml $ (assumption |&| r) |=>| l
        return $ (res1 && (not res2 || (Set.size ls > Set.size rs)))
      isSubsumed val = anyM (\v -> strictlyImplies val v)
  in prune isSubsumed vals
  
-- | 'pruneQualifiers' @quals@: eliminate logical duplicates from @quals@
pruneQSpace :: MonadSMT s => QSpace -> FixPointSolver s QSpace 
pruneQSpace qSpace = let isSubsumed qual = anyM (\q -> isValidFml $ qual |<=>| q)
  in do
    quals' <- filterM (\q -> ifM (isValidFml q) (return False) (not <$> isValidFml (fnot q))) (qSpace ^. qualifiers) 
    quals <- prune isSubsumed quals'
    return $ set qualifiers quals qSpace
  
-- | 'prune' @isSubsumed xs@ : prune all elements of @xs@ subsumed by another element according to @isSubsumed@  
prune :: MonadSMT s => (a -> [a] -> FixPointSolver s Bool) -> [a] -> FixPointSolver s [a]
prune _ [] = return []
prune isSubsumed (x:xs) = prune' [] x xs
  where
    prune' lefts x [] = ifM (isSubsumed x lefts) (return lefts) (return $ x:lefts)
    prune' lefts x rights@(y:ys) = ifM (isSubsumed x (lefts ++ rights)) (prune' lefts y ys) (prune' (lefts ++ [x]) y ys)
    
-- | 'isValid' @fml@: is @fml@ valid (free variables are implicitly universally quantified)?
isValidFml :: MonadSMT s => Formula -> FixPointSolver s Bool
isValidFml fml = not <$> lift (isSat $ fnot fml)

-- | 'isSat' @fml@: is @fml@ satisfiable (free variables are implicitly existentially quantified)?
isSatFml :: MonadSMT s => Formula -> FixPointSolver s Bool
isSatFml = lift . isSat

writeLog level msg = do
  maxLevel <- asks solverLogLevel
  when (level <= maxLevel) $ traceShow (plain msg) (return ())

