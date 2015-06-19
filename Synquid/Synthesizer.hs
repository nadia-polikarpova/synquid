-- | Top-level synthesizer interface
module Synquid.Synthesizer (
  synthesize,
  (|++|)
) where

import Synquid.Util
import Synquid.Logic
import Synquid.Solver
import Synquid.SMTSolver
import Synquid.Z3
import Synquid.Program
import Synquid.Pretty
import Synquid.ConstraintGenerator
import Synquid.TemplateGenerator

import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
import Control.Monad.Stream
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Applicative
import Control.Lens
import System.IO.Unsafe

-- | 'synthesize' @templGenParam consGenParams solverParams env typ templ cq tq@ : synthesize a program that has a type @typ@ 
-- in the typing environment @env@ and follows template @templ@,
-- using conditional qualifiers @cquals@ and type qualifiers @tquals@,
-- with parameters for template generation, constraint generation, and constraint solving @templGenParam@ @consGenParams@ @solverParams@ respectively
synthesize :: TemplGenParams -> ConsGenParams -> SolverParams -> Environment -> RType -> Template -> [Formula] -> [Formula] -> IO (Maybe SimpleProgram)
synthesize templGenParams consGenParams solverParams env typ templ cquals tquals = exploreTemplates2
  where
    -- | Qualifier generator for conditionals
    condQualsGen = toSpace . foldl (|++|) (const []) (map extractCondQGen cquals)
    
    -- | Qualifier generator for types
    typeQualsGen = toSpace . foldl (|++|) (extractQGenFromType typ) (map extractTypeQGen tquals)
    
    -- | All argument types of a function type
    allArgTypes (ScalarT _ _) = Set.empty
    allArgTypes (FunctionT _ tArg tRes) = Set.insert tArg $ allArgTypes tRes    
    
    -- | Type shapes leafs can have in a template
    leafShapes = let 
        res = shape $ typ
        symbols = Map.keysSet (env ^. symbolsOfShape)
        cons = [s | (s, names) <- Map.toList (env ^. symbolsOfShape), not $ Set.null $ names `Set.intersection` (env ^. constructors)]
      in Set.insert res $                             -- result type (because of recursion)
         symbols `Set.union`                          -- type shapes of components
         (Set.unions $ map allArgTypes (res : cons))  -- all argument types of the result type (for lambda arguments) and of constructors (for match bindings)
    
    -- | Interleave template exploration and constraint solving
    exploreTemplates1 :: IO (Maybe SimpleProgram)
    exploreTemplates1 = return . listToMaybe . toList $ do
      templ' <- exapansions templGenParams leafShapes templ
      case resForTemplate consGenParams solverParams env typ condQualsGen typeQualsGen templ' of
        Nothing -> mzero
        Just prog -> return prog
        
    -- | First explore all templates, then start solving constraints; this has the benefit of only creating an SMT solver once
    exploreTemplates2 :: IO (Maybe SimpleProgram)
    exploreTemplates2 = do
      let templs = toList $ exapansions templGenParams leafShapes templ
      evalZ3State $ runMaybeT $ msum $ map (synthesizeForTemplate consGenParams solverParams env typ condQualsGen typeQualsGen) templs  

-- | Pure wrapper around 'synthesizeForTemplate'      
resForTemplate :: ConsGenParams -> SolverParams -> Environment -> RType -> QualsGen -> QualsGen -> Template -> Maybe SimpleProgram
resForTemplate consGenParams solverParams env typ cq tq templ = unsafePerformIO $ evalZ3State $ runMaybeT $ synthesizeForTemplate consGenParams solverParams env typ cq tq templ
      
-- | Synthesize a solution for a given fully expanded template, if it exisits
synthesizeForTemplate :: ConsGenParams -> SolverParams -> Environment -> RType -> QualsGen -> QualsGen -> Template -> MaybeT Z3State SimpleProgram
synthesizeForTemplate consGenParams solverParams env typ cq tq templ = do
  let (clauses, qmap, p) = genConstraints consGenParams cq tq env typ templ
  lift initSolver
  mSol <- lift $ solveWithParams solverParams qmap clauses (candidateDoc p)
  case mSol of
    Nothing -> mzero
    Just sol -> extract sol p
    
{- Qualifier Generators -}

(|++|) gen gen' = \symbs -> nub $ gen symbs ++ gen' symbs
infixr 5  |++|

toSpace quals = QSpace quals (length quals)

-- | 'extractQGenFromType' @qual@: qualifier generator that treats free variables of @qual@ except the value variable as parameters
extractTypeQGen qual (val : syms) = let vars = varsOf qual in
    if Set.member val vars
      then allSubstitutions qual (Set.toList $ Set.delete val (varsOf qual)) syms -- val has correct base type
      else []                                                                     -- val has wrong base type

-- | 'extractCondQGen' @qual@: qualifier generator that treats free variables of @qual@ as parameters
extractCondQGen qual syms = allSubstitutions qual (Set.toList $ varsOf qual) syms

-- | 'extractQGenFromType' @t@: qualifier generator that extracts all conjuncts from @t@ and treats their free variables as parameters
extractQGenFromType :: RType -> [Formula] -> [Formula]
extractQGenFromType (ScalarT _ fml) syms = let fs = Set.toList $ conjunctsOf fml in concatMap (flip extractTypeQGen syms) fs
extractQGenFromType (FunctionT _ tArg tRes) syms = extractQGenFromType tArg syms ++ extractQGenFromType tRes syms    

-- | 'allSubstitutions' @qual vars syms@: all well-types substitutions of @syms@ for @vars@ in a qualifier @qual@
allSubstitutions (BoolLit True) _ _ = []
allSubstitutions qual vars syms = do
  let pickSubstForVar var = [Map.singleton (varName var) v | v <- syms, varType v == varType var]
  subst <- Map.unions <$> mapM pickSubstForVar vars
  guard $ Set.size (Set.fromList $ Map.elems subst) == Map.size subst -- Only use substitutions with unique values (qualifiers are unlikely to have duplicate variables)      
  return $ substitute subst qual
    
