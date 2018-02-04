{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}

module Main where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.Parser
import Synquid.Resolver (resolveDecls)
import Synquid.SolverMonad
import Synquid.HornSolver
import Synquid.TypeConstraintSolver
import Synquid.Explorer
import Synquid.Synthesizer
import Synquid.HtmlOutput
import Synquid.Codegen
import Synquid.Stats

import Control.Monad
import Control.Lens ((^.))
import System.Exit
import System.Console.CmdArgs
import System.Console.ANSI
import System.FilePath
import Data.Char
import Data.Time.Calendar
import Data.Map ((!))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Text.PrettyPrint.ANSI.Leijen (fill, column)

import Data.List.Split

programName = "synquid"
versionName = "0.4"
releaseDate = fromGregorian 2016 8 11

-- | Type-check and synthesize a program, according to command-line arguments
main = do
  res <- cmdArgsRun $ mode
  case res of
    (Synthesis file libs onlyGoals
               appMax scrutineeMax matchMax auxMax fix genPreds explicitMatch unfoldLocals partial incremental consistency memoize symmetry
               lfp bfs
               out_file out_module outFormat resolve
               print_spec print_stats log_) -> do
                  let explorerParams = defaultExplorerParams {
                    _eGuessDepth = appMax,
                    _scrutineeDepth = scrutineeMax,
                    _matchDepth = matchMax,
                    _auxDepth = auxMax,
                    _fixStrategy = fix,
                    _predPolyRecursion = genPreds,
                    _abduceScrutinees = not explicitMatch,
                    _unfoldLocals = unfoldLocals,
                    _partialSolution = partial,
                    _incrementalChecking = incremental,
                    _consistencyChecking = consistency,
                    _useMemoization = memoize,
                    _symmetryReduction = symmetry,
                    _explorerLogLevel = log_
                    }
                  let solverParams = defaultHornSolverParams {
                    isLeastFixpoint = lfp,
                    optimalValuationsStrategy = if bfs then BFSValuations else MarcoValuations,
                    solverLogLevel = log_
                    }
                  let synquidParams = defaultSynquidParams {
                    goalFilter = liftM (splitOn ",") onlyGoals,
                    outputFormat = outFormat,
                    resolveOnly = resolve,
                    showSpec = print_spec,
                    showStats = print_stats
                  }
                  let codegenParams = defaultCodegenParams {
                    filename = out_file,
                    module_ = out_module
                  }
                  runOnFile synquidParams explorerParams solverParams codegenParams file libs

{- Command line arguments -}

deriving instance Typeable FixpointStrategy
deriving instance Data FixpointStrategy
deriving instance Eq FixpointStrategy
deriving instance Show FixpointStrategy

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Redundant bracket" #-}
{-# ANN module "HLint: ignore" #-}

data CommandLineArgs
    = Synthesis {
        -- | Input
        file :: String,
        libs :: [String],
        only :: Maybe String,
        -- | Explorer params
        app_max :: Int,
        scrutinee_max :: Int,
        match_max :: Int,
        aux_max :: Int,
        fix :: FixpointStrategy,
        generalize_preds :: Bool,
        explicit_match :: Bool,
        unfold_locals :: Bool,
        partial :: Bool,
        incremental :: Bool,
        consistency :: Bool,
        memoize :: Bool,
        symmetry :: Bool,
        -- | Solver params
        lfp :: Bool,
        bfs_solver :: Bool,
        -- | Output
        out_file :: Maybe String,
        out_module :: Maybe String,
        output :: OutputFormat,
        resolve :: Bool,
        print_spec :: Bool,
        print_stats :: Bool,
        log_ :: Int
      }
  deriving (Data, Typeable, Show, Eq)

synt = Synthesis {
  file                = ""              &= typFile &= argPos 0,
  libs                = []              &= args &= typ "FILES",
  only                = Nothing         &= typ "GOAL,..." &= help ("Only synthesize the specified functions"),
  app_max             = 3               &= help ("Maximum depth of an application term (default: 3)") &= groupname "Explorer parameters",
  scrutinee_max       = 1               &= help ("Maximum depth of a match scrutinee (default: 1)"),
  match_max           = 2               &= help ("Maximum depth of matches (default: 2)"),
  aux_max             = 1               &= help ("Maximum depth of auxiliary functions (default: 1)") &= name "x",
  fix                 = FirstArgument   &= help (unwords ["What should termination metric for fixpoints be derived from?", show AllArguments, show FirstArgument, show DisableFixpoint, show Nonterminating, "(default:", show FirstArgument, ")"]),
  generalize_preds    = True            &= help ("Make recursion polymorphic in abstract refinements (default: False)"),
  explicit_match      = False           &= help ("Do not abduce match scrutinees (default: False)"),
  unfold_locals       = False           &= help ("Use all variables, as opposed to top-level function arguments only, in match scrutinee abduction (default: False)"),
  partial             = False           &= help ("Generate best-effort partial solutions (default: False)") &= name "p",
  incremental         = True            &= help ("Subtyping checks during bottom-up phase (default: True)"),
  consistency         = True            &= help ("Check incomplete application types for consistency (default: True)"),
  memoize             = False           &= help ("Use memoization (default: False)") &= name "z",
  symmetry            = False           &= help ("Use symmetry reductions (default: False)") &= name "s",
  lfp                 = False           &= help ("Use least fixpoint solver (only works for type checking, default: False)") &= groupname "Solver parameters",
  bfs_solver          = False           &= help ("Use BFS instead of MARCO to solve second-order constraints (default: False)"),
  resolve             = False           &= help ("Resolve only; no type checking or synthesis (default: False)"),
  out_file            = Nothing         &= help ("Generate Haskell output file (default: none)") &= typFile &= name "o" &= opt "" &= groupname "Output",
  out_module          = Nothing         &= help ("Name of Haskell module to generate (default: from file name)") &= typ "Name",
  output              = defaultFormat   &= help ("Output format: Plain, Ansi or Html (default: " ++ show defaultFormat ++ ")") &= typ "FORMAT",
  print_spec          = True            &= help ("Show specification of each synthesis goal (default: True)"),
  print_stats         = False           &= help ("Show specification and solution size (default: False)"),
  log_                = 0               &= help ("Logger verboseness level (default: 0)") &= name "l"
  } &= auto &= help "Synthesize goals specified in the input file"
    where
      defaultFormat = outputFormat defaultSynquidParams


mode = cmdArgsMode $ synt &=
  help "Synquid program synthesizer" &=
  program programName &=
  summary (programName ++ " v" ++ versionName ++ ", " ++ showGregorian releaseDate)

-- | Parameters for template exploration
defaultExplorerParams = ExplorerParams {
  _eGuessDepth = 3,
  _scrutineeDepth = 1,
  _matchDepth = 2,
  _auxDepth = 1,
  _fixStrategy = AllArguments,
  _polyRecursion = True,
  _predPolyRecursion = False,
  _abduceScrutinees = True,
  _unfoldLocals = False,
  _partialSolution = False,
  _incrementalChecking = True,
  _consistencyChecking = False,
  _splitMeasures = True,
  _useMemoization = False,
  _symmetryReduction = False,
  _context = id,
  _sourcePos = noPos,
  _explorerLogLevel = 0
}

-- | Parameters for constraint solving
defaultHornSolverParams = HornSolverParams {
  pruneQuals = True,
  isLeastFixpoint = False,
  optimalValuationsStrategy = MarcoValuations,
  semanticPrune = True,
  agressivePrune = True,
  candidatePickStrategy = InitializedWeakCandidate,
  constraintPickStrategy = SmallSpaceConstraint,
  solverLogLevel = 0
}

-- | Output format
data OutputFormat = Plain -- ^ Plain text
  | Ansi -- ^ Text with ANSI-terminal special characters
  | Html -- ^ HTML
  deriving (Typeable, Data, Eq, Show)

-- | 'printDoc' @format doc@ : print @doc@ to the console using @format@
printDoc :: OutputFormat -> Doc -> IO()
printDoc Plain doc = putDoc (plain doc) >> putStr "\n"
printDoc Ansi doc = putDoc doc >> putStr "\n"
printDoc Html doc = putStr (showDocHtml (renderPretty 0.4 100 doc))

-- | Parameters of the synthesis
data SynquidParams = SynquidParams {
  goalFilter :: Maybe [String],
  outputFormat :: OutputFormat,                -- ^ Output format
  resolveOnly :: Bool,                         -- ^ Stop after resolution step
  repairPolicies :: Bool,
  verifyOnly :: Bool,
  showSpec :: Bool,                            -- ^ Print specification for every synthesis goal
  showStats :: Bool                            -- ^ Print specification and solution size
}

defaultSynquidParams = SynquidParams {
  goalFilter = Nothing,
  outputFormat = Plain,
  resolveOnly = False,
  repairPolicies = False,
  verifyOnly = False,
  showSpec = True,
  showStats = False
}

-- | Parameters for code extraction and Haskell output
data CodegenParams = CodegenParams {
  filename :: Maybe String,               -- ^ Output filename (of Haskell code)
  module_ :: Maybe String,                -- ^ Generated module name
  imports :: Map.Map String [Declaration] -- ^ Modules to depend on
}

defaultCodegenParams = CodegenParams {
  filename = Nothing,
  module_ = Nothing,
  imports = Map.empty
}

fillinCodegenParams fn libs p = (fillinCodegenNames fn p) { imports = Map.mapKeys idfy libs }

-- | figures out output filename from module name or vise versa
fillinCodegenNames f p@(CodegenParams (Just "") _ _) = fillinCodegenNames f $ p { filename = Just (f -<.> ".hs") }
fillinCodegenNames _ p@(CodegenParams (Just "-") Nothing _) =                 p { module_ = Just "Synthed" }
fillinCodegenNames _ p@(CodegenParams (Just filename) Nothing _) =            p { module_ = Just $ idfy filename }
fillinCodegenNames _ p@(CodegenParams Nothing (Just module_) _) =             p { filename = Just (module_ <.> ".hs") }
fillinCodegenNames _ p = p

-- | E.g., "out/User-Module.hs" ---> "UserModule"
idfy = filter isAlphaNum . dropExtension . takeFileName

codegen params results = case params of
  CodegenParams {filename = Just filePath, module_ = Just moduleName, imports = imports} ->
      extractModule filePath moduleName results imports
  _ -> return ()

collectLibDecls libs declsByFile =
  Map.filterWithKey (\k _ -> k `elem` libs) $ Map.fromList declsByFile


-- | Parse and resolve file, then synthesize the specified goals
runOnFile :: SynquidParams -> ExplorerParams -> HornSolverParams -> CodegenParams
                           -> String -> [String] -> IO ()
runOnFile synquidParams explorerParams solverParams codegenParams file libs = do
  declsByFile <- parseFromFiles (libs ++ [file])
  let decls = concat $ map snd declsByFile
  case resolveDecls decls of
    Left resolutionError -> (pdoc $ pretty resolutionError) >> pdoc empty >> exitFailure
    Right (goals, cquals, tquals) -> when (not $ resolveOnly synquidParams) $ do
      results <- mapM (synthesizeGoal cquals tquals) (requested goals)
      when (not (null results) && showStats synquidParams) $ printStats results declsByFile
      -- Generate output if requested
      let libsWithDecls = collectLibDecls libs declsByFile
      codegen (fillinCodegenParams file libsWithDecls codegenParams) (map fst results)
  where
    parseFromFiles [] = return []
    parseFromFiles (file:rest) = do
      parseResult <- parseFromFile parseProgram file
      case parseResult of
        Left parseErr -> (pdoc $ pretty $ toErrorMessage parseErr) >> pdoc empty >> exitFailure
        -- Right ast -> print $ vsep $ map pretty ast
        Right decls -> let decls' = if null rest then decls else filter (not . isSynthesisGoal) decls in -- Remove implementations from libraries
          ((file, decls') :) <$> parseFromFiles rest
    requested goals = case goalFilter synquidParams of
      Just filt -> filter (\goal -> gName goal `elem` filt) goals
      _ -> goals
    pdoc = printDoc (outputFormat synquidParams)
    synthesizeGoal cquals tquals goal = do
      when ((gSynthesize goal) && (showSpec synquidParams)) $ pdoc (prettySpec goal)
      -- print empty
      -- print $ vMapDoc pretty pretty (allSymbols $ gEnvironment goal)
      -- print $ pretty (gSpec goal)
      -- print $ vMapDoc pretty pretty (_measures $ gEnvironment goal)
      (mProg, stats) <- synthesize explorerParams solverParams goal cquals tquals
      case mProg of
        Left typeErr -> pdoc (pretty typeErr) >> pdoc empty >> exitFailure
        Right prog -> do
          when (gSynthesize goal) $ pdoc (prettySolution goal prog)
          pdoc empty
          return ((goal, prog), stats)
    printStats results declsByFile = do
      let env = gEnvironment (fst $ fst $ head results)
      let measureCount = Map.size $ _measures $ env
      let namesOfConstants decls = mapMaybe (\decl ->
           case decl of
             Pos { node = FuncDecl name _ } -> Just name
             _ -> Nothing
           ) decls
      let totalSizeOf = sum . map (typeNodeCount . toMonotype .unresolvedType env)
      let policySize = Map.fromList $ map (\(file, decls) -> (file, totalSizeOf $ namesOfConstants decls)) declsByFile
      let getStatsFor ((goal, prog), stats) =
             StatsRow
             (gName goal)
             (typeNodeCount $ toMonotype $ unresolvedSpec goal)
             (programNodeCount $ gImpl goal)   -- size of implementation template (before synthesis/repair)
             (programNodeCount prog)           -- size of generated solution
             (stats ! TypeCheck) (stats ! Repair) (stats ! Recheck) (sum $ Map.elems stats)  -- time measurements
      let perResult = map getStatsFor results
      let specSize = sum $ map (typeNodeCount . toMonotype . unresolvedSpec . fst . fst) results
      let solutionSize = sum $ map (programNodeCount . snd . fst) results
      pdoc $ vsep $ [
                parens (text "Goals:" <+> pretty (length results)),
                parens (text "Measures:" <+> pretty measureCount)] ++
              if repairPolicies synquidParams
                then [
                  parens (text "Policy size:" <+> (text $ show policySize)),
                  statsTable perResult]
                else [
                  parens (text "Spec size:" <+> pretty specSize),
                  parens (text "Solution size:" <+> pretty solutionSize)
                ] ++
              [empty]
