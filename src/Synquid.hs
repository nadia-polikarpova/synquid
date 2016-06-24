{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}

module Main where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.Parser (parseFromFile, parseProgram, toErrorMessage)
import Synquid.Resolver (resolveDecls)
import Synquid.SolverMonad
import Synquid.HornSolver
import Synquid.TypeConstraintSolver
import Synquid.Explorer
import Synquid.Synthesizer
import Synquid.HtmlOutput
import Synquid.Codegen

import Control.Monad
import System.Exit
import System.Console.CmdArgs
import System.Console.ANSI
import System.FilePath
import Data.Char
import Data.Time.Calendar
import qualified Data.Map as Map

programName = "synquid"
versionName = "0.3"
releaseDate = fromGregorian 2016 3 8

-- | Type-check and synthesize a program, according to command-line arguments
main = do
  (CommandLineArgs file
                   appMax
                   scrutineeMax
                   matchMax
                   auxMax
                   fix
                   genPreds
                   explicitMatch
                   unfoldLocals
                   partial
                   incremental
                   consistency
                   memoize
                   symmetry
                   lfp
                   bfs
                   out_file
                   out_module
                   outFormat
                   resolve
                   repair
                   print_spec
                   print_stats
                   log_) <- cmdArgs cla
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
    outputFormat = outFormat,
    resolveOnly = resolve,
    repairPolicies = repair,
    showSpec = print_spec,
    showStats = print_stats
  }
  let codegenParams = defaultCodegenParams {
    filename = out_file,
    module_ = out_module
  }
  runOnFile synquidParams explorerParams solverParams codegenParams file

{- Command line arguments -}

deriving instance Typeable FixpointStrategy
deriving instance Data FixpointStrategy
deriving instance Eq FixpointStrategy
deriving instance Show FixpointStrategy

data CommandLineArgs
    = CommandLineArgs {
        -- | Input
        file :: String,
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
        repair :: Bool,
        print_spec :: Bool,
        print_stats :: Bool,
        log_ :: Int
      }
  deriving (Data, Typeable, Show, Eq)

cla = CommandLineArgs {
  file                = ""              &= typFile &= argPos 0,
  app_max             = 3               &= help ("Maximum depth of an application term (default: 3)") &= groupname "Explorer parameters",
  scrutinee_max       = 1               &= help ("Maximum depth of a match scrutinee (default: 1)"),
  match_max           = 2               &= help ("Maximum depth of matches (default: 2)"),
  aux_max             = 1               &= help ("Maximum depth of auxiliary functions (default: 1)") &= name "x",
  fix                 = FirstArgument   &= help (unwords ["What should termination metric for fixpoints be derived from?", show AllArguments, show FirstArgument, show DisableFixpoint, "(default:", show FirstArgument, ")"]),
  generalize_preds    = True            &= help ("Make recursion polymorphic in abstract refinements (default: False)"),
  explicit_match      = False           &= help ("Do not abduce match scrutinees (default: False)"),
  unfold_locals       = False           &= help ("Use all variables, as opposed to top-level function arguments only, in match scrutinee abduction (default: False)"),
  partial             = False           &= help ("Generate best-effort partial solutions (default: False)") &= name "p",
  incremental         = True            &= help ("Subtyping checks during bottom-up phase (default: True)"),
  consistency         = False           &= help ("Check incomplete application types for consistency (default: False)"),
  memoize             = False           &= help ("Use memoization (default: False)") &= name "z",
  symmetry            = False           &= help ("Use symmetry reductions (default: False)") &= name "s",
  lfp                 = False           &= help ("Use least fixpoint solver (only works for type checking, default: False)") &= groupname "Solver parameters",
  bfs_solver          = False           &= help ("Use BFS instead of MARCO to solve second-order constraints (default: False)"),
  resolve             = False           &= help ("Resolve only; no type checking or synthesis (default: False)"),
  repair              = False           &= help ("Policy repair mode (default: False)") &= name "r",
  out_file            = Nothing         &= help ("Generate Haskell output file (default: none)") &= typFile &= name "o" &= opt "" &= groupname "Output",
  out_module          = Nothing         &= help ("Name of Haskell module to generate (default: from file name)") &= typ "Name",
  output              = defaultFormat   &= help ("Output format: Plain, Ansi or Html (default: " ++ show defaultFormat ++ ")") &= typ "FORMAT",
  print_spec          = True            &= help ("Show specification of each synthesis goal (default: True)"),
  print_stats         = False           &= help ("Show specification and solution size (default: False)"),
  log_                = 0               &= help ("Logger verboseness level (default: 0)") &= name "l"
  } &= help "Synthesize goals specified in the input file" &= program programName &= summary (programName ++ " v" ++ versionName ++ ", " ++ showGregorian releaseDate)
    where
      defaultFormat = outputFormat defaultSynquidParams

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
  _consistencyChecking = True,
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
  semanticPrune = False,
  agressivePrune = False,
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
  outputFormat :: OutputFormat,                -- ^ Output format
  resolveOnly :: Bool,                         -- ^ Stop after resolution step
  repairPolicies :: Bool,
  showSpec :: Bool,                            -- ^ Print specification for every synthesis goal
  showStats :: Bool                            -- ^ Print specification and solution size
}

defaultSynquidParams = SynquidParams {
  outputFormat = Plain,
  resolveOnly = False,
  repairPolicies = False,
  showSpec = True,
  showStats = False
}

-- | Parameters for code extraction and Haskell output
data CodegenParams = CodegenParams {
  filename :: Maybe String,
  module_ :: Maybe String
} deriving (Show)

defaultCodegenParams = CodegenParams {
  filename = Nothing,
  module_ = Nothing
}

{- figures out output filename from module name or vise versa -}
fillinCodegenParams f p@(CodegenParams (Just "") _) = fillinCodegenParams f $ p { filename = Just (f -<.> ".hs") }
fillinCodegenParams _ p@(CodegenParams (Just "-") Nothing) =                  p { module_ = Just "Synthed" }
fillinCodegenParams _ p@(CodegenParams (Just filename) Nothing) =             p { module_ = Just $ idfy filename }
fillinCodegenParams _ p@(CodegenParams Nothing (Just module_)) =              p { filename = Just (module_ <.> ".hs") }
fillinCodegenParams _ p = p

idfy = filter isAlphaNum . dropExtension . takeFileName

codegen params results = case params of
  CodegenParams {filename = Just filePath, module_ = Just moduleName} ->
      extractModule filePath moduleName results
  _ -> return ()

-- | Parse and resolve file, then synthesize the specified goals
runOnFile :: SynquidParams -> ExplorerParams -> HornSolverParams -> CodegenParams
                           -> String -> IO ()
runOnFile synquidParams explorerParams solverParams codegenParams file = do
  parseResult <- parseFromFile parseProgram file
  case parseResult of
    Left parseErr -> (pdoc $ pretty $ toErrorMessage parseErr) >> pdoc empty >> exitFailure
    -- Right ast -> print $ vsep $ map pretty ast
    Right decls -> case resolveDecls decls of
      Left resolutionError -> (pdoc $ pretty resolutionError) >> pdoc empty >> exitFailure
      Right (goals, cquals, tquals) -> when (not $ resolveOnly synquidParams) $ do
        results <- mapM (synthesizeGoal cquals tquals) goals
        when (not (null results) && showStats synquidParams) $ printStats results
        -- Generate output if requested
        codegen (fillinCodegenParams file codegenParams) results
  where
    pdoc = printDoc (outputFormat synquidParams)
    synthesizeGoal cquals tquals goal = do
      when (showSpec synquidParams) $ pdoc (prettySpec goal)
      -- print empty
      -- print $ vMapDoc pretty pretty (allSymbols $ gEnvironment goal)
      -- print $ pretty (gSpec goal)
      -- print $ vMapDoc pretty pretty (_measures $ gEnvironment goal)
      mProg <- if repairPolicies synquidParams  
                then policyRepair explorerParams solverParams { isLeastFixpoint = True} goal cquals tquals
                else synthesize explorerParams solverParams goal cquals tquals
      case mProg of
        Left typeErr -> pdoc (pretty typeErr) >> pdoc empty >> exitFailure
        Right prog -> do
          pdoc (prettySolution goal prog)
          pdoc empty
          return (goal, prog)
    printStats results = do
      let measureCount = Map.size $ _measures $ gEnvironment (fst $ head results)
      let specSize = sum $ map (typeNodeCount . toMonotype . unresolvedSpec . fst) results
      let solutuionSize = sum $ map (programNodeCount . snd) results
      pdoc $ vsep [
              parens (text "Goals:" <+> pretty (length results)),
              parens (text "Measures:" <+> pretty measureCount),
              parens (text "Spec size:" <+> pretty specSize),
              parens (text "Solution size:" <+> pretty solutuionSize),
              empty
              ]
