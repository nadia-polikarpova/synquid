{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}

module Main where

import Synquid.Logic
import Synquid.Program
import Synquid.Pretty
import Synquid.Parser (parseFromFile, parseProgram)
import Synquid.Resolver (resolveDecls)
import Synquid.SolverMonad
import Synquid.HornSolver
import Synquid.TypeConstraintSolver
import Synquid.Explorer
import Synquid.Synthesizer
import Synquid.HtmlOutput

import Control.Monad
import System.Exit
import System.Console.CmdArgs
import System.Console.ANSI
import Data.Time.Calendar
import Data.Map (size, elems, keys)

programName = "synquid"
versionName = "0.2"
releaseDate = fromGregorian 2015 11 20

-- | Execute or test a Boogie program, according to command-line arguments
main = do
  (CommandLineArgs file 
                   appMax 
                   scrutineeMax 
                   matchMax 
                   auxMax
                   fix
                   genPreds
                   hideScr 
                   explicitMatch
                   unfoldLocals
                   partial
                   incremental
                   consistency 
                   log_ 
                   useMemoization 
                   bfs
                   outFormat
                   print_spec
                   print_spec_size
                   print_solution_size) <- cmdArgs cla
  let explorerParams = defaultExplorerParams {
    _eGuessDepth = appMax,
    _scrutineeDepth = scrutineeMax,
    _matchDepth = matchMax,
    _auxDepth = auxMax,
    _fixStrategy = fix,
    _predPolyRecursion = genPreds,
    _hideScrutinees = hideScr,
    _abduceScrutinees = not explicitMatch,
    _unfoldLocals = unfoldLocals,
    _partialSolution = partial,
    _incrementalChecking = incremental,
    _consistencyChecking = consistency,
    _useMemoization = useMemoization,
    _explorerLogLevel = log_
    }
  let solverParams = defaultHornSolverParams {
    optimalValuationsStrategy = if bfs then BFSValuations else MarcoValuations,
    solverLogLevel = log_
    }
  let synquidParams = defaultSynquidParams {
    outputFormat = outFormat,
    showSpec = print_spec,
    showSpecSize = print_spec_size,
    showSolutionSize = print_solution_size
  }
  runOnFile synquidParams explorerParams solverParams file

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
        hide_scrutinees :: Bool,
        explicit_match :: Bool,
        unfold_locals :: Bool,
        partial :: Bool,
        incremental :: Bool,
        consistency :: Bool,
        log_ :: Int,
        use_memoization :: Bool,
        -- | Solver params
        bfs_solver :: Bool,
        -- | Output
        output :: OutputFormat,
        print_spec :: Bool,
        print_spec_size :: Bool,
        print_solution_size :: Bool
      }
  deriving (Data, Typeable, Show, Eq)

cla = CommandLineArgs {
  file                = ""              &= typFile &= argPos 0,
  app_max             = 3               &= help ("Maximum depth of an application term (default: 3)"),
  scrutinee_max       = 1               &= help ("Maximum depth of a match scrutinee (default: 1)"),
  match_max           = 2               &= help ("Maximum depth of matches (default: 2)"),
  aux_max             = 1               &= help ("Maximum depth of auxiliary functions (default: 1)") &= name "x",
  fix                 = AllArguments    &= help (unwords ["What should termination metric for fixpoints be derived from?", show AllArguments, show FirstArgument, show DisableFixpoint, "(default:", show AllArguments, ")"]),
  generalize_preds    = False           &= help ("Make recursion polymorphic in abstract refinements (default: False)"),
  hide_scrutinees     = False           &= help ("Hide scrutinized expressions from the environment (default: False)"),
  explicit_match      = False           &= help ("Do not abduce match scrutinees (default: False)"),
  unfold_locals       = False           &= help ("Use all variables, as opposed to top-level function arguments only, in match scrutinee abduction (default: False)") &= name "n",
  partial             = False           &= help ("Generate best-effort partial solutions (default: False)"),
  incremental         = True            &= help ("Subtyping checks during bottom-up phase (default: True)"),
  consistency         = True            &= help ("Check incomplete application types for consistency (default: True)"),
  log_                = 0               &= help ("Logger verboseness level (default: 0)"),
  use_memoization     = False           &= help ("Use memoization (default: False)") &= name "u",
  bfs_solver          = False           &= help ("Use BFS instead of MARCO to solve second-order constraints (default: False)"),
  output              = defaultFormat   &= help ("Output format: Plain, Ansi or Html (default: " ++ show defaultFormat ++ ")"),
  print_spec          = True            &= help ("Show specification of each synthesis goal (default: True)"),
  print_spec_size     = False           &= help ("Show specification size (default: False)"),
  print_solution_size = False           &= help ("Show solution size (default: False)")
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
  _hideScrutinees = False,
  _abduceScrutinees = True,
  _unfoldLocals = False,
  _partialSolution = False,
  _incrementalChecking = True,
  _consistencyChecking = True,
  _useMemoization = False,
  _context = id,
  _explorerLogLevel = 0
}

-- | Parameters for constraint solving
defaultHornSolverParams = HornSolverParams {
  pruneQuals = True,
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
  outputFormat :: OutputFormat,                -- ^ Output format
  showSpec :: Bool,                            -- ^ Print specification for every synthesis goal 
  showSpecSize :: Bool,                        -- ^ Print specification size
  showSolutionSize :: Bool                     -- ^ Print solution size
}

defaultSynquidParams = SynquidParams {
  outputFormat = Plain,
  showSpec = True,
  showSpecSize = False,
  showSolutionSize = False
}

-- | Parse and resolve file, then synthesize the specified goals
runOnFile :: SynquidParams -> ExplorerParams -> HornSolverParams -> String -> IO ()
runOnFile synquidParams explorerParams solverParams file = do
  parseResult <- parseFromFile parseProgram file
  case parseResult of
    Left parseErr -> (pdoc $ errorDoc $ text (show parseErr)) >> exitFailure
    -- Right ast -> print $ vsep $ map pretty ast
    Right decls -> case resolveDecls decls of
      Left resolutionError -> (pdoc $ errorDoc $ text resolutionError) >> exitFailure
      Right (goals, cquals, tquals) -> mapM_ (synthesizeGoal cquals tquals) goals
  where
    pdoc = printDoc (outputFormat synquidParams)
    synthesizeGoal cquals tquals goal = do
      when (showSpec synquidParams) $ pdoc (prettySpec goal)
      -- print empty
      -- print $ vMapDoc pretty pretty (allSymbols $ gEnvironment goal)
      mProg <- synthesize explorerParams solverParams goal cquals tquals
      case mProg of
        Left err -> pdoc err >> exitFailure
        Right prog -> do
          pdoc (prettySolution goal prog)
          when (showSolutionSize synquidParams) $ pdoc (parens (text "Size:" <+> pretty (programNodeCount prog)))
          when (showSpecSize synquidParams) $ pdoc specSizeDoc
          where
            specSizeDoc = let allConstructors = concatMap _constructors $ elems $ _datatypes $ gEnvironment goal in
                parens (text "Spec size:" <+> pretty (typeNodeCount $ toMonotype $ gSpec goal)) $+$
                  parens (text "#measures:" <+> pretty (size $ _measures $ gEnvironment goal)) $+$
                  parens (text "#components:" <+>
                    pretty (length $ filter (not . flip elem allConstructors) $ keys $ allSymbols $ gEnvironment goal)) -- we only solve one goal
      pdoc empty
      
