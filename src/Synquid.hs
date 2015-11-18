{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}

module Main where

import Synquid.Logic
import Synquid.Program
import Synquid.Pretty
import qualified Synquid.Parser as Parser (parseProgram)
import qualified Synquid.Resolver as Resolver (resolveProgramAst)
import Synquid.Solver
import Synquid.Explorer
import Synquid.Synthesizer

import System.Exit
import System.Console.CmdArgs
import Data.Time.Calendar
import Text.ParserCombinators.Parsec (parse, parseFromFile)
import Data.Map (size)

programName = "synquid"
versionName = "0.2"
releaseDate = fromGregorian 2015 11 20

-- | Execute or test a Boogie program, according to command-line arguments
main = do
  (CommandLineArgs file appMax scrutineeMax matchMax fix hideScr explicitMatch
    consistency log_ useMemoization print_solution_size print_spec_info) <- cmdArgs cla
  let explorerParams = defaultExplorerParams {
    _eGuessDepth = appMax,
    _scrutineeDepth = scrutineeMax,
    _matchDepth = matchMax,
    _fixStrategy = fix,
    _hideScrutinees = hideScr,
    _abduceScrutinees = not explicitMatch,
    _consistencyChecking = consistency,
    _explorerLogLevel = log_,
    _useMemoization = useMemoization
    }
  let solverParams = defaultSolverParams {
    solverLogLevel = log_
    }
  let synquidParams = defaultSynquidParams {
    showSolutionSize = print_solution_size,
    showSpecInfo = print_spec_info
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
        fix :: FixpointStrategy,
        hide_scrutinees :: Bool,
        explicit_match :: Bool,
        consistency :: Bool,
        log_ :: Int,
        use_memoization :: Bool,
        print_solution_size :: Bool,
        print_spec_info :: Bool
      }
  deriving (Data, Typeable, Show, Eq)

cla = CommandLineArgs {
  file            = ""              &= typFile &= argPos 0,
  app_max         = 3               &= help ("Maximum depth of an application term (default: 3)"),
  scrutinee_max   = 1               &= help ("Maximum depth of a match scrutinee (default: 0)"),
  match_max       = 2               &= help ("Maximum number of a matches (default: 2)"),
  fix             = AllArguments    &= help (unwords ["What should termination metric for fixpoints be derived from?", show AllArguments, show FirstArgument, show DisableFixpoint, "(default:", show AllArguments, ")"]),
  hide_scrutinees = False           &= help ("Hide scrutinized expressions from the evironment (default: False)"),
  explicit_match  = False           &= help ("Do not abduce match scrutinees (default: False)"),
  consistency     = True            &= help ("Check incomplete application types for consistency (default: True)"),
  log_            = 0               &= help ("Logger verboseness level (default: 0)"),
  use_memoization = False           &= help ("Use memoization (default: False)"),
  print_solution_size = False       &= help ("Show size of the synthesized solution (default: False)"),
  print_spec_info = False       &= help ("Show information about the given synthesis problem (default: False)")
  } &= help "Synthesize goals specified in the input file" &= program programName &= summary (programName ++ " v" ++ versionName ++ ", " ++ showGregorian releaseDate)

-- | Parameters for template exploration
defaultExplorerParams = ExplorerParams {
  _eGuessDepth = 3,
  _scrutineeDepth = 1,
  _matchDepth = 2,
  _condDepth = 1,
  _fixStrategy = AllArguments,
  _polyRecursion = True,
  _hideScrutinees = False,
  _abduceScrutinees = True,
  _consistencyChecking = True,
  _condQualsGen = undefined,
  _matchQualsGen = undefined,
  _typeQualsGen = undefined,
  _context = id,
  _explorerLogLevel = 1,
  _useMemoization = False
}

-- | Parameters for constraint solving
defaultSolverParams = SolverParams {
  pruneQuals = True,
  optimalValuationsStrategy = MarcoValuations,
  semanticPrune = True,
  agressivePrune = True,
  candidatePickStrategy = InitializedWeakCandidate,
  constraintPickStrategy = SmallSpaceConstraint,
  candDoc = const empty,
  solverLogLevel = 1
}

-- | Parameters of the synthesis
data SynquidParams = SynquidParams {
  showSolutionSize :: Bool,                    -- ^ Print synthesized term size
  showSpecInfo :: Bool                         -- ^ Print information about speficiation
}

defaultSynquidParams = SynquidParams {
  showSolutionSize = False,
  showSpecInfo = False
}

-- | Parse and resolve file, then synthesize the specified goals
runOnFile :: SynquidParams -> ExplorerParams -> SolverParams -> String -> IO ()
runOnFile synquidParams explorerParams solverParams file = do
  parseResult <- parseFromFile Parser.parseProgram file
  case parseResult of
    Left parseErr -> (putStr $ show parseErr) >> exitFailure
    -- Right ast -> print $ vsep $ map pretty ast
    Right ast -> case Resolver.resolveProgramAst ast of
      Left resolutionError -> (putStr resolutionError) >> exitFailure
      Right (goals, cquals, tquals) -> mapM_ (synthesizeGoal cquals tquals) goals
  where
    synthesizeGoal cquals tquals goal = do
      print $ text (gName goal) <+> text "::" <+> pretty (gSpec goal)
      -- print empty
      -- print $ vMapDoc pretty pretty (allSymbols $ gEnvironment goal)
      mProg <- synthesize explorerParams solverParams goal cquals tquals
      case mProg of
        Nothing -> putStr "No Solution" >> exitFailure
        Just prog ->
          print $ text (gName goal) <+> text "=" <+> programDoc (const empty) prog $+$
            solutionSizeDoc $+$
            specSizeDoc
          where
            solutionSizeDoc =
              if (showSolutionSize synquidParams) then parens (text "Size:" <+> pretty (programNodeCount prog))
              else empty
            specSizeDoc =
              if (showSpecInfo synquidParams)
                then
                  parens (text "Spec size:" <+> pretty (typeNodeCount $ toMonotype $ gSpec goal)) $+$
                    parens (text "#measures:" <+> pretty (size $ _measures $ gEnvironment goal)) $+$
                    parens (text "#components:" <+>
                      pretty (
                        (size $ _symbols $ gEnvironment goal) -
                        (size $ _datatypes $ gEnvironment goal) - 1)) -- we only solve one goal
                else empty
      print empty
