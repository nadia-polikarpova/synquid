{-# LANGUAGE DeriveDataTypeable #-}

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

programName = "synquid"
versionName = "0.2"
releaseDate = fromGregorian 2015 11 20

-- | Execute or test a Boogie program, according to command-line arguments
main = do
  (CommandLineArgs file) <- cmdArgs cla
  runOnFile defaultExplorerParams defaultSolverParams file
  
{- Command line arguments -}

data CommandLineArgs
    = CommandLineArgs {
        -- | Input
        file :: String 
      }
  deriving (Data, Typeable, Show, Eq)
  
cla = CommandLineArgs {
  file        = ""              &= typFile &= argPos 0
  } &= help "Synthesize goals specified in the input file" &= program programName &= summary (programName ++ " v" ++ versionName ++ ", " ++ showGregorian releaseDate)

-- | Parameters for template exploration
defaultExplorerParams = ExplorerParams {
  _eGuessDepth = 3,
  _scrutineeDepth = 0,
  _matchDepth = 1,
  _condDepth = 1,
  _combineSymbols = PickDepthFirst,
  -- _combineSymbols = PickInterleave,
  _fixStrategy = AllArguments,
  -- _fixStrategy = FirstArgument,
  -- _fixStrategy = DisableFixpoint,
  _polyRecursion = True,
  _incrementalSolving = True,
  _consistencyChecking = False,
  _condQualsGen = undefined,
  _typeQualsGen = undefined,
  _context = id,
  _explorerLogLevel = 1
}

-- | Parameters for constraint solving
defaultSolverParams = SolverParams {
  pruneQuals = True,
  -- pruneQuals = False,
  optimalValuationsStrategy = MarcoValuations,    
  -- optimalValuationsStrategy = BFSValuations,    
  semanticPrune = True,
  agressivePrune = True,
  -- semanticPrune = False,
  -- agressivePrune = False,    
  candidatePickStrategy = InitializedWeakCandidate,
  -- candidatePickStrategy = WeakCandidate,
  constraintPickStrategy = SmallSpaceConstraint,
  candDoc = const empty,
  solverLogLevel = 1
  }
  
inequalities = do
  op <- [Ge, Le, Neq]
  return $ Binary op (intVar "x") (IntLit 0)

-- | Parse and resolve file, then synthesize the specified goals 
runOnFile :: ExplorerParams -> SolverParams -> String -> IO ()      
runOnFile explorerParams solverParams file = do 
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
      print empty
      -- print $ vMapDoc pretty pretty (allSymbols $ gEnvironment goal)
      mProg <- synthesize explorerParams solverParams goal cquals tquals
      case mProg of
        Nothing -> putStr "No Solution"
        Just prog -> print $ text (gName goal) <+> text "=" <+> programDoc (const empty) prog -- $+$ parens (text "Size:" <+> pretty (programNodeCount prog))
