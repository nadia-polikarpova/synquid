module Synquid.Stats where
  
import Data.Map hiding (map)
import Data.Time.Clock
import Data.Fixed

import Synquid.Pretty


{- Time Measurement -}

type Tm = NominalDiffTime

data SynthPhase = TypeCheck | Repair | Recheck deriving (Show, Eq, Ord)
type TimeStats = Map SynthPhase Tm
type TimeCheckpoint = (UTCTime, TimeStats)

startTiming :: IO TimeCheckpoint
startTiming = do
  now <- getCurrentTime
  return (now, fromList [(TypeCheck, 0), (Repair, 0), (Recheck, 0)])

sample :: TimeCheckpoint -> SynthPhase -> IO TimeCheckpoint
sample (then_, stats) phase = do
  now <- getCurrentTime
  return (now, insert phase (diffUTCTime now then_) stats)

{- Couldn't make it to work }
timed :: Monad m => TimeCheckpoint -> SynthPhase -> m (IO a) -> m (IO (a, TimeCheckpoint))
timed cp phase operation = do
  res <- operation
  cp' <- lift $ sample cp phase
  return (res, cp')
-}


{- Statistics Table -}

data StatsRow = StatsRow { 
  sName :: String,    sSpec :: Int,    sTempl :: Int,    sSolution :: Int, 
  sTmTypeCheck :: Tm, sTmRepair :: Tm, sTmRecheck :: Tm, sTmTotal :: Tm
}

statsTable :: [StatsRow] -> Doc
statsTable dataRows =
  let headerRow = [text "Goal", {-text "Spec",-} text "Templ", text "Solution", text "Time: Typecheck", text "Repair", text "Recheck", text "Total Synth"]
      totalsRow = StatsRow "Totals" (sum $ map sSpec dataRows) (sum $ map sTempl dataRows) (sum $ map sSolution dataRows) (sum $ map sTmTypeCheck dataRows) (sum $ map sTmRepair dataRows) (sum $ map sTmRecheck dataRows) (sum $ map sTmTotal dataRows)
      toDocs (StatsRow a b c d e f g h) = [text a, {-pretty b, -}pretty c, pretty d, tm e, tm f, tm g, tm h]
      tm t = text $ show (realToFrac t :: Centi) ++ "s"
      colWidths = [20, {--8,-} -8, -8, -16, -9 ,-9, -11]   -- TODO autocompute width of first column
  in
    mkTableLaTeX colWidths $ headerRow : map toDocs (dataRows ++ [totalsRow])
