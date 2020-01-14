module Synquid.Error (
  Pos(..)
  ,SourcePos
  ,sourceLine
  ,sourceColumn
  ,sourceName
  ,noPos
  ,ErrorKind(..)
  ,ErrorMessage(..)
  ) where

import Text.PrettyPrint.ANSI.Leijen
import Text.Parsec.Pos

-- | Anything with a source position attached
data Pos a = Pos {
  position :: SourcePos,
  node :: a
}

instance (Eq a) => Eq (Pos a) where
  (==) p1 p2 = node p1 == node p2

-- | Dummy source position
noPos = initialPos "<no file name>"

data ErrorKind = ParseError | ResolutionError | TypeError | SynthesisError

data ErrorMessage = ErrorMessage {
  emKind :: ErrorKind,
  emPosition :: SourcePos,
  emDescription :: Doc
}
