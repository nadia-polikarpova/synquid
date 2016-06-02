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
    
-- | Dummy source position
noPos = (initialPos "<no file name>")    

data ErrorKind = ParseError | ResolutionError | TypeError

data ErrorMessage = ErrorMessage {
  emKind :: ErrorKind,
  emPosition :: SourcePos,
  emDescription :: Doc
}

