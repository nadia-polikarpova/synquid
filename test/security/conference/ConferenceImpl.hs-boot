module ConferenceImpl where

import qualified Prelude
import Prelude hiding (String, Maybe)

import {-# SOURCE #-} Conference
import {-# SOURCE #-} Security

type String = Prelude.String

type User = String

type PaperId = Prelude.Int

type Token = String

data World

data Tagged a


true :: Bool
false :: Bool

eq :: (Eq a, Ord a) => a -> a -> Bool

and :: Bool -> Bool -> Bool

bind ::
     (Eq a, Ord a, Eq b, Ord b) =>
       Tagged a -> (a -> Tagged b) -> Tagged b

bindBool ::
     (Eq b, Ord b) => Tagged Bool -> (Bool -> Tagged b) -> Tagged b

return :: (Eq a, Ord a) => a -> Tagged a

foldl1 :: (a -> a -> a) -> List a -> a
foldl :: (a -> b -> a) -> a -> List b -> a

--sameElem :: List a -> List a -> Bool

forM_ ::
        (Eq a, Ord a) =>
        World -> Tagged (List (Tagged a)) -> (World -> Tagged a -> World) -> World

emptyString :: String
s_colon :: String
s_comma :: String
s_authors :: String
s_paperNo :: String
s_qmark :: String
s_delighted :: String
s_regret :: String

getChair :: World -> Tagged User

getPC :: World -> Tagged (List User)

getCurrentPhase :: World -> Tagged Phase

getPaperAuthors :: World -> PaperId -> Tagged (List User)

getPaperConflicts :: World -> PaperId -> Tagged (List User)

getPaperSession :: World -> PaperId -> Tagged String

getPaperStatus :: World -> PaperId -> Tagged Status

getPaperTitle :: World -> PaperId -> Tagged String

getSessionUser :: World -> Tagged User

getAllPapers :: World -> List PaperId

getPaperBidToken :: World -> PaperId -> Tagged (Maybe Token)

defaultPaperAuthors :: Tagged (List User)
defaultPaperBidToken :: Tagged (Maybe Token)
defaultPaperConflicts :: Tagged (List User)
defaultPaperStatus :: Tagged Status
defaultPaperTitle :: Tagged String

lift1 ::
      (Eq a, Ord a, Eq b, Ord b) => (a -> b) -> Tagged a -> Tagged b

lift2 ::
      (Eq a, Ord a, Eq b, Ord b, Eq c, Ord c) =>
        (a -> b -> c) -> Tagged a -> Tagged b -> Tagged c

not :: Bool -> Bool

print :: World -> Tagged User -> Tagged String -> World

printAll :: World -> Tagged (List User) -> Tagged String -> World

printManyMaybe :: World -> Tagged (List User) -> Tagged (Maybe String) -> World

strcat :: String -> String -> String

show :: (Show a) => a -> String

instance Eq a => Eq (Tagged a)
instance Ord a => Ord (Tagged a)
instance Show Status
instance Show a => Show (List a)
instance Show a => Show (Maybe a)
