module ConferenceImpl where

import qualified Prelude
import Prelude hiding (String)

import {-# SOURCE #-} ConferenceVerification

type String = Prelude.String

type User = String

type PaperId = Prelude.Int

data World

data Tagged a



and :: Bool -> Bool -> Bool

bind ::
     (Eq a, Ord a, Eq b, Ord b) =>
       Tagged a -> (a -> Tagged b) -> Tagged b

elem :: (Eq a, Ord a) => a -> List a -> Bool
map :: (a -> b) -> List a -> List b
foldl1 :: (a -> a -> a) -> List a -> a
foldl :: (a -> b -> a) -> a -> List b -> a

forM_ ::
        (Eq a, Ord a) =>
        World -> Tagged (List (Tagged a)) -> (World -> Tagged a -> World) -> World

emptyString :: String
s_colon :: String
s_comma :: String
s_authors :: String
s_paperNo :: String
s_qmark :: String

eq :: (Eq a, Ord a) => a -> a -> Bool

getChair :: World -> Tagged User

getCurrentPhase :: World -> Tagged Phase

getPaperAuthors :: World -> PaperId -> Tagged (List User)

getPaperConflicts :: World -> PaperId -> Tagged (List User)

getPaperSession :: World -> PaperId -> Tagged String

getPaperStatus :: World -> PaperId -> Tagged Status

getPaperTitle :: World -> PaperId -> Tagged String

getSessionUser :: World -> Tagged User

getAllPapers :: World -> List PaperId

if_ ::
    (Eq a, Ord a) => Tagged Bool -> Tagged a -> Tagged a -> Tagged a

lift1 ::
      (Eq a, Ord a, Eq b, Ord b) => (a -> b) -> Tagged a -> Tagged b

lift2 ::
      (Eq a, Ord a, Eq b, Ord b, Eq c, Ord c) =>
        (a -> b -> c) -> Tagged a -> Tagged b -> Tagged c

liftAnd :: Tagged Bool -> Tagged Bool -> Tagged Bool

not :: Bool -> Bool

print :: World -> Tagged User -> Tagged String -> World

printAll :: World -> Tagged (List User) -> Tagged String -> World

return :: (Eq a, Ord a) => a -> Tagged a

strcat :: String -> String -> String

toString :: (Show a) => a -> String

instance Eq a => Eq (Tagged a)
instance Ord a => Ord (Tagged a)
instance Show Status
instance Show a => Show (List a)
