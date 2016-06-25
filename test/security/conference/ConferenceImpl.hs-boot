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


emptyString :: String
s_colon :: String
s_comma :: String
s_authors :: String
s_paperNo :: String

eq :: (Eq a, Ord a) => a -> a -> Bool

getChair :: World -> Tagged User

getCurrentPhase :: World -> Tagged Phase

getPaperAuthors :: World -> PaperId -> Tagged (List User)

getPaperConflicts :: World -> PaperId -> Tagged (List User)

getPaperSession :: World -> PaperId -> Tagged String

getPaperStatus :: World -> PaperId -> Tagged Status

getPaperTitle :: World -> PaperId -> Tagged String

getSessionUser :: World -> Tagged User

if_ ::
    (Eq a, Ord a) => Tagged Bool -> Tagged a -> Tagged a -> Tagged a

lift1 ::
      (Eq a, Ord a, Eq b, Ord b) => (a -> b) -> Tagged a -> Tagged b

lift2 ::
      (Eq a, Ord a, Eq b, Ord b, Eq c, Ord c) =>
        (a -> b -> c) -> Tagged a -> Tagged b -> Tagged c

not :: Bool -> Bool

print :: World -> Tagged User -> Tagged String -> World

printAll :: World -> Tagged (List User) -> Tagged String -> World

return :: (Eq a, Ord a) => a -> Tagged a

strcat :: String -> String -> String

toString :: (Show a) => a -> String

instance Show Status
instance Show a => Show (List a)
