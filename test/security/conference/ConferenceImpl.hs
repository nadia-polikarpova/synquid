{-# LANGUAGE StandaloneDeriving, TemplateHaskell #-}
module ConferenceImpl where

import Prelude hiding (String, elem, print, foldl, foldl1, map, show)

import qualified Prelude
import Data.Map (Map, (!))
import qualified Data.Map as M
import qualified Data.Text as T

import Control.Lens

import Security
import qualified Conference as C
import Conference hiding (Maybe, Just, Nothing)
import ConferenceRepair


type String = Prelude.String

type User = String

type PaperId = Int

type Token = String

data Tagged a = Tagged a
deriving instance Eq a => Eq (Tagged a)
deriving instance Ord a => Ord (Tagged a)

data Database = Database {
  _chair :: User,
  _pc :: [User],
  _phase :: Phase,
  _papers :: Map PaperId PaperRecord
}
 deriving (Show)

data World = World {
  _db :: Database,
  _sessionUser :: User,
  _effects :: Map User [String]
}
 deriving (Show)

data PaperRecord = PaperRecord {
  _papid :: PaperId,
  _title :: String,
  _authors :: [String],
  _conflicts :: [String],
  _status :: Status,
  _session :: String
}
 deriving (Show)

deriving instance Show Phase
deriving instance Show Status

makeLenses ''Database
makeLenses ''World
makeLenses ''PaperRecord


data PaperRow = PaperRow Int T.Text (Maybe T.Text) (Maybe T.Text) deriving (Show)
data UserRow = UserRow Int T.Text deriving (Show)
data AuthorRow = AuthorRow Int Int deriving (Show)
data ConflictRow = ConflictRow Int Int deriving (Show)
data PcRow = PcRow Int deriving (Show)

selectJoin table1 table2 cross = concatMap (\x -> concatMap (cross x) table2) table1

mkPapers prows urows arows crows =
    M.fromList $ 
         Prelude.map (\(PaperRow id title status session) ->
                        (id, PaperRecord {
                            _papid = id,
                            _title = T.unpack title,
                            _authors = authors id,
                            _conflicts = conflicts id,
                            _status = case fmap T.unpack status of
                                        Just "Accepted" -> Accepted
                                        Just "Rejected" -> Rejected
                                        _ -> NoDecision
                            ,
                            _session = case session of
                                         Just ss -> T.unpack ss
                                         Nothing -> ""
                        })) prows
    where
        authors papid = selectJoin arows urows (\(AuthorRow papid' usid') (UserRow usid name) ->
          [T.unpack name | papid == papid' && usid == usid'])
        --concatMap (\(AuthorRow papid' usid') ->
        --    concatMap (\(UserRow usid name) -> if (papid == papid' && usid == usid') then [T.unpack name] else []) urows) arows
        conflicts papid = selectJoin crows urows (\(ConflictRow papid' usid') (UserRow usid name) ->
          [T.unpack name | papid == papid' && usid == usid'])

mkPc pcrows urows =
    selectJoin pcrows urows (\(PcRow usid') (UserRow usid name) -> [T.unpack name | usid == usid'])

{- Actual impls! -}


{- Boolean stuff -}

true = True
false = False

eq :: (Eq a, Ord a) => a -> a -> Bool
eq x y = x == y

and :: Bool -> Bool -> Bool
and p q = p && q

not :: Bool -> Bool
not = Prelude.not

{- Tagged "Monad" -}

bind ::
     (Eq a, Ord a, Eq b, Ord b) =>
       Tagged a -> (a -> Tagged b) -> Tagged b
bind (Tagged a) f = f a

return :: (Eq a, Ord a) => a -> Tagged a
return = Tagged

bindBool ::
      (Eq b, Ord b) => Tagged Bool -> (Bool -> Tagged b) -> Tagged b
bindBool = bind

if_ ::
    (Eq a, Ord a) => Tagged Bool -> Tagged a -> Tagged a -> Tagged a
if_ (Tagged cond) t e = if cond then t else e

lift1 ::
      (Eq a, Ord a, Eq b, Ord b) => (a -> b) -> Tagged a -> Tagged b
lift1 f (Tagged a) = Tagged $ f a

lift2 ::
      (Eq a, Ord a, Eq b, Ord b, Eq c, Ord c) =>
        (a -> b -> c) -> Tagged a -> Tagged b -> Tagged c
lift2 f (Tagged a) (Tagged b) = Tagged $ f a b

liftAnd = lift2 (&&)

{- List -}

foldl1 :: (a -> a -> a) -> List a -> a
foldl1 f = Prelude.foldl1 f . toList

foldl :: (a -> b -> a) -> a -> List b -> a
foldl f a = Prelude.foldl f a . toList

forM_ ::
        (Eq a, Ord a) =>
        World -> Tagged (List (Tagged a)) -> (World -> Tagged a -> World) -> World
forM_ w (Tagged Nil) f = w
forM_ w (Tagged (Cons x xs)) f = forM_ (f w x) (Tagged xs) f

toList Nil = []
toList (Cons x xs) = x : toList xs

fromList = foldr Cons Nil

lfoldl f w Nil = w
lfoldl f w (Cons x xs) = lfoldl f (f w x) xs

instance Show a => Show (List a) where
  show = show . toList

{- Maybe -}

toMaybe C.Nothing = Nothing
toMaybe (C.Just x) = Just x

instance Show a => Show (C.Maybe a) where
  show = show . toMaybe

{- String -}

emptyString = ""

{-# ANN module "HLint: Use camelCase" #-}
s_colon = ": "
s_comma = ", "
s_authors = "authors: "
s_paperNo = "Paper #"
s_qmark = "?"
s_delighted = "We are delighted to inform you"
s_regret = "We regret to inform you"

strcat :: String -> String -> String
strcat s1 s2 = s1 ++ s2

show :: (Show a) => a -> String
show = Prelude.show

{- Database access -}

getChair :: World -> Tagged User
getChair w = Tagged $ w ^. db ^. chair

getPC :: World -> Tagged (List User)
getPC w = Tagged $ fromList $ w ^. db ^. pc

getCurrentPhase :: World -> Tagged Phase
getCurrentPhase w = Tagged $ w ^. db ^. phase

getPaperAuthors :: World -> PaperId -> Tagged (List User)
getPaperAuthors w papid = Tagged $ fromList $ (w ^. db ^. papers) ! papid ^. authors
defaultPaperAuthors :: Tagged (List User)
defaultPaperAuthors = Tagged Nil

getPaperConflicts :: World -> PaperId -> Tagged (List User)
getPaperConflicts w papid = Tagged $ fromList $ (w ^. db ^. papers) ! papid ^. conflicts
defaultPaperConflicts :: Tagged (List User)
defaultPaperConflicts = Tagged Nil

getPaperSession :: World -> PaperId -> Tagged String
getPaperSession w papid = Tagged $ (w ^. db ^. papers) ! papid ^. session

getPaperStatus :: World -> PaperId -> Tagged Status
getPaperStatus w papid = Tagged $ (w ^. db ^. papers) ! papid ^. status
defaultPaperStatus = Tagged NoDecision

getPaperTitle :: World -> PaperId -> Tagged String
getPaperTitle w papid = Tagged $ (w ^. db ^. papers) ! papid ^. title
defaultPaperTitle = Tagged ""

getSessionUser :: World -> Tagged User
getSessionUser w = Tagged $ w ^. sessionUser

getAllPapers :: World -> List PaperId
getAllPapers w = fromList $ M.keys $ w ^. db ^. papers

getPaperBidToken :: World -> PaperId -> Tagged (C.Maybe Token)
getPaperBidToken w pid = Tagged (C.Just "do it!")
defaultPaperBidToken :: Tagged (C.Maybe Token)
defaultPaperBidToken = Tagged C.Nothing

{- Output -}

print :: World -> Tagged User -> Tagged String -> World
print w (Tagged u) (Tagged s) = over effects (M.insertWith (\new old -> old ++ new) u [s]) w

printAll :: World -> Tagged (List User) -> Tagged String -> World
printAll w (Tagged us) s = lfoldl (\w u -> print w (Tagged u) s) w us

printManyMaybe :: World -> Tagged (List User) -> Tagged (C.Maybe String) -> World
printManyMaybe w us (Tagged (C.Just s)) = printAll w us (Tagged s)
printManyMaybe w _ _ = w
