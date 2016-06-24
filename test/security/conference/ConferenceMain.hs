{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad
import Control.Applicative
import Control.Lens
import qualified Data.Map as Map
import qualified Data.Text as T

import ConferenceImpl hiding (print)
import ConferenceVerification

import Database.SQLite.Simple
import Database.SQLite.Simple.FromRow


instance FromRow PaperRow where
  fromRow = PaperRow <$> field <*> field <*> field <*> field
instance FromRow UserRow where
  fromRow = UserRow <$> field <*> field
instance FromRow AuthorRow where
  fromRow = AuthorRow <$> field <*> field
instance FromRow ConflictRow where
  fromRow = ConflictRow <$> field <*> field

tests = [("test1 w 12", (`test1` 12)),
         ("test2 w 12", (`test2` 12)),
         ("test3 w 12", (`test3` 12))]

main :: IO ()
main = do
  db <- open "conf.db"
  execute_ db "CREATE TABLE IF NOT EXISTS papers (id INTEGER PRIMARY KEY, title TEXT, status TEXT, session TEXT)"
  execute_ db "CREATE TABLE IF NOT EXISTS users (id INTEGER PRIMARY KEY, name TEXT)"
  execute_ db "CREATE TABLE IF NOT EXISTS authors (paperId INTEGER, userId INTEGER)"
  execute_ db "CREATE TABLE IF NOT EXISTS conflicts (paperId INTEGER, userId INTEGER)"

  users <- query_ db "SELECT * FROM users" :: IO [UserRow]
  papers <- query_ db "SELECT * FROM papers" :: IO [PaperRow]
  authors <- query_ db "SELECT * FROM authors" :: IO [AuthorRow]
  conflicts <- query_ db "SELECT * FROM conflicts" :: IO [ConflictRow]


  let w = World {
            _db = Database {
              _chair = "Emery",
              _phase = Review,
              _papers = mkPapers papers users authors conflicts
            },
            _sessionUser = "Nadia",
            _effects = Map.empty
          }
      w's = map (\(title,test) -> (title, test w)) tests
    in
     forM_ w's $ \(title, w') -> do
       putStrLn ""
       putStrLn $ "==  " ++ title ++ "  =="
       forM_ (Map.assocs $ w' ^. effects) $ \(who,what) -> do
         putStrLn who
         forM_ what (putStrLn . ("> " ++))
