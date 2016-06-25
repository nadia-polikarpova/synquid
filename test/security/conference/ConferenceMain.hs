{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}

module Main where

import Control.Monad
import Control.Applicative
import Control.Lens
import qualified Data.Map as Map
import qualified Data.Text as T
import Text.Printf

import System.Console.CmdArgs

import Database.SQLite.Simple
import Database.SQLite.Simple.FromRow

import ConferenceImpl hiding (print, String)
import ConferenceVerification


instance FromRow PaperRow where
  fromRow = PaperRow <$> field <*> field <*> field <*> field
instance FromRow UserRow where
  fromRow = UserRow <$> field <*> field
instance FromRow AuthorRow where
  fromRow = AuthorRow <$> field <*> field
instance FromRow ConflictRow where
  fromRow = ConflictRow <$> field <*> field

(%) s n = printf s n
infix 0 %

tests opts =
  let papids = fromList $ paperIds opts
      papid = head $ paperIds opts
  in
        [("test1 w %d" % papid,          (`test1` papid)),
         ("test2 w %d" % papid,          (`test2` papid)),
         ("test3 w %d" % papid,          (`test3` papid)),
         ("test4 w %d" % papid,          (`test4` papid)),
         ("test5 w %d" % papid,          (`test5` papid)),
         ("test6 w %d" % papid,          (`test6` papid)),
         ("test7 w %s" % show (papids),  (`test7` papids))]

data CommandLineArgs = CommandLineArgs {
  db_ :: String,
  user :: String,
  papers_ :: String
}
 deriving (Data)
cla = CommandLineArgs {
  db_ = "conf.db" &= typFile,
  user = "Nadia" &= typ "NAME",
  papers_ = "12" &= typ "ID,ID,..."
}

split :: String -> String -> [String]
split sep s = map T.unpack $ T.splitOn (T.pack sep) $ T.pack s

paperIds opts = map read $ split "," (papers_ opts) :: [Int]

main :: IO ()
main = do
  opts <- cmdArgs cla
  db <- open (db_ opts)
  print $ paperIds opts
  execute_ db "CREATE TABLE IF NOT EXISTS papers (id INTEGER PRIMARY KEY, title TEXT, status TEXT, session TEXT)"
  execute_ db "CREATE TABLE IF NOT EXISTS users (id INTEGER PRIMARY KEY, name TEXT)"
  execute_ db "CREATE TABLE IF NOT EXISTS authors (paperId INTEGER REFERENCES papers (id), userId INTEGER REFERENCES users (id))"
  execute_ db "CREATE TABLE IF NOT EXISTS conflicts (paperId INTEGER REFERENCES papers (id), userId INTEGER REFERENCES users (id))"

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
            _sessionUser = (user opts),
            _effects = Map.empty
          }
      w's = map (\(title,test) -> (title, test w)) $ tests opts
    in do
     putStrLn $ "Session for user \"" ++ (w ^. sessionUser) ++ "\""
     forM_ w's $ \(title, w') -> do
       putStrLn ""
       putStrLn $ "==  " ++ title ++ "  =="
       forM_ (Map.assocs $ w' ^. effects) $ \(who,what) -> do
         putStrLn who
         forM_ what (putStrLn . ("> " ++))
