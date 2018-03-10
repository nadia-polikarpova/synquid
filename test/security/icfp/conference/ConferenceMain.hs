{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}

module Main where

import Control.Monad
import Control.Applicative
import Control.Lens
import Data.List
import Data.List.Split (splitOn)
import qualified Data.Map as Map
import qualified Data.Text as T
import Text.Printf

import System.Console.CmdArgs

import Database.SQLite.Simple
import Database.SQLite.Simple.FromRow

import ConferenceImpl hiding (String, print, elem, forM_, foldl, foldl1, map, show)
import Conference
import ConferenceRepair

instance FromRow PaperRow where
  fromRow = PaperRow <$> field <*> field <*> field <*> field
instance FromRow UserRow where
  fromRow = UserRow <$> field <*> field
instance FromRow AuthorRow where
  fromRow = AuthorRow <$> field <*> field
instance FromRow ConflictRow where
  fromRow = ConflictRow <$> field <*> field
instance FromRow PcRow where
  fromRow = PcRow <$> field

(%) s n = printf s n
infix 0 %

tests :: CommandLineArgs -> [(String, World -> World)]
tests opts =
  let papids = fromList $ paperIds opts
      papid = head $ paperIds opts
      filt = if null $ actions opts then id else filter (\(title,_) -> or (map (\act -> act `isPrefixOf` title) (actions opts)))
  in  filt
        [("test1 w %d" % papid,          (`test1` papid)),
         ("test2 w %d" % papid,          (`test2` papid)),
         ("test3 w %d" % papid,          (`test3` papid)),
         ("test4 w %d" % papid,          (`test4` papid)),
         ("test5 w %d" % papid,          (`test5` papid)),
         ("test6 w %d" % papid,          (`test6` papid)),
         ("test7 w %s" % show (papids),  (`test7` papids)),
         ("test8 w",                     test8),
         ("test9 w",                     test9),
         ("test10 w",                    test10),
         ("test11 w %d" % papid,         (`test11` papid)),
         ("test12 w",                    test12)]

data CommandLineArgs = CommandLineArgs {
  db_ :: String,
  user :: String,
  actions :: [String],
  papers_ :: String,
  phase_ :: String
}
 deriving (Data)
cla = CommandLineArgs {
  db_ = "conf.db"   &= typFile,
  user = "Nadia"    &= typ "NAME",
  actions = []      &= args,
  papers_ = "12"    &= typ "ID,ID,...",
  phase_ = "S"      &= typ "S/R/D" &= help "Phase of the conference (Submission/Review/Done)"
}

paperIds opts = map read $ splitOn "," (papers_ opts) :: [Int]

parsePhase :: String -> Phase
parsePhase s | s `isPrefixOf` "Submission" = Submission
             | s `isPrefixOf` "Review" = Review
             | s `isPrefixOf` "Done" = Done

main :: IO ()
main = do
  opts <- cmdArgs cla

  db <- open (db_ opts)
  execute_ db "CREATE TABLE IF NOT EXISTS papers (id INTEGER PRIMARY KEY, title TEXT, status TEXT, session TEXT)"
  execute_ db "CREATE TABLE IF NOT EXISTS users (id INTEGER PRIMARY KEY, name TEXT)"
  execute_ db "CREATE TABLE IF NOT EXISTS authors (paperId INTEGER REFERENCES papers (id), userId INTEGER REFERENCES users (id))"
  execute_ db "CREATE TABLE IF NOT EXISTS conflicts (paperId INTEGER REFERENCES papers (id), userId INTEGER REFERENCES users (id))"
  execute_ db "CREATE TABLE IF NOT EXISTS pc (userId INTEGER REFERENCES users (id))"

  users <- query_ db "SELECT * FROM users" :: IO [UserRow]
  papers <- query_ db "SELECT * FROM papers" :: IO [PaperRow]
  authors <- query_ db "SELECT * FROM authors" :: IO [AuthorRow]
  conflicts <- query_ db "SELECT * FROM conflicts" :: IO [ConflictRow]
  pc <- query_ db "SELECT * FROM pc" :: IO [PcRow]

  let w = World {
            _db = Database {
              _chair = "Emery",
              _pc = mkPc pc users,
              _phase = parsePhase $ phase_ opts,
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
