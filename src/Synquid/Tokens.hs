-- | Lexems of the Synquid language
module Synquid.Tokens where

import Synquid.Logic
import Synquid.Util
import Data.Maybe
import Data.Map (Map, fromList)
import Data.Char

-- | Keywords
keywords :: [String]
keywords = ["Bool", "data", "else", "error", "False", "if", "in", "inline", 
  "Int", "let", "match", "measure", "predicate", "qualifier", "Set", "termination",
  "then", "True", "type", "with", "where"
  ]

-- | Names of unary operators    
unOpTokens :: Map UnOp String
unOpTokens = fromList [ (Neg, "-")
                      , (Not, "!")
                      ]
                           
-- | Names of binary operators             
binOpTokens :: Map BinOp String
binOpTokens = fromList [ (Times,     "*")
                       , (Plus,      "+")
                       , (Minus,     "-")
                       , (Eq,        "==")
                       , (Neq,       "!=")
                       , (Lt,        "<")
                       , (Le,        "<=")
                       , (Gt,        ">")
                       , (Ge,        ">=")
                       , (And,       "&&")
                       , (Or,        "||")
                       , (Implies,   "==>")
                       , (Iff,       "<==>")
                       , (Union,     "+")
                       , (Intersect, "*")
                       , (Diff,      "-")
                       , (Member,    "in")
                       , (Subset,    "<=")
                       ]
                        
-- | Other operators         
otherOps :: [String]
otherOps = ["::", ":", "->", "|", "=", "??", ",", ".", "\\"] 

-- | Characters allowed in identifiers (in addition to letters and digits)
identifierChars = "_'"
-- | Start of a multi-line comment
commentStart = "{-"
-- | End of a multi-line comment
commentEnd = "-}"
-- | Start of a single-line comment
commentLine = "--"

-- | 'isLiteral' @str@ : Is string @str@ a literal of a primitive type?
isLiteral str = isJust (asInteger str) || str == "True" || str == "False"

isTypeName str = isUpper $ head str
isIdentifier str = isLower $ head str