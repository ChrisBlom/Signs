module Interpreter where

import Control.Monad.State
import Control.Monad


import Term
import Type
import Parse
import Grammar
import GrammarParser
import Inference

import Data.Maybe
import System.IO
import System.IO.Unsafe
import Data.List
import Text.ParserCombinators.Parsec hiding ((<|>))
{- 

commands

load "file.grammar"



-}



data InterpreterState = St
  { reduce :: Bool
  , showReductions :: Bool
  , active_grammar :: Maybe Grammar
  , filename :: String
  } deriving Show
  
  
startState = St
  { reduce = True
  , showReductions = True
  , active_grammar = Nothing
  , filename = ""
  }  


-- add sign 'sign_def'
-- add type_interpretation 'type_interpretation'
-- remove sign 'sign_name'
-- add type_interpretation 'type_name'

commands = undefined

command ":help" state = do {
  ; putStrLn $ helpmenu  
  ; return state
  }
  
command ":status" state = do {
  ; putStrLn $ show state
  ; return state
  }  
  
command (':':'l':'o':'a':'d':' ':file) state = 
  putStrLn ("loading... " ++ file) >> loadThenParse state file

      
  
  
  
parseFile file state content   = case (parse grammar file content) of
  Left error -> do {
    ; putStrLn ( concat ["error parsing \'" ++ file ++"\'"] )
    ; putStrLn $ show error    
    ; return ( state {filename = file } )
    }
  Right parsedGrammar -> do {
    ; putStrLn ( concat ["succesfully loaded and parsed \'" ++ file ++"\'"] )
    ; return ( state {filename = file , active_grammar = Just parsedGrammar } )
    }
    

getFileContent :: FilePath -> IO String
getFileContent file = do { i <- openFile file ReadMode ; c <- hGetContents i ; return c }
    
loadThenParse :: InterpreterState -> FilePath -> IO InterpreterState
loadThenParse state file = (getFileContent file) >>= (parseFile file state)

test x = liftM (fromJust . active_grammar) $ loadThenParse startState (x ++ ".signs")


check x = do 
  grammar <- test "optional"
  (mapM_ putStrLn $ concat $  (map.map) (either ("fail: "++) ("pass: "++)) $ typeCheckSigns $ grammar)

  
helpmenu = (concat 
  [ "Commands : "
  , ":load \"filename\" \t : load a grammar" 
  , ":save (\"filename\") \t : save the grammar"
  , ":latex (\"filename\") \t : export a grammar to a latex file"
  ])  
  
--command _ =  mapM putStrLn $ ["unknown command"]



topLevelLoop state = do
  putStr ">"
  input <- getLine
  newstate <- command input state
  topLevelLoop newstate


----------------------------------------------------
-- main


main :: IO ()
main = header >>
  (topLevelLoop startState)



header = mapM_ putStrLn
 [" _______ _________ _______  _     _  _______ "
 ,"(  ____ \\\\__   __/(  ____ \\( \\   ( )/  ____ \\"
 ,"| (    \\/   ) (   | (    \\/|  \\  | || (    \\/"
 ,"| (_____    | |   | |      |   \\ | || (_____ "
 ,"(_____  )   | |   | | ____ | |\\ \\| |(_____  )"
 ,"      ) |   | |   | | \\_  )| | \\   |      ) |"
 ,"/\\____) |___) (___| (___) || |  \\  |/\\____) |"
 ,"\\_______)\\_______/(_______)(_)   \\_)\\_______)"
 ," v0.5                       Chris Blom 2011   "
 ,""
 ] 
                                             
