module Interpreter where

import Control.Monad.State
import Control.Monad
import Signature
import Grammar
import GrammarParser
import System.IO.Unsafe
import Data.List
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
  
command (':':'l':'o':'a':'d':' ':file) state = do 
  { putStrLn ("loading " ++ file)
  ; newstate <- return (state {filename = file} )
  ; return newstate
  }    
  
  
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
                                             
