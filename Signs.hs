
import Commands
import Interpreter

import Control.Monad.Trans.State.Lazy
import System.Console.Readline

import Data.Maybe
-- top level loop: get input, proces it to get a command, execute the command, and propagate the updated state

repl :: InterpreterState -> IO ()
repl prevState = do
  { input   <- readline "> "
  ; case input of 
      Nothing      -> repl prevState
      Just ":quit" -> return ()
      Just ":q"    -> return ()
      Just line    -> do 
        newstate <- runStateT (processCommand2 $ line) prevState 
        addHistory line
        repl (snd newstate)
  }

-- display welcome menu, start top level loop with initial state
main :: IO ()
main = sequence_ [welcome,repl initialState]

welcome = mapM_ putStrLn
 [" _______ _________ _______  _     _  _______ "
 ,"(  ____ \\\\__   __/(  ____ \\( \\   ( )/  ____ \\"
 ,"| (    \\/   ) (   | (    \\/|  \\  | || (    \\/"
 ,"| (_____    | |   | |      |   \\ | || (_____ "
 ,"(_____  )   | |   | | ____ | |\\ \\| |(_____  )"
 ,"      ) |   | |   | | \\_  )| | \\   |      ) |"
 ,"/\\____) |___) (___| (___) || |  \\  |/\\____) |"
 ,"\\_______)\\_______/(_______)(_)   \\_)\\_______)"
 ," v0.96                       Chris Blom 2012   "
 ,""
 ,"enter :help to list the available commands."
 ,""
 ] 
