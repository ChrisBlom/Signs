
import Commands
import Interpreter
import Parse
import Control.Monad.Trans.State.Lazy
import System.Console.Readline

import Data.Maybe

-- read evaluate print loop, passes interpreter state around
repl :: InterpreterState -> IO ()
repl prevState = do
  { input   <- readline "> "
  ; case input of 
      Nothing      -> repl prevState  -- do nothing
      Just ":quit" -> return ()       -- quit
      Just ":q"    -> return ()
      Just line    -> do              
        newstate <- runStateT (processCommand $ line) prevState -- parse and execute the command
        addHistory line
        repl (snd newstate)           -- pass on the updated state
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
 ," v0.97                       Chris Blom 2013   "
 ,""
 ,"enter :help to list the available commands."
 ,""
 ] 
