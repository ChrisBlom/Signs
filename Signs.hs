import Interpreter

import System.IO.Unsafe



import Control.Monad.Error
import Control.Monad.Trans.State.Strict

-- top level loop: get input, proces it to get a command, execute the command, and propagate the updated state
topLevelLoop state = do
  { putStr ">" 
  ; input   <- getLine
  ; newstate <- runStateT (processCommand2 input) state
  ; topLevelLoop (snd newstate)
  }

-- display welcome menu, start top level loop with initial state
main :: IO ()
main = sequence_ [header,putStr ">",topLevelLoop initialState]

header = mapM_ putStrLn
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
