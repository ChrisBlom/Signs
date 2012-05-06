module Interpreter where

import Control.Monad

import Term
import Type
import Parse
import Sign
import Grammar
import GrammarParser
import Inference
import Reductions
import MyError
import Commands
import Control.Monad.Error
import Control.Monad.Reader
import System.Environment


import Data.Maybe
import Data.Either
import System.IO
import Control.Monad.Trans.State.Strict

import Data.List
import Text.ParserCombinators.Parsec hiding ((<|>),State)

import Tex

type I a = StateT InterpreterState IO a 

interpret :: I a -> IO InterpreterState
interpret f = liftM snd $ runStateT f initialState

-- the global state of the interpreter : 
data InterpreterState = St
  { active_grammar  :: Maybe Grammar
  , filename        :: Maybe FilePath
  , last_output     :: String
  } 
  
-- initial state
initialState = St
  { active_grammar = Nothing
  , filename = Nothing
  , last_output = ""
  }    
  
instance Show InterpreterState where
  show g = case (filename g,active_grammar g) of
    (Nothing,_) -> " no file loaded"
    (_,Nothing) -> " no grammar loaded"    
    (Just f,g)  -> " file = " ++ show f ++ " grammar = " ++ 
                   maybe "not loaded" (\g' -> "loaded " ++ show (length $ signs g') ++ " signs" ) g

unsetGrammar s  = s {active_grammar = Nothing} 
setGrammar g s  = s {active_grammar = Just g} 
setFilename g s  = s {filename = Just g} 


run :: [Command] -> IO InterpreterState
run commands  = interpret $ sequence_ $ map execute commands 

run' commands  = sequence_ $ map execute commands 

testrun commands = run $ Load "opt.signs" : commands

-- operational semantics of the command language
execute :: Command -> I ()
execute command  = case command of
  Load filename        -> doLoad filename
  Evaluate term        -> doPrintSign term
  Reload               -> doReload
  Echo string          -> liftIO $ putStrLn string
  SaveTex term file    -> doSaveTex term file
  TypeOf term          -> doTypeInfer term
  Help                 -> liftIO $ sequence_ $ map putStrLn helpmenu

-- load a file into the state
doLoad filename = sequence_ 
  [ liftIO $ putStr ("loading... \t" ++ filename)
  , loadGrammarFile filename
  , typeCheckGrammar
  ]

-- load, parse, and type-check a grammar file
loadGrammarFile :: FilePath ->  I ()
loadGrammarFile path = do
  content <- liftIO (loadGrammar path)
  case content of
    Right grammar -> do
       liftIO (putStr "\t: OK" >> putStrLn "") 
       modify (setGrammar grammar) 
       modify (setFilename path)
    Left  error  -> liftIO $ sequence_ $ map putStrLn
      [ "\nParse error:"
      , show error 
      , "loading failed"
      ]
    
-- type check the grammar, unset the current grammer on any failure    
typeCheckGrammar :: I ()
typeCheckGrammar = do
  withGrammar' $ \g ->
   let errors = filter (not . null) $ validate g in
   case errors of 
     [] -> liftIO $ putStrLn "type checking...\t      \t: OK"
     _  -> do liftIO $ mapM_ (mapM_ putStrLn) errors
              modify unsetGrammar 
              liftIO $ putStrLn "loading failed." 

-- reload the current file              
doReload = do 
  state <- get 
  case filename state of
    Just filename -> execute $ Load filename
    Nothing       -> liftIO $ putStrLn "failed: no file is loaded yet"     
    
-- infer the type of a term and display it    
doTypeInfer term = do
  state <- get    
  liftIO $ putStrLn $ case active_grammar state of 
    Just g -> do
        (either show show) $ do 
        term <- procesConsoleTerm' g term
        (typeOfE term)           
    Nothing -> "no grammar loaded" 
    
  
execute2' :: String -> I ()
execute2' string  = case runParser parseCommand () "" string of
  Left  errormsg -> liftIO $ print errormsg 
  Right command  -> execute command 

-- interaction with commandline
--processCommand2 :: String -> InterpreterState -> IO InterpreterState
processCommand2 string 
  | null string   = modify id           -- do nothing
  | otherwise     = execute2' string

-- Parses a term with untyped constants.
procesConsoleTerm :: Grammar -> String -> MyError Term
procesConsoleTerm g input = do
  absTerm <- (show .|. id) $ parse term' "console" input
  typedAbsTerm <- runReader (addTypesToTermG (runReader getAbstractSig g) absTerm) g
  return typedAbsTerm
  
-- Parses a term with untyped constants.
procesConsoleTerm' :: Grammar -> Term -> MyError Term
procesConsoleTerm' g absTerm = runReader (addTypesToTermG (runReader getAbstractSig g) absTerm) g

-- maps an abstact term to its sign  
termToSign :: Grammar -> Term -> Either String Sign
termToSign g abstractTerm 
  | errors == []  = Right $ Sign {abstract = abstractTerm , concretes = terms } 
  | otherwise     = Left $ unlines errors
  where  (errors,terms) = concatEithers $ map  (\sig -> termHomomorphism g sig abstractTerm ) (runReader getConcreteSigs g)
  
  
withGrammar f = do 
  state <- get
  liftIO $ case active_grammar state of 
    Just g -> f g
    Nothing ->  putStrLn "no sign grammar loaded yet"

withGrammar' f = do 
  state <- get
  case active_grammar state of 
    Just g -> f g
    Nothing -> liftIO $ putStrLn "no sign grammar loaded yet"
    
    
-- evalutate, types and prints a term  
doPrintSign term = do 
  withGrammar $ \g -> case procesConsoleTerm' g term of
     Left error      -> putStrLn error 
     Right typedTerm -> case termToSign g typedTerm of 
       Left error  -> putStrLn error 
       Right sign  -> putStrLn $ runReader (prettyPrintSign sign) g
       
      
-- display a term as a latex file
doShowTex 
     :: Term
     -> I ()
doShowTex term = do
  state <- get
  liftIO $ putStrLn $ case active_grammar state of
   Nothing -> "no sign grammar loaded yet" 
   Just g -> case procesConsoleTerm' g term of   
     Left error      -> error
     Right typedTerm ->  case (termToSign g typedTerm) of
      Left error -> error
      Right x    -> render $ runReader (prettyPrintSignTex (reduceSign x)) g
     
        
texSign sign =  mathmode $  tex sign

-- save a term as a latex file, or display it of no file is specified
doSaveTex 
     :: Term
     -> Maybe FilePath 
     -> I ()
doSaveTex term file = do
  withGrammar' $ \g -> case procesConsoleTerm' g term of 
     Left error      -> liftIO $ putStrLn error
     Right typedTerm -> case termToSign g typedTerm of 
       Left error  -> liftIO $ putStrLn error 
       Right sign  -> let texString = render $ runReader (prettyPrintSignTex $ reduceSign sign) g in 
        case file of
         Just f -> do
           liftIO $ writeFile f texString 
           liftIO $ putStrLn $ "written to " ++ show f
           modify ( \s -> s {last_output = texString})
         Nothing -> doShowTex term



