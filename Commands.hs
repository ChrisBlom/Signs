module Commands where

import Parse
import Term
import Data.Maybe
import Text.ParserCombinators.Parsec hiding ((<|>))

-- This ADT defines the the command language for the interpreter
data Command
     = Evaluate        Term
     | Load String
     | Save            (Maybe FilePath)
     | TypeOf          Term
     | Reload
     | SaveTex         Term (Maybe FilePath)
     | SaveTexAll      (Maybe FilePath)     
     | Status
     | Echo String
     | Help
     | Unknown    
     | Listing String  -- show a listing, the arg serves as a filter
     deriving (Eq,Show)

helpmenu = 
  [ "Commands : "
  , "'term'                  \t : evalutate 'term' and display the result"
  , ":l(oad) 'filename'      \t : loads 'file'" 
  , ":r(eload) 'filename'    \t : reload the loaded file"
  , ":h(elp)                 \t : shows the help menu"
  , ":r(eload)               \t : reload the last loaded grammar file"
  , ":t(ype) 'term'          \t : infers and displays the type of 'term'"
  , ":tex 'term'             \t : pretty prints 'term' as latex source"
  , ":savetex 'filename' 'term' \t : saves the latex repr. of 'term' in 'file'" 
  , ":q(uit)                 \t : exit" 
  , ":l(ist) 'filter'        \t : lists the loaded grammar"
  ]
  
isCommand = (==':') . head  

parseCommand :: Parser Command    
parseCommand =  
  ( (string ":" >> choice 
    [ parseTex    
    , parseSaveTex
    , parseTypeOf
    , parseReload
    , try parseLoad
    , parseListing 
    , string "status" >> return Status  
    , string "h" >> optional (string "elp")   >> return Help
    ] )
  <|> parseTerm)

parseReload = do
  { string "r"
  ; optional $ string "eload"
  ; spaces
  ; return Reload
  }
  
parseTypeOf = do
  { string "t"
  ; optional $ string "ype"
  ; spaces
  ; term <- term'
  ; return (TypeOf term)
  }  
  

parseTerm = do
  { spaces
  ; term <- term'
  ; spaces
  ; return (Evaluate term)
  }

on (h:t) =  do {
  ; string (h:[])
  ; optional $ string t
  ; string " "
  }

parseLoad = do
  { on "load"
  ; name <- parseFileName "signs" 
  ; return (Load name)
  }
  
parseSave = do
  on "save"
  maybeTarget <- optionMaybe $ do
      string " "
      parseFileName "signs"
  return (Save maybeTarget)
  
  
parseTexAll = do  
  string "texall"  
  maybeTarget <- optionMaybe $ do
      string " "
      parseFileName "tex"
  return (SaveTexAll maybeTarget)  
  
parseTex = do  
  string "tex"  
  string " "      
  term <- term'      
  return (SaveTex term Nothing)
  
parseSaveTex = do  
  string "savetex "  
  filename <- parseFileName "tex"
  string " "
  spaces
  term <- term'      
  return (SaveTex term (Just filename) )

parseListing = do
  string "p"
  optional $ string "rint"
  string " "
  maybeTarget <- do many alphaNum
  return (Listing maybeTarget)     
   
