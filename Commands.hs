module Commands where

import Parse
import Term
import Data.Maybe
import Text.ParserCombinators.Parsec hiding ((<|>))

-- This ADT defines the the command language for the interpreter
data Command
     = Load String
     | Save            (Maybe FilePath)
     | TypeOf          Term
     | Reload
     | SaveTex         Term (Maybe FilePath)
     | SaveTexAll      (Maybe FilePath)     
     | Evaluate        Term
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
  (string ":" >> choice 
    [ parseTex    
    , parseSaveTex
    , parseTypeOf
    , parseReload
    , parseLoad
    , parseListing 
    , string "status" >> return Status  
    , string "h" >> optional (string "elp")   >> return Help
    ] <?> "command string")
  <|> parseTerm

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

parseLoad = do
  { string "l"
  ; optional $ string "oad"
  ; string " "
  ; name <- parseFileName "signs" 
  ; return (Load name)
  }
  
parseSave = do
  string "s"
  optional $ string "ave"
  string " "
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
   
