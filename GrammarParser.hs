module GrammarParser where
import Signature

import Inference
import Grammar
import Prelude hiding (lines)
import Text.ParserCombinators.Parsec hiding ((<|>))
import System.IO.Unsafe
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language (haskellDef)
import Text.ParserCombinators.Parsec.Prim
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Combinator
import Control.Monad(liftM)

import qualified Data.Map as Map

import qualified Text.ParserCombinators.Parsec.Token as P


data Name = Gen Int | User String
  deriving (Eq,Show)


defs = haskellDef {
  P.reservedNames = ["fun","in","let","lam","type_interpretations" ,"signatures" ,"?"  , "*" ],
  P.reservedOpNames = ["->","::" , ":" , "," , ":::" , "=>","=",".","/\\","\\/"]
}



fromRight (Right x) = x

type TypeInterpretation = Map.Map Type [Type]



grammar = do 
  { lines 
  ; sigNames <- signatures
  ; lines
  ; typeMappings <- type_interpretations
  ; lines
  ; signs <- many1 signline
  ; return (Grammar sigNames typeMappings signs)
  }


signatures = do 
  { reserved "signatures"  ; optional spaces
  ; (abstract,concretes) <- abstract_concrete capitalized
  ; return (abstract,concretes)
  } <?> "signature names"

capitalized = do { u <- upper ; l <- many1 lower ; return (u:l) } <?> "capitalized"
    

type_mapping = do 
  (abstract,concretes) <- abstract_concrete typ
  return (Map.singleton abstract concretes)


type_interpretations = do 
  { reserved "type_interpretations"
  ; reservedOp "=" 
  ; mappings <- ( parseList (char '[' .>. ospaces) type_mapping  (freely2 comma) (freely2 $ char ']') )
  ; return mappings 
  }
  
  
freely x = ospaces .>. x .>. ospaces

freely2 x = ws .>. x .>. ws where
  ws = many (space <|> char '\n')
  
f .>. g = do { f ; g  ; return []}
  
ospaces = optional spaces  


abstract_concrete p = do 
  a <- p
  optional spaces
  reservedOp "="
  optional spaces
  c <- tuple p
  return (a,c)




lexer = P.makeTokenParser defs

parens      = P.parens lexer
identifier  = P.identifier lexer
reserved    = P.reserved lexer
reservedOp  = P.reservedOp lexer
angles      = P.angles lexer
comma       = P.comma lexer


basictype = liftM Atom identifier


basicterm = omitted <|> con  <|> liftM Var identifier


omitted = do 
  reserved "*"
  return Nil

lam = do 
  string "\\"
  spaces
  var <- many1 $ noneOf "\\.=>-()@, " 
  spaces
  string "."
  spaces
  term <- term
  return (Lam var term)
  
con = do
   x <- many1 $ oneOf "QWETYUIOPASDFGHJKLZXCVBNM'" 
   spaces
   string "::"
   spaces
   typ <- typ
   return (Con x typ)
 


sign = do 
  { abscon <- con 
  ; reservedOp "="
  ; conc <- parseList (string "<") term (reservedOp ",") (string ">")
  ; return (Sign abscon conc) 
  }


  
  
tuple p = parseList (string "<") p (reservedOp ",") (string ">")  
  
  

parseList start elem sep end = do 
  start
  content <- parseCons elem sep  
  end  
  return content


-- Build up a list of cells.  Try to parse the first cell, then figure out 
-- what ends the cell.

parseCons elem sep = 
    do first <- elem
       next <- parseNext elem sep 
       return (first : next)

-- The cell either ends with a comma, indicating that 1 or more cells follow,
-- or it doesn't, indicating that we're at the end of the cells for this line

parseNext elem sep =
    (sep >> parseCons elem sep )            -- Found comma?  More cells coming
    <|> (return [])                -- No comma?  Return [], no more cells


lines = many (eol <|> space)
signline = 
    do result <- sign
       eol                       -- end of line
       return result

-- The end of line character is \n
eol :: GenParser Char st Char
eol = char '\n'

run p x = parse p "" x

typ :: Parser Type
typ    = buildExpressionParser typetable simpletype
          <?> "expression"

simpletype =  parens typ 
          <|> basictype
          <?> "simple expression"

typetable = [ --[prefix "-" negate, prefix "+" id ]
             [postfix "?" (Option)]
           , [binary "->" (:->) AssocRight  {-, binary "/" (div) AssocLeft-} ]
--         , [binary "+" (+) AssocLeft, binary "-" (-)   AssocLeft ]
           ]
          
          
term   = buildExpressionParser termtable simpleterm
      <?> "expression"

simpleterm =  parens term 
          <|> basicterm
          <|> lam

          <?> "simple expression"

termtable   = [ --[prefix "-" negate, prefix "+" id ]
           [postfix "^" (NotNil)]
          , [binary "@" (App) AssocLeft  {-, binary "/" (div) AssocLeft-} ]
--          , [binary "+" (+) AssocLeft, binary "-" (-)   AssocLeft ]
          ]    
          
binary  name fun assoc = Infix (do{ reservedOp name; return fun }) assoc
prefix  name fun       = Prefix (do{ reservedOp name; return fun })
postfix name fun       = Postfix (do{ reservedOp name; return fun })


