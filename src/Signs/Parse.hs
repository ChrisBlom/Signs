module Signs.Parse
  ( Parse
  , Parser(..)
  , parse
  , qparse
  , parseDef
  , binary , prefix , postfix
  , identifier
  , P.whiteSpace
  , pparens
  , reservedOp
  , reserved
  , string
  , space
  , comma
  , optional
  , spaces
  , lower
  , parseList
  , ParseError
  , fromRight
  , many
  , many1
  , alphaNum
  , choice
  , (<|>)
  , (<?>)
  , newline
  , ws
  , eol
  , String
  , parseFileName
  ) where

import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Prim
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Combinator

fromRight (Right x) = x
fromRight x = error $  "fromRight error : " ++ show x

class Parse a where
  parseDef :: Parser a
  qparse :: String -> Either ParseError a

  qparse string =  parse parseDef "" string

defs = emptyDef { commentStart   = "/*"
                , commentEnd     = "*\\"
                , commentLine    = "//"
                , nestedComments = True
                , identStart     = lower
                , identLetter	 = alphaNum <|> oneOf "_'"
                , opStart	 = opLetter defs
                , opLetter	 = oneOf "->\\/+"
                , reservedOpNames= ["->","+","/\\@","=",":"]
                , reservedNames  = words "\\ option forall id exists OPT DEOPT :: PAT AG GOAL TRUE FALSE"
                , caseSensitive  = True
                }

lexer       = P.makeTokenParser defs
pparens     = P.parens lexer
identifier  = P.identifier lexer
reserved    = P.reserved lexer
reservedOp  = P.reservedOp lexer
angles      = P.angles lexer
comma       = P.comma lexer


binary  name fun assoc = Infix   (do{ reservedOp name; return fun }) assoc
prefix  name fun       = Prefix  (do{ reservedOp name; return fun })
postfix name fun       = Postfix (do{ reservedOp name; return fun })

ws :: Parser String
ws = many (space <|> newline)


parseList start elem sep end = do
  start
  content <- parseCons elem (sep >> ws)
  ws
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


-- The end of line character is \n
eol :: GenParser Char st Char
eol = newline


-- parser for the command language
parseFileName :: String -> Parser String
parseFileName defaultExtension = do
  name <- many1 ( alphaNum <|> char '.' <|> char '/' )
  maybeExt <- optionMaybe $
              do { string "."
                 ; ext <- many1 alphaNum
                 ; return ext
                 }
  return (name ++ (maybe ("."++defaultExtension) ("."++) maybeExt) )
  <?> "filename"
