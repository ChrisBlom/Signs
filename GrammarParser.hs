module GrammarParser where

import Sign

import Sentence
import Inference
import Grammar
import Type
import Parse
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

type TypeInterpretation = Map.Map Type [Type]

instance Parse Grammar where parseDef = grammar

-- load and parse a grammar file
loadGrammar :: FilePath -> IO (Either ParseError Grammar)
loadGrammar path = do
  file <- readFile path  
  return (parse grammar path file)

-- grammar parser
grammar = do 
  { sigNames <- signatures
  ; lines
  ; typeMappings <- type_interpretations
  ; lines
  ; signs <- many1 signline
  ; lines
  ; return (Grammar sigNames (Map.unions typeMappings) signs )
  } <?> "grammar"


signatures = do 
  { reserved "signatures"  ; optional spaces
  ; (abstract,concretes) <- abstract_concrete capitalized
  ; return (abstract,concretes)
  } <?> "a list of signature definitions, each on a single line"

capitalized = do { u <- upper ; l <- many1 lower ; return (u:l) } <?> "capitalized"
    

type_mapping = do
  (abstract,concretes) <- abstract_concrete' atom (parseDef :: Parser Type)
  return (Map.singleton abstract concretes)


type_interpretations = do
  { reserved "type_interpretations"
  ; reservedOp "=" 
  ; ws
  ; mappings <- ( parseList (char '[' >> ws) type_mapping  (ws >> comma >> ws) (ws >> char ']') )
  ; return  mappings 
  } <?> "a type interpreation function definitions, of the form  [ 'abstract1' -> 'concrete1' , 'abstract2' -> concrete2' ]"
  
  
freely x = ospaces .>. x .>. ospaces

freely2 x = ws .>. x .>. ws where
  ws = many (space <|> char '\n')
  
f .>. g = do { f ; g  ; return []}

ospaces :: Parser String
ospaces = many (space <|> char '\n')


lines = many (eol <|> space)
signline =
    do result <- (parseDef :: Parser Sign)   
       many (char ' ')
       eol                       -- end of line
       return result
