module Sign (Type(..), Term(..),Sign(..),abstract_concrete,abstract_concrete',asList,reduceSign) where

import Type
import Inference
import Term
import Reductions
import Parse
import Tex
import Data.List

-- Sign datatype : an abstract term with multiple untyped concrete terms
data Sign = Sign
  { abstract :: Term
  , concretes :: [Term]
  } deriving (Eq)

instance Tex Sign where
  tex s = typedTriple s


-- reduces all terms in a sign
reduceSign (Sign a c) = Sign (reduce a) (map reduce c)

-- Pretty prints a sign
typedTriple (Sign absTerm [stringTerm,semTerm])  = case typeOfE $ reduce absTerm of 
  Right absTyp -> array [ [ hcat [tex absTerm ,  text " : "  <> (texStyle "ABSTRACT" $ absTyp) , text " = "  ] ] , [pair]   ] 
    where pair =  array [string,semant]
          string = [text "\\langle" ,  texTerm "STRING" stringTerm  ]
          semant = [ text ","       ,  texTerm "SEM" semTerm  , text "\\rangle"]
  Left error -> text $ "typedTriple : " ++  error

asList (Sign a b) = a : b

instance Show Sign where
 show s = concat 
  [ case (abstract s) of 
      c@(Con s t) -> show c ++ " :: " ++ show t
      x -> show x ++ " :: " ++ (case typeOfE x of Right typ -> show typ ; Left err -> err)
  , " = \n\t< "
  ,   concat $ intersperse "\n\t, " (map (\x -> ((show . reduce) x) ++ " :: " ++ (show $ typeOfE $ reduce x)) (concretes s))
  , "\n \t>"
  ]

instance Parse Sign where parseDef = signParser

signParser = do
  { abscon <- con
  ; reservedOp "="
  ; conc <- tuple term
  ; return (Sign abscon conc)
  }

tuple p = parseList (string "<") (do {ws ; p}) (do ws ; reservedOp "," ; ws) (ws >> string ">")

-- combinator to parse signs like  content1 = < content2 .... >
abstract_concrete p = do
  a <- p
  optional spaces
  reservedOp "="
  optional spaces
  c <- tuple p
  return (a,c)

abstract_concrete' q p = do
  a <- q
  optional spaces
  reservedOp "="
  optional spaces
  c <- tuple p
  return (a,c)
