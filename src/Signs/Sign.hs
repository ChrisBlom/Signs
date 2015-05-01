module Signs.Sign (Type(..), Term(..),Sign(..),abstract_concrete,abstract_concrete',asList,reduceSign) where

import Signs.Type
import Signs.Inference
import Signs.Term
import Signs.Reductions
import Signs.Parse
import Signs.Tex
import Data.List

-- Sign datatype : an abstract term with multiple untyped concrete terms
data Sign = Sign
  { abstract :: Term
  , concretes :: [Term]
  } deriving (Eq)

instance Tex Sign where
  tex = typedTripleTex

-- reduces all terms in a sign
reduceSign (Sign a c) = Sign (reduce a) (map reduce c)

-- Pretty prints a sign
typedTripleTex (Sign absTerm [stringTerm,semTerm])  = case typeOfE $ reduce absTerm of
  Right absTyp -> array [ [ hcat [tex absTerm ,  text " : "  <> (texStyle "ABSTRACT" absTyp) , text " = "  ] ] , [pair]   ]
    where pair =  array [string,semant]
          string = [text "\\langle" ,  texTerm "STRING" stringTerm  ]
          semant = [ text ","       ,  texTerm "SEM" semTerm  , text "\\rangle"]
  Left error -> text $ "typedTriple : " ++ show error

asList (Sign a b) = a : b

instance Show Sign where
 show s = concat
  [ case abstract s of
      constant@(Con s t) -> show constant ++ " :: " ++ show t
      x -> show x ++ " :: " ++ (case typeOfE x of Right typ -> show typ ; Left err -> show err)
  , " = \n\t< "
  ,   intercalate "\n\t, " $
        map ( \term -> concat [show $ reduce term ," :: ",(show . typeOfE . reduce) term]) (concretes s)
  , "\n \t>"
  ]

instance Parse Sign where parseDef = signParser

signParser = do
  { abscon <- con
  ; reservedOp "="
  ; concretes <- tupleOf term
  ; return (Sign abscon concretes)
  }

tupleOf p = parseList (string "<") (do {ws ; p}) (do ws ; reservedOp "," ; ws) (ws >> string ">")

-- combinator to parse signs like  content1 = < content2 .... >
abstract_concrete p = abstract_concrete' p p

abstract_concrete' q p = do
  a <- q
  optional spaces
  reservedOp "="
  optional spaces
  c <- tupleOf p
  return (a,c)
