module Type where

import Parse
import Data.Char
import Tex

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Control.Monad

instance Parse Type where parseDef = typ

-- the datatype for types
infixr 6 :->
data Type
  = Atom String
  | TVar String
  | (Type) :-> (Type)
  | (Type) :+: (Type)
  | (Type) :*: (Type)
  | Option Type
  | Marker Type String
  | Unit
  | Void
  deriving (Ord,Eq) -- ,Show)


typeT = Atom "t"
typeE = Atom "e"

markerless t = case t of
  a :-> b   -> markerless a && markerless b
  a :+: b   -> markerless a && markerless b
  a :*: b   -> markerless a && markerless b
  Option a  -> markerless a
  Marker _ _ -> True
  _         -> False


-- Parser for types
atom :: Parser Type
atom = liftM Atom identifier <?> "atomic type"



isBoolean t = case t of 
  Atom "t" -> True
  _ :-> x  -> isBoolean x
  _        -> False


typ :: Parser Type
-- typ = buildExpressionParser typetable simpletype <?> "type expression"
typ = buildExpressionParser typetable markedtype <?> "type expression"



typetable = [ [postfix "?" Option ]
       --    ,  [binary "*" (:*:) AssocLeft]
       --    ,  [binary "+"  (:+:) AssocLeft]
           ,  [binary "->" (:->) AssocRight ]
           ]
           

markedtype = do
  typ <- simpletype 
  maybeMarker <- optionMaybe $ (do 
    { string "^{"         
    ; marker <- many1 alphaNum <?> "marker string"
    ; string "}"             
    ; return marker
    } <?> "marker")     
  spaces  
  return $ case maybeMarker of 
    Just marker -> Marker typ marker
    Nothing -> typ
  where simpletype =  pparens typ
           <|> atom
           <?> "simple expression"
  
  
(f .?. d) o = case o of 
  Just o' -> f o'
  Nothing -> d

-- Show instance for types
instance Show Type where
  show t = case t of
    Atom a -> map toLower a
    TVar v -> map toUpper v
    (a :-> b) -> if (isAtomic a) then concat [show a , " -> " , show b] else concat [sparens $ show a , "->" , show b]
    (a :*: b) -> sparens$ concat [show a , " * " , show b]
    (a :+: b) -> sparens$ concat [show a , " + " , show b]
    (Option a) -> concat [rankparens a $ show a , "?"]
    (Marker a str) -> concat [rankparens a $ show a , "^{" , str , "}" ]    
    Unit -> "1"
    Void -> "0"
    where rankparens x s = if isAtomic x then s else sparens s


showAbbt t = case t of
    Atom a -> map toLower a
    TVar v -> map toUpper v
    (a :-> b) -> if (isAtomic a) 
      then concat [showAbbt a , showAbbt b] 
       else concat [sparens $ showAbbt a ,showAbbt b]
    (a :*: b) -> sparens$ concat [showAbbt a , "*" , showAbbt b]
    (a :+: b) -> sparens$ concat [showAbbt a , "+" , showAbbt b]
    (Option a) -> concat [rankparens a $ showAbbt a , "?"]
    (Marker a str) -> concat [rankparens a $ showAbbt a , "{" , str , "}"]       
    Unit -> "1"
    Void -> "0"
    where rankparens x s = if isAtomic x then s else sparens s

sparens a = concat ["(",a,")"]


order typ = case typ of
  Atom _      -> 0
  TVar _      -> 0
  a :-> b     -> max (order a + 1 ) (order b)
  a :*: b     -> max (order a) (order b)
  a :+: b     -> max (order a) (order b)
  (Option a)  -> order a
  (Marker a str)  -> order a  
  Unit        -> 0
  Void        -> 0

atomicType = (==0) . order
isAtomic = atomicType


at x = text "\\at{ " <> x <> text "}"
 

texStyle' "ABSTRACT" t = let ; tex' = texStyle' "ABSTRACT" in case t of
    Atom a -> string2tex a
    TVar v -> text $ map toLower $  v
    (a :-> b) -> hsep [(if (atomicType a) then id else parens) $ tex' a, text "\\rightarrow" , tex' b] 
    (a :*: b) -> hsep [tex' a , text "\\otimes" , tex' b]
    (a :+: b) -> hsep [tex' a , text "\\oplus" , tex' b]
    (Option a) -> hcat [tex' a ,text "^?"]            
    (Marker a str ) -> hcat [tex' a ,text "^{\\at{" , text str ,text "}}"]       
    Unit -> text $ "1" 
    Void -> text $ "0"    

texStyle "ABSTRACT" t = at $ texStyle' "ABSTRACT" t
   
  
texStyle "SEM" t = let tex' = texStyle "SEM" in case t of
    Atom a -> string2tex $ map toLower a
    TVar v -> text $ map toLower $ v
    (a :-> b) -> hcat [(if (atomicType a) then id else parens) $ tex' a, tex' b]  
    (a :*: b) -> hsep [tex' a , text "\\otimes" , tex' b]
    (a :+: b) -> hsep [tex' a , text "\\oplus" , tex' b]
    (Option a) -> hcat [tex' a ,text "^?"]       
    (Marker a str ) -> hcat [tex' a ,text "^{\\at{" , text str , text "}}"]        
    Unit -> text $ "1" 
    Void -> text $ "0"     

texStyle "STRING" t = let tex' = texStyle "STRING" in case t of
    Atom x -> string2tex' x
    TVar v -> text $ map toLower $  v
    (a :-> b) -> hcat [(if (atomicType a) then id else parens) $ tex' a, tex' b]  
    (a :*: b) -> hsep [tex' a  , text "\\otimes" , tex' b]
    (a :+: b) -> hsep [tex' a  , text "\\oplus"  , tex' b]
    (Option a) -> hcat [tex' a ,text "^?"]     
    (Marker a str ) -> hcat [tex' a ,text "^{\\at{" ,text str , text "}}"]                   
    Unit -> text $ "1" 
    Void -> text $ "0"     


string2tex' [] = text ""
string2tex' ['f'] = text "\\smallf"
string2tex' ('_':t) = hcat [text "_",tex '{' ,string2tex' t, tex '}']
string2tex' (h:t)   = tex h <> string2tex' t

