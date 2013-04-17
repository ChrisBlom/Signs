module Lexicon where

import Parse
import Term
import Type
import Reductions
import Inference

import Text.ParserCombinators.Parsec hiding (option)
import Text.ParserCombinators.Parsec.Expr
import Control.Monad
import Control.Arrow
import Data.Functor
import Data.List hiding (drop)
import Prelude hiding (drop)


data LexEntry = LexEntry
 { word :: String
 , denotation :: Term
 , ltyp  :: Type
 } deriving (Eq)

newtype Lexicon = Lexicon [LexEntry] deriving (Eq,Show)

pp (Lexicon x) = unlines $ map show x

-- instance Parse Lexicon where

lexicon :: Parser Lexicon
lexicon = do
     more  <- many1 entryline
     return $ Lexicon (more)
     
     
test2 = (fromRight $ parse term "" "(Read :: e -> e -> t)" ,fromRight $ parse typ ""  "e^{opt} -> e -> t" )
test3 = (fromRight $ parse term "" "(Read :: e -> e -> t)" ,fromRight $ parse typ ""  "e -> e^{opt} -> t" )

close :: (Term,Type) -> (Term,Type)

-- TODO : flip application order in close
close (tr,ty) = let fv = nextFreshVar tr in  case (tr,ty) of
  ( term ,  a :-> (Atom "t") ) ->  ( exists fv $ term `App` (Var fv) , Atom "t" )
  ( term ,  a :-> b :-> c )    ->  let (closedTerm,closedTyp) = close (term `App` (Var fv)  , b :-> c ) in 
                                   ( Lam fv $ closedTerm    , a :-> closedTyp  ) 


optionalize x = case  x of
  (term                         , typ ) | markerless typ  -> (term,typ)

  (term                         , Marker arg "opt" :-> res )  -> ( Lam "x'" $ CaseO (Var "x'") (term) (fst . close $ (term,arg:->res))         , Option arg :-> res )
  
  (term                         , arg :-> res ) | markerless res  -> (term,arg :-> res)
  
  (term                         , arg  :-> res )  -> let (resTerm,resTyp) = optionalize (term `App` (Var "fv") , res) in
                                                     (Lam "fv" resTerm , arg:->resTyp )
  

  x -> error . ("no case for " ++) . show $ x



instance Show LexEntry where
  show e = concat
    ["[[",word e,"]] = "
    , (show.denotation) e
    , " :: "
    , (show.ltyp) e
    ]

test p x = runParser p () "" x

spaced f = do 
  spaces
  res <- f
  spaces 
  return res

entryline = do
   word <- (many1 $ alphaNum) <?> "word"
   spaced $ string "="
   term <- term' <?> "term"
   spaced $ string ":"
   typ <- parseDef <?> "type"
   string ";"
   eol
   return $ LexEntry word term typ


parseLE = do
   word <- (many1 $ alphaNum) <?> "word"
   string "="
   term <- term' <?> "term"
   string ":"
   typ <- parseDef <?> "type"
   string ";"
   return $ LexEntry word term typ

instance Parse LexEntry where
  parseDef = parseLE
