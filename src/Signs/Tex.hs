{-# LANGUAGE FlexibleInstances #-}
module Signs.Tex (tex,text,hcat,vcat,hsep,string2tex,Tex,parens,(<>),array,render,mathmode,enum,narray) where

import Text.PrettyPrint.HughesPJ
import Data.List


class Tex a where
  tex :: a -> Doc

instance Tex Char where
  tex '\\' = text "\\"
  tex '_' = text "\\_"
  tex ' ' = text "\\ "
  tex '\'' = text "'"
  tex x = text [x]

instance Tex [Char] where
  tex x = hcat $ map tex x

data Mode = Normal | Underline | Overline

string2tex [] = empty
string2tex ('_':t) = hcat [text "_",tex '{' ,string2tex t, tex '}']
string2tex (h:t)   = tex h <> string2tex t



mathmode x = tex "$" <> x <> tex "$"

sf x = hcat [tex "{" , text "\\sf " , x , tex "}"]

enum :: [Doc ] -> Doc
enum list = vcat $ [text "\\begin{enumerate}"] ++ map item list ++ [text "\\end{enumerate}"]
item x = text "\\item " <>  x

array :: [ [Doc] ] -> Doc
array list = vcat $
  [hcat [text "\\begin{array}[t]{" ,tex $ take (foldr max 0 $ map length list) (repeat 'l') ,tex "}"]]
   ++
   map arrayentry list
   ++
   [text "\\end{array}"]

narray :: [ [Doc] ] -> Doc
narray list = vcat $
  [hcat [text "\\begin{array}[t]{" ,tex $ concat $ take (foldr max 0 $ map length list) (repeat "l@{}") ,tex "}"]]
   ++
   map arrayentry list
   ++
   [text "\\end{array}"]

arrayentry x = hsep $ (++ [tex "\\\\"] ) $ intersperse (tex "&") x
