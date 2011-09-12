module Tex where

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

instance Tex String where
  tex x = hcat $ map tex x


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

arrayentry x = hsep $ (++ [tex "\\\\"] ) $ intersperse (tex "&") x
