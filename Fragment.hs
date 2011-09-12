module Fragments where

import ACG
import Tex
import Signature
import Reductions
import Inference
import Lexicon
import Data.Maybe
import Data.Char
import Data.List hiding (break)
import Prelude hiding ((^),break)
import Text.PrettyPrint.HughesPJ 
import System.IO.Unsafe


main =  sequence_ [ storeE ("../tex/fragment/"++name) ( signs) | (name,signs) <- fragment  ]

fragment = 
  [("constants" ,enum $ map (mathmode . typedTriple) ( constants ))
  ,("unaccusatives",toTex2 unaccusative)
  ,("unergatives",toTex2 unergative)
  ,("passs",toTex2 passs)
  ,("scope" ,toTex2 scope )
  ,("reflexives" ,toTex2 reflexives )
  
  ,("break" , mathmode $ typedTriple $ break ) 
  ,("johnbrokethewindow" , mathmode $ typedTriple $ close # ( break # window # NotNil john) )   
  ,("thewindowbroke" , mathmode $ typedTriple $ close # (break # window # nil_ ) )     
  ,("someonebrokethewindow" , mathmode $ typedTriple $ someone # ("x" ^ close # (break # window # NotNil x_)))

-- pass expl  
  ,("pass",mathmode $ typedTriple $ pass) 
  ,("pass_build",mathmode $ typedTriple $ pass # build)      
-- reflex expl
  ,("self",mathmode $ typedTriple $ self) 
  ,("self_like" , enum [mathmode $ unredTriple $ reduce $ self # like ,  mathmode $ typedTriple $ reduce $ self # like])      

  ,("run",mathmode $ typedTriple $ run) 
  ,("build",mathmode $ typedTriple $ build) 
  ,("think",mathmode $ typedTriple $ think)   
  ,("give",mathmode $ typedTriple $ give)     
  ,("sink",mathmode $ typedTriple $ sink)     

  ,("eat",mathmode $ typedTriple $ eat)   
  ,("shave",mathmode $ typedTriple $ shave)   


  , ("requireObjTriple" , mathmode $ typedTriple $ requireObj )
  , ("requireObjTriple" , mathmode $ typedAbstract $ requireObj )
  , ("requireSubjTriple", mathmode $ typedAbstract $ requireSubj )    
  ] -- ++ (map (\(x,y) -> (x,tex y) ) combinators) 




-- transitve
unaccusative = map (reduce  )
  [ (close # ) $ (requireSubj # sink)  # the_raft # john
  , (close # ) $ (pass # (requireSubj # sink)) # (NotNil john) # the_raft
  
  ,  (someone # (  "x" ^ close # ( (requireObj # (pass # (requireSubj # sink))) # x_ # the_raft ) ))

  , (close # ) $ (pass # (requireSubj # sink)) # nil_          # the_raft
  , (close # ) $  (noSubj # sink) # the_raft  
  ]
  
unergative = map (reduce )
  [ (close # ) $ (noObj # eat) # john
  ,   something # ("x" ^ ( close # ( (requireObj #eat) `App` (Var "x") `App` john)))
  , (close # ) $ (requireObj # eat)  # the_cake # john
  , (close # ) $ (pass # (requireObj # eat)) # (NotNil john) # the_cake
  ,  (someone # (  "x" ^ close # ( (requireObj # (pass # (requireObj # eat))) # x_ # the_cake ) ))
  , (close # ) $ (pass # (requireObj # eat)) # nil_          # the_cake
  ]  

  
passs = map (reduce . (close # ) )
  [ ( build)  # the_raft # john
  , (pass # ( build)) # (NotNil john) # the_raft
  , (sat # ( requireObj # (pass # ( build))  )) # someone # the_raft
  , (pass # ( build)) # nil_          # the_raft
  ]
  
e_ = (Var "E") :: Term ABS

flipT  = "f" ^ "g" ^ "h" ^ (Var "f" :: Term ABS) # (Var "h" :: Term ABS) # (Var "g" :: Term ABS)

scope =  map (reduce )
  [ everyone # ("y" ^ something # ( "x" ^ close # (build # x_ # y_ ) ) )
  , something # ("x" ^ everyone # ( "y" ^ close # (build # x_ # y_ ) ) )
  , everyone # ( "x" ^ close # (( noObj # eat) # x_) )
  , everyone # ("y" ^ something # ( "x" ^ close # ( (requireObj # eat ) # x_ # y_ ) ) )
  , something # ("x" ^ everyone # ( "y" ^ close # ( (requireObj # eat ) # x_ # y_ ) ) )
  ]
  
reflexives :: [Term ABS]
reflexives = 
  [ shave ] ++  map (reduce  )
  [ close # (shave # nil_ # john)
  , close # (self # (requireObj # shave) # john )
  , close # ((requireObj # shave) # bob # john)
  , close # ((pass # (requireObj # shave)) # (NotNil john) # bob)
  , close # ((pass # (requireObj # shave)) # nil_ # bob  )
  , everyone # ( "x" ^ (close # ( (noObj # shave) # x_)))
  , everyone # ( "x" ^ (close #  (self # (requireObj # shave) # x_)))
  ]
  
all_examples = concat [ unaccusative , unergative , passs ]
  

intrans = [ run ]


--examples i = map (\x -> (x,ex x)) i 


constants = map (Con . ABSC) $ ( ( [minBound..maxBound] :: [AbstractConstants]) 
  \\ [GIVE,INTRODUCE,REFL,SELF,ATNOON,TO,SOMETHING] )





--- main = do store "out" $ toTex2 constants 


toTex2 terms  = 
 enum [ hcat 
      [ mathmode $ typedTriple abstract   ]
    |  ( (abstract)) <- terms
    ] 

    
store name texdoc = writeFile (name ++ ".tex") (concat [preamble,render texdoc , postamble]) where
      preamble = "\\documentclass{article}\n\n  \\setlength{\\evensidemargin}{-1cm} \n \\setlength{\\oddsidemargin}{-1cm} \n \\begin{document} \n\n "
      postamble = "\n\\end{document}"


storeE name texdoc = writeFile (name ++ ".tex") (concat [render texdoc ]) where
      preamble = "\\documentclass{article}\n\n  \\setlength{\\evensidemargin}{-1cm} \n \\setlength{\\oddsidemargin}{-1cm} \n \\begin{document} \n\n "
      postamble = "\n\\end{document}"

-- constants = map (\x -> (  ("abstract constant : " ++ show x ++ (render $ mathmode  (hsep [tex " :: ", tex $ typeOf x])) , x )))$ map (Con . ABSC) $ enumFromTo minBound maxBound






addTypes = not False


unredTriple a  = array [ [ hcat [tex a ,  text " : "  <> (tex $ typeOf $ reduce a) , text " = "  ] ] , [pair]   ]  where
  
  pair =  array [string,semant]
  string = [text "\\langle" , tex . to String   $ a , text "" ]
  semant = [ text ","        , tex . to Semantic $ a , text "\\rangle" ]

triple a  =  array [ [ hcat [tex a , text " = "  ]] , [pair]   ]  where
  
  pair =  array [string,semant]
  string = [text "\\langle" , tex . reduce . to String   $ a , text "" ]
  semant = [ text ","        , tex . reduce . to Semantic $ a , text "\\rangle" ]


typedTriple a  =  array [ [ hcat [tex a ,  text " : "  <> (tex $ typ) , text " = "  ] ] , [pair]   ]  where
  typ = typeOf $ reduce a
  pair =  array [string,semant]
  string = [text "\\langle" , tex . reduce . to String   $ a , text " : " , tex $ to String $ typ , text ""         ]
  semant = [ text ","       , tex . reduce . to Semantic $ a , text " : " , tex $ to Semantic $ typ , text "\\rangle" ]


typedAbstract a  =  hcat [tex a ,  text " : "  <> (tex $ typ) ] where
  typ = typeOf $ reduce a













