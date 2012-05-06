module Frag where

import Tex
import Interpreter
import Grammar
import Term
import Data.Either
import MyError
import Term
import Type
import Parse
import Sign
import Grammar
import GrammarParser
import Inference
import Reductions
import MyError
import Commands
import Control.Monad.Error
import Control.Monad.Reader

import Data.Maybe
import Data.Either
import System.IO
import Control.Monad.Trans.State.Lazy

pair a b = (a,b)



main = interpret main' 

main' :: I ()
main' = sequence_ 
  [ execute (Load "opt.signs") 
  , saveConstants
  , saveTexAllConstants  
  , saveTexAllFragment frag 

  ]

outputDir = "../tex/fragment/"

frag = 
  [ pair "johnlikesmary"             "EC ( LIKES MARY JOHN )"
  
  , pair "readdune"              "( READ DUNE^  )" 
  , pair "johnreaddune"              "( READ DUNE^ JOHN )" 
  , pair "ecjohnreaddune"              "EC ( READ DUNE^ JOHN )"   
  , pair "johnreadsomething"          "(\\y.SOMETHING(\\x.EC(READ x^ y))) JOHN"
  , pair "ecjohnread"                "EC ( READ * JOHN ) "   
    , pair "johnread"                "( READ * JOHN ) "   
  , pair "readnull"                "READ * "    
  


   
  , pair "johnreadduneUO"            "EC ( (UO READtv) DUNE^ JOHN )"  
  , pair "johnreadsomethingUO"       "(\\y.SOMETHING(\\x.EC( (UO READtv) x^ y))) JOHN"
  , pair "johnreadUO"                "EC ( (UO READtv) * JOHN ) "      
  
  
  , pair "johnran"                  "( RUN JOHN )"
  , pair "ecjohnran"                  "EC ( RUN JOHN )"
  
  , pair "InjDUNE"                  "DUNE^"
  , pair "johnbrokethewindow"       "EC( BREAK THEWINDOW JOHN^)"
  , pair "thewindowbroke"           "EC( BREAK THEWINDOW *)"  
  , pair "someonebrokethewindow"    "SOMEONE ( \\x. EC ( BREAK THEWINDOW x^) )"
  
  , pair "everyoneeats"             "EVERYONE (\\x . EC ( EAT * x))"
  , pair "everyoneeatssomethingONS" "EVERYONE( \\s . SOMETHING ( \\o. EC ( EAT o^ s )))"
  , pair "everyoneeatssomethingOWS" "SOMETHING( \\o . EVERYONE ( \\s. EC ( EAT o^ s )))"
  
  , pair "johnsanktheship"          "SINK THESHIP JOHN^"
  , pair "theshipsank"              "SINK THESHIP *"  
  , pair "SELFSHAVEtv"                "SELF SHAVEtv"


  , pair "SHAVEwithObj"             "\\x.(SHAVE x^)"  
  , pair "johnshaves"               "EC (SHAVE * JOHN)"
  , pair "johnshaveshimself"        "EC (SELF (\\x.SHAVE x^) JOHN)"  
  , pair "johnshavesbob"            "EC ( SHAVE BOB^ JOHN)" 

  
  , pair "johnsheertzich"           "SCHEREN * JOHN"
  , pair "johnsheertzichzelf"       "SELF ( \\x . SCHEREN x^) JOHN"  
  , pair "UOTransitiveRead"         "UO READtv"    
  , pair "RequireObjREAD"           "RequireObj READ"    
  , pair "DropObjREAD"              "DropObj READ"    
  
  , pair "PASSdtvGIVE"              "PASSdtv GIVE'"

  , pair "theshipwasgivenbyjohntomaryPASS"  "EC ( (PASSdtv GIVE') (BY JOHN)^ (TO MARY)^ THESHIP )"
  , pair "theshipwasgiventomaryPASS"        "EC ( (PASSdtv GIVE') * (TO MARY)^ THESHIP )"  
  , pair "theshipwasgivenbyjohnPASS"        "EC ( (PASSdtv GIVE') (BY JOHN)^ * THESHIP )"  
  , pair "theshipwasgivenPASS"              "EC ( (PASSdtv GIVE') * * THESHIP )"    
  
  , pair "johngivesmarytheship"              "EC ( GIVE MARY THESHIP JOHN )"      

  , pair "givesmary"              "GIVE MARY"        
  , pair "givesmarytheship"              "GIVE MARY THESHIP"          
  , pair "johngivesmarytheshipvp"              "GIVE MARY THESHIP JOHN"          
  , pair "UOReadTv" "UO READtv"
  , pair "lambdav-UO-v-filler"  "\\v . UO v *"
  
  


      
  -- Reflexive Optional Objects  
  , pair "REFLjohnshavesbob"  "EC (  (REFL SHAVEtv) BOB^ JOHN  )"
  , pair "REFLjohnshaves"      "EC (  (REFL SHAVEtv) * JOHN        )"
  , pair "REFLverb"  "REFL SHAVEtv"    


  , pair "INTROpassnone"                  "INTRODUCEpass * * "
  , pair "INTROpassby"                    "\\x.INTRODUCEpass x^ * "
  , pair "INTROpassto"                    "\\x.INTRODUCEpass * x^ "
  , pair "INTROpassbyto"                  "\\x.\\y.INTRODUCEpass x^ y^ "

  -- For Passives UO's
  , pair "bobwasintroduced"              "EC ( (INTRODUCEpass) * * BOB                      )"
  , pair "bobwasintroducedtomary"        "EC ( (INTRODUCEpass) * (TO MARY)^ BOB             )"  
  , pair "bobwasintroducedbyjohn"         "EC ( INTRODUCEpass (BY JOHN)^ * BOB             )"  
  , pair "bobwasintroducedbyjohntomary"  "EC ( (INTRODUCEpass) (BY JOHN)^ (TO MARY)^ BOB    )" 
  , pair "bobwasintroducedbysomeonetosomeone"  "SOMEONE(\\y.(SOMEONE(\\x.(EC ( INTRODUCEpass (BY x)^ (TO y)^ BOB )))))" 
  , pair "bobwasintroducedtoeveryone"  "EVERYONE(\\y.(EC ( INTRODUCEpass * (TO y)^ BOB )))" 
  
  , pair "johnblinks"  "EC ( BLINK * JOHN )"
  , pair "johnblinksjohnseyes"  "EC ( BLINK (OF EYES JOHN)^ JOHN )"
  
    , pair "UOdtv"                    "\\v.\\z.UO(\\y.UO(\\x.v x y z))"    
  ]
  
  

(><) f g (a,b) = (f a, g b)
-- loadStrings grammar = map (\(file,term)


-- procesConsoleTerm :: Grammar -> String -> Either String Term

loadSign g (file,str) = 
   case procesConsoleTerm g str of
      Left error -> [Echo $ concat [error," in ",file]]
      Right term -> [Echo $ "\n-- " ++file ++ "\t" , SaveTex term  (Just $ concat [outputDir,file,".tex"])] 

--buildSaveCommands = map (\(file,term) -> SaveTex term (Just $ concat [outputDir,file,".tex"]) )

buildCommands g =  concatMap (loadSign g) 
  
saveTexAllFragment frag = do
  state <- get
  case  active_grammar state of 
   Nothing      -> liftIO $ putStrLn "no grammar loaded" 
   Just grammar -> run' (buildCommands grammar frag)

 
saveTexAllConstants = do
 state <- get
 case  active_grammar state of 
  Nothing      -> liftIO $  putStrLn "no grammar loaded" 
  Just grammar -> run' saveCommands 
    where saveCommands = map (\absterm -> SaveTex absterm (Just $ outputDir ++ show absterm ++".tex" )) (map abstract $ signs grammar)
 
      
saveConstants = do 
  state <- get
  let  texedSigns = enum $ map ( texSign . reduceSign ) (signs $ fromJust $ active_grammar  state) 
  liftIO $ writeFile "../tex/fragment/allConstants.tex"(render texedSigns)
  
