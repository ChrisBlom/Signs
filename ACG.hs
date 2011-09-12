{-# LANGUAGE UndecidableInstances #-}

module ACG where

import Tex
import Signature
import Reductions
import Inference
import Lexicon
import Data.Maybe
import Data.Char
import Data.List 
import Prelude hiding ((^),break)
import Text.PrettyPrint.HughesPJ 

data ABS = Abstract
data STR = String
data SEM = Semantic


sat =  "r" ^ "q" ^ "y" ^ ( q_ # ( "x" ^  ( r_ # x_ # y_  )  )    ) where
  q_ ::  Term ABS
  [q_,r_,x_,y_,e_] = map mkVar "qrxye"

sink :: Term ABS
[sink,run,john,mary,bob,the_raft,the_cake,build,close,pass,something,everyone,atnoon_,give,introduce,eat,self,refl,shave,like,think,some,every,man,woman,nothing,break,window] = map (Con . ABSC) [SINK,RUN,J,M,B,RAFT,CAKE,BUILD,EC,PASS,SOMETHING,EVERYONE,ATNOON,GIVE,INTRODUCE,EAT,SELF,REFL,SHAVE,LIKE,THINK,SOME,EVERY,MAN,WOMAN,NOTHING,BREAK,WINDOW]

nil_ :: Term ABS
nil_ = Nil

mkVar x = Var [x]

x_ :: Term ABS
[v_,x_,y_,z_,w_,_1,_2,q_,r_,o_,s_] = map mkVar "vxyzw12qros"

close' x = close # x

-- combinators :
requireSubj = "v" ^ "x" ^ "y" ^ ( v_ # x_ # (NotNil y_)  ) 
requireObj = "v" ^ "x" ^ "y" ^ ( v_ # (NotNil x_) # y_  ) 

noSubj = "v" ^ "x" ^ ( v_ # x_ # nil_  ) 
noObj = "v" ^ "y" ^ ( v_ # nil_ # y_  )   




eps = epsilon

 
pair a b = (a,b)


demo n = putStrLn $ render $
  vcat $ map text  $ 
  [""
  ,(show $ reduce n) ++ " : " ++ (show $ typeOf n) 
  ,"\t|"
  , (" syn :\t|>" ++) $  asString $ syntactic 
  ,"\t| : " ++ (show $ to String $ typeOf n  )
  ,(" sem : \t|>" ++) $ pp $ reduce $ to Semantic $ n  
  ,"\t| : " ++ (show $ to Semantic $ typeOf n)  
  ]
   where syntactic =  reduce $ to String $  n
         semantic =  reduce $ to Semantic $  n


data AbstractConstants 
     = J 
     | B 
     | M
     | MAN
     | WOMAN
     | RAFT 
     | WINDOW
     | CAKE     
     | LIKE
     | EVERYONE 
  
     | SOMEONE      
     | SOME
     | EVERY
     | ATNOON 
     | TO
     | SELF
     | RUN
     | SINK  -- transitive / noSubjusative intrans   
     | BREAK  
     | REFL
     | EAT   -- transitive / noObjative intrans
     | SHAVE
     | BUILD -- transitive verb

     | INTRODUCE 
     | EC     -- existential closure
     | PASS
     | SOMETHING
     | NOTHING     
     | GIVE  -- ditransitive
     | THINK    
     deriving (Show,Eq,Enum,Bounded)


tv = np :->  np :-> vp  
iv =  np :-> vp    

instance Signature ABS where
  allConstants _ = map ABSC [minBound..maxBound]
  data ConstantOf ABS = ABSC AbstractConstants deriving (Eq)
  data AtomOf ABS     = NP | N | S | VP deriving (Show,Eq)
  typing (ABSC c) = case c of
    SINK       -> np :-> (Option np) :-> vp    
    BUILD      -> tv
    THINK      -> np :-> s :-> vp     
    LIKE       -> tv
    MAN        -> n
    WINDOW     -> np
    WOMAN      -> n
    GIVE       -> np :-> np :-> np :-> vp
    EAT        -> (Option np) :-> np :-> vp
    SHAVE      -> (Option np) :-> np :-> vp    
    BREAK      -> np :-> (Option np) :-> vp  
    J          -> np
    M          -> np
    B          -> np
    RAFT       -> np
    RUN        -> np :-> vp
    CAKE       -> np
    EC         -> vp :-> s
    SOMETHING -> (np :-> s) :-> s
    NOTHING   -> (np :-> s) :-> s
    SOME      -> n :-> (np :-> vp) :-> vp
    EVERY     -> n :-> (np :-> vp) :-> vp    
        

    EVERYONE  -> (np :-> s) :-> s
    SOMEONE   -> (np :-> s) :-> s    
    PASS      -> (np :-> np :-> vp ) :-> ((Option np) :-> np :-> vp)

    TO      -> np :-> vp :-> vp
    ATNOON  -> (np :-> vp) :-> (np :-> vp)
    INTRODUCE -> np :-> (Option np) :-> np :-> vp
    SELF    -> (np :-> np :-> vp) :->  np :-> vp
    REFL      -> (np :-> np :-> vp) :->  np :-> vp
    x -> error ( "untyped constant : " ++ show x )
vp  = Atom VP

instance Show (ConstantOf ABS) where  show (ABSC x) = show x
instance Tex  (ConstantOf ABS) where  tex  (ABSC x) =  sf . text . show $ x
instance Tex  (AtomOf ABS) where  tex  (x) =  at . text . (map toLower) . show $ x

at x = text "\\at{" <> x <> text "}"


isEventPredicate x = case x of Predicate _ -> True ; _ -> False

instance Signature SEM where
  data ConstantOf SEM =  Predicate String | Entity String   deriving (Eq)
  data AtomOf SEM     = E | T deriving (Show,Eq)
  typing ( (Entity _)) = e
  typing ( (Predicate c)) = case c of
    x | x `elem` (words "run' like' eat' sink' shave' build' think") -> et
    "Build'"    -> e :-> e :-> et
    "break'"    -> e :-> Option e :-> et    
    "give"     -> e :-> e :-> e :-> et
    "Exists"    -> (e :-> t) :-> t
    "Forall"    -> (e :-> t) :-> t    
    "And"       -> t :-> t :-> t
    "Impl"      -> t :-> t :-> t    
    "Not"       -> t :-> t 
    "AG"        -> e :-> e :-> t
    "PAT"       -> e :-> e :-> t
    "TIME"      -> e :-> e :-> t
    "GOAL"      -> e :-> e :-> t
    "Is"        -> e :-> e :-> t    
    "man'"      -> e :-> t
    "woman'"      -> e :-> t    
    "TOP"       -> t
    "introduce'" -> e :-> (Option e) :-> e :-> et
    _ -> error $ "missing case in sig SEM " ++ show c


instance Show (ConstantOf SEM)  where
  show ((Predicate x)) = x
  show ( (Entity x)) = x  


true = predicate "TOP"
(/\) :: Term SEM -> Term SEM -> Term SEM
f /\ g = (predicate "And") # f # g

conj :: [Term SEM] -> Term SEM
conj = foldr1 (/\)

f ==> g = (predicate "Impl") # f # g
f .= g = (predicate "Is") # f # g    
    
agent,patient :: Term SEM
agent = predicate "AG"
patient = predicate "PAT"
time = predicate "TIME"
goal = predicate "GOAL"
exists = predicate "Exists"
negate = predicate "Not"
for_all = predicate "Forall"
sink' = predicate "Sink'"
build' = predicate "Build'"
introduce' = predicate "Introduce'"

e = Atom E
t = Atom T    
et = e :-> t

sem_con = Con
predicate = Con . Predicate
entity = Con . Entity

p_ :: Term ABS
p_ = Var "p"





transitive :: String -> Term SEM
ditransitive    pred = "x" ^ "y" ^ "z" ^ "e" ^ (predicate pred # "e") /\ (agent # "e" # "y")  /\ (patient # "e" # "x") /\ (goal # "e" # "z")
transitive    pred = "x" ^ "y" ^ "e" ^ (predicate pred # "e") /\ (agent # "e" # "y")  /\ (patient # "e" # "x") 
unergativeI   pred = "x" ^ "e" ^       (predicate pred # "e") /\ (agent   # "e" # "x")
unaccusativeA pred = "x" ^ "y" ^ "e" ^ conj [predicate pred # "e" , CaseO (Var "y") ("q" ^ agent # "e" # (Var "q")) true  , patient # "e" # "x" ]
reflexiveA    pred = "x" ^ "y" ^ "e" ^ conj [predicate pred # "e" , (agent # "e" # "y") , (CaseO (Var "x") ("x'" ^ (patient # "e" # "x'")) (patient # "e" # "y") ) ]
existentialA  pred = "x" ^ "y" ^ "e" ^ conj [predicate pred # "e" , (agent # "e" # "y") , (CaseO (Var "x") ("q" ^ (patient # "e" # "q")) (exists # ( "p" ^ patient # "e" # p)) )] where p = Var "p" :: Term SEM

instance Lexicon ABS SEM where  
  atomicMap a = case a of
    N   -> e :-> t
    NP  -> e
    VP  -> e :-> t
    S   -> t
  constantMap (ABSC c) = case ( c) of
      J       -> entity "John'"
      M       -> entity "Mary'"
      B       -> entity "Bob'"
      RAFT    -> entity "the_raft'"
      CAKE    -> entity "the_cake'"      
      WINDOW  -> entity "the_window'"
      MAN     -> predicate "man'"
      WOMAN   -> predicate "woman'"
      
      RUN     -> unergativeI "run'"
         
      BUILD   -> transitive "build'"
      LIKE    -> transitive "like'"
      THINK   -> transitive "think"
      
      GIVE    -> ditransitive "give"
      
      SHAVE   -> reflexiveA "shave'"     
      
      BREAK   -> unaccusativeA "break'"      
      SINK    -> unaccusativeA "sink'"
            
      EAT     -> existentialA "eat'"
      
      SOMETHING -> "a" ^  ( (exists) # ("q" ^ (a # q ) )   )
      NOTHING ->   "a"  ^ ( ACG.negate # (exists # ("t" ^ (a # t) )  )  )
      SOMEONE -> "f"  ^ ( (exists) # ("x" ^ (f # x ) )   )      
      EVERYONE -> "f"  ^ ( for_all # ("x" ^ (f # x ) )   )         
      
      SOME    -> "f" ^ "g" ^ ( exists # ("x" ^ (f # x ) /\ (g #  x ) )   )      
      EVERY   -> "f" ^ "g" ^ ( for_all # ("x" ^ (f # x) ==> (g # x ) )   )     
      
      TO      ->  "v" ^ "a" ^ "e" ^ ( (a # e) /\ (goal # e # v ) )
      ATNOON  -> "v" ^ "x" ^ "e" ^ ( (v # x # e) /\ ( time # e # (entity "noon'") ) )
      INTRODUCE -> "p" ^ "g" ^ "a" ^ "e" ^ (
          (predicate "introduce'" # e) /\ (agent # e # a) /\ (patient # e # p) /\ 
          (CaseO g 
            ( "x" ^ (goal # e # x) )
            ( exists # ( "x" ^ (goal # e # x)  ) )  
          )
          )
      EC    -> "f" ^ exists # "f" where

      PASS -> "v" ^ "s" ^ "o" ^"e" ^ (
        ("f" ^ CaseO (s) ("S" ^ f # s') (exists # ( "S" ^ f # s') )) #   ("x" ^ (v # o # x # e )))

      SELF -> "v" ^ "a" ^ "e" ^ v # a # a # e
      REFL   -> "v" ^ "a" ^ v # a # a  
                         

      where v :: Term SEM ; [v,s,o,n,e,a,p,q,_2,_1,t,t',x,g,g',y,f,s'] = map mkVar "vsoneapq21tTxgGyfS"



someone = Con $ ABSC $ SOMEONE

string = Con . W
verb = Con . V

flip' :: Term STR
flip'  = "f" ^ "x" ^ "y" ^ (Var "f") `App` (Var "y") `App` (Var "x")


instance Lexicon ABS STR where  
  constantMap (ABSC c) = case ( c) of
     J     -> string "john"
     B     -> string "bob"
     M     -> string "mary"          
     MAN   -> string "man"
     WOMAN -> string "woman"          
     
     
     EAT   -> "o" ^ "s" ^ s .+ (string "eat") .+ (CaseO o ("g" ^ g) (eps) )
     SHAVE   -> "o" ^ "s" ^ s .+ (string "shave") .+ (CaseO o ("g" ^ g) (eps) )     
     
     
     BREAK   -> "o" ^ "s" ^ (CaseO s ("S" ^ "S" .+ (string "broke") .+ "o") ("o" .+ (string "broke") ) )             
     SINK    -> "o" ^ "s" ^ (CaseO (Var "s")  ("z" ^ ( z .+ (string "sink") .+ o ) )   (o .+ (string "sank")  )
        )
     RUN    -> "s" ^ ( s .+ (string "run") )        
     BUILD  -> "o" ^ "s" ^ ( s .+ (string "build") .+ o)
     THINK  -> "o" ^ "s" ^ ( s .+ (string "think") .+ o)     
     LIKE   -> "o" ^ "s" ^ ( s .+ (string "like") .+ o)     
     GIVE  -> "p" ^ "g" ^ "a" ^ ( a .+ (string "give") .+ g .+ p  )
     PASS -> "v" ^ "o" ^ "s" ^  (v # (CaseO o ("x" ^ string "by" .+ "x") eps) # (s .+ string "was"))
     RAFT    ->  string "the raft"
     WINDOW  ->  string "the window"     
     CAKE    ->  string "the cake"     
     EC    -> "f" ^ "f"
     SELF    -> "v" ^ "s" ^ v # (string "self") # s
     SOMETHING -> "f" ^ ("f" # (string "something") )
     NOTHING -> "f" ^ ("f" # (string "nothing") )     
     SOME  ->  "f" ^ "g" ^ ("g" # (string "some") .+ (f)) 
     EVERY ->  "f" ^ "g" ^ ("g" # (string "every") .+ (f))        
     SOMEONE -> "f" ^ ("f" # (string "someone") )     
     EVERYONE -> "f" ^ ("f" # (string "everyone") )        
     TO     -> "v" ^ "o" ^ o .+ (Con $ W "to") .+ v
     ATNOON -> "v" ^ "x" ^ ( (v # x) .+ (string "at noon")  ) 
     INTRODUCE -> "p" ^ "g" ^ "a" ^ ( a  .+ (string "introduce") .+ p .+ (CaseO g ( "x" ^ (string "to") .+ x ) eps )  )
     REFL    -> "v" ^ "x"  ^ v # x # eps

      
    where
      s :: Term STR
      [s,o,z,f,v,x,a,p,g,y,e] = map mkVar "sozfvxapgye"
  atomicMap a = case a of
    NP  -> str
    N   -> str
    S   -> str
    VP  -> str

asString :: Term STR -> String
asString term = case term of 
  Var v -> show v
  Con Eps   -> "_"
  Con (W x)   -> x
  Con (CCat )   -> show CCat

  App (App (Con CCat) (Con Eps)) b ->  concat [asString b]
  App (App (Con CCat) a) (Con Eps)  ->  concat [asString a]
  App (App (Con CCat) a) b ->  concat [asString a , "+" , asString b]
  App a b -> "("++asString a ++ " " ++ asString b++")"
--  Pair a b -> asString a ++ " , "++ asString b
  Lam v t  ->  "\\" ++ v ++ "." ++ asString t
  Snd a -> asString a
  Fst a -> asString a  
  NotNil x -> "[" ++ asString x ++ "]"
  Nil -> "*"
  CaseO m l r -> concat ["option(",asString m ,", ",asString l,",",asString r,")"]  
  _ -> error $ "error in asString for " ++ show term


pp t = concat $ case  t of
 Lam v t     -> ["\\" , v , ".", pp t] 
 (App (Con ( (Predicate "Exists"))) (Lam v t)) -> [ "Exists "  , show v , "." , pp t ]
 (App (Con ( (Predicate "Forall"))) (Lam v t)) -> [ "Forall "  , show v , "." , pp t ] 
 (App (App (Con ( (Predicate "And"))) a) b) ->  [pp a , " /\\ ", pp b,")" ]
 (App (App (Con ( (Predicate "Impl"))) a) b) ->  [pp a , " => ", pp b,")" ]   
 (App (App (Con ( (Predicate "Is"))) a) b) ->  [pp a , " = ", pp b,")" ]  
 App (App (App (f) a) b) c ->  [pp f , "(" , pp a ,",", pp b,",", pp c ,")" ] 
 App (App (f) a) b ->  [pp f , "(" , pp a ,",", pp b,")" ] 
 App m n ->  [pp m,"(" , pp n ,")"]
 Con ((Predicate "TOP")) -> ["true"]
 
 Con s  -> [show s]
 Var v  -> [show v]   
 Nil -> ["*"]
 NotNil x ->  ["{" , pp x , "}"]
 CaseO m l r ->  ["option(",pp m ,", ",pp l,",",pp r,")"]

instance Show (ConstantOf STR) where show (W s) = show s ; show Eps = "" ; show CCat = "+"
instance Signature STR where
  data ConstantOf STR = W String | V String | Eps | CCat deriving (Eq)
  data AtomOf STR     = STR deriving (Show,Eq)
  typing c = case c of
     Eps      -> str
     CCat     -> str :-> str :-> str
     W _      -> str
     V _      -> str :-> str


instance Tex  (ConstantOf STR) where  tex  (W x) = text $ x ; tex  (V x) = text $ x ; tex Eps = text "\\epsilon" ; tex CCat = text "\\bullet"
instance Tex  (AtomOf STR) where  tex  (STR) = sf $ text "f"

-- string concat    

l .+ r  = (Con CCat) # l # r  

epsilon = Con Eps
str = Atom STR
strstr = str :-> str

np = Atom NP
n = Atom N
s = Atom S



 
instance Tex  (ConstantOf SEM) where  
  tex ((Entity x)) = tex $ map toLower $  x
  tex  ( (Predicate x)) = case x of 
       "Exists" -> text "\\exists "
       "Forall" -> text "\\forall "       
       "And"    -> text "\\wedge " 
       "Is"     -> text " = "        
       "TOP"    -> text "\\top "
       "Not"    -> text "\\neg "
       "Impl"    -> text "\\rightarrow "       
       y      -> hcat [text "\\sem{" , tex $ y , text "}"]
       
instance Tex  (AtomOf SEM) where  tex  (x) = text $ concat [show x]


primeIfUpper [c] 
  | isUpper c   = [toLower c , '\'' ]
  | otherwise   = [c]
primeIfUpper x = x  


instance (Tex a,Tex b) => Tex (a,b) where
  tex (a,b) = hsep [text "\\langle " , tex a  , text " , " , tex b ,text "\\rangle" ]

instance Tex (Term ABS) where
 tex term = case term of
  Nil   -> text "\\ast"
  NotNil a -> hcat [text "\\overline{ " , tex a , text "}" ]
  Var c -> tex $ primeIfUpper c
  Con s -> hcat [text "\\abs{" , tex s , text "}" ]
  App m n -> hcat $  [tex m,parens $ tex n]  
--  App m n -> parens $ hsep  $  [tex m,tex ' ',tex n]
  Pair m n ->  hcat [text"\\langle", tex m ,text ",", tex n ,text"\\rangle"]
  L m  ->   hcat [text"inl(", tex m,text")" ]
  R m  ->   hcat [text"inr(", tex m,text")" ]
  Lam v n ->  hcat[text" \\lambda ", tex $ primeIfUpper v,text" . ", tex n ,text""]
  Fst n ->  hcat [text"fst" , parens $  tex n ]
  Snd n ->  hcat [text"snd" , parens $ tex n ]
  Case m l r ->  hcat [text"case(",tex m ,text", ",tex l,text",",tex r,text")"]
  CaseO m l r ->  hcat [text"option(",tex m ,text", ",tex l,text",",tex r,text")"]
  
 
instance Tex (Type ABS) where  
  tex t = let at x = text "\\at{ " <> x <> text "}" in case t of
    Atom a -> at $ tex a
    TVar v -> text $ map toLower $  v
    (a :-> b) -> hsep [(if (atomicType a) then id else parens) $ tex a, text "\\rightarrow" , tex b] 
    (a :*: b) -> hsep [tex a , text "\\otimes" , tex b]
    (a :+: b) -> hsep [tex a , text "\\oplus" , tex b]
    (Option a) -> hcat [tex a ,text "^?"]            
    Unit -> text $ "1" 
    Void -> text $ "0"    
  
instance Tex (Type SEM) where  
  tex t = let at x = text "\\at{ " <> x <> text "}" in case t of
    Atom a -> tex $ map toLower $ show a
    TVar v -> text $ map toLower $ v
    (a :-> b) -> hsep [(if (atomicType a) then id else parens) $ tex a, tex b]  
    (a :*: b) -> hsep [tex a , text "\\otimes" , tex b]
    (a :+: b) -> hsep [tex a , text "\\oplus" , tex b]
    (Option a) -> hcat [tex a ,text "^?"]            
    Unit -> text $ "1" 
    Void -> text $ "0"     

instance Tex (Type STR) where  
  tex t = let at x = text "\\at{ " <> x <> text "}" in case t of
    Atom STR -> tex $ "f"
    TVar v -> text $ map toLower $  v
    (a :-> b) -> hsep [(if (atomicType a) then id else parens) $ tex a, tex b]  
    (a :*: b) -> hsep [tex a , text "\\otimes" , tex b]
    (a :+: b) -> hsep [tex a , text "\\oplus" , tex b]
    (Option a) -> hcat [tex a ,text "^?"]            
    Unit -> text $ "1" 
    Void -> text $ "0"     
  
  
instance Tex (Term STR) where
 tex term = case term of
  Nil   -> text "\\ast"
  NotNil a -> hcat [text "\\overline{ " , tex a , text "}" ]
  Var c -> text $ primeIfUpper c
  Con (W s) -> hcat [text "\\str{" , tex  s , text "}" ]
  Con Eps -> tex "\\epsilon"
  Con CCat -> tex CCat
 -- App (App v@(Var _) a) b -> hsep [tex v,parens $ tex a <> comma <> tex b]
  App (App (Con CCat) (Con Eps)) b -> hsep [tex b]
  App (App (Con CCat) a) (Con Eps) -> hsep [tex a]
  App (App (Con CCat) a) b -> hsep [tex a,tex CCat,tex b]
  App m n -> hsep $  [tex m,parens $ tex n]
  Pair m n ->  hcat [text"\\langle", tex m ,text ",", tex n ,text"\\rangle"]
  L m  ->   hcat [text"inl(", tex m,text")" ]
  R m  ->   hcat [text"inr(", tex m,text")" ]
  Lam v n ->  hcat[text" \\lambda ", tex $ primeIfUpper v,text" . ", tex n ,text" "]
  Fst n ->  hcat [text"fst" , parens $  tex n ]
  Snd n ->  hcat [text"snd" , parens $ tex n ]
  Case m l r ->  hcat [text"case(",tex m ,text", ",tex l,text",",tex r,text")"]
  CaseO m l r ->  hcat [text"option(",tex m ,text", ",tex l,text",",tex r,text")"]


instance Tex (Term SEM) where
 tex term = case term of
  Nil   -> text "\\ast"
  NotNil a -> hcat [text "\\overline{" , tex a , text "}" ]
  Var c -> tex $ primeIfUpper c
  Con s ->  tex s 
  
  App (App impl@(Con ( (Predicate "Impl"))) l) r -> hsep [ tex l , tex impl , tex r ]  
  App (App and@(Con ( (Predicate "And"))) l) r -> hsep [ tex l , tex and , tex r ]
  App (App is@(Con ( (Predicate "Is"))) l) r -> hsep [ tex l , tex is , tex r ]
  (App exi@(Con ( (Predicate "Exists"))) ( Lam x m)) -> hsep [ tex exi , tex $ primeIfUpper x , tex '.' , tex m ]
  (App exi@(Con ( (Predicate "Forall"))) ( Lam x m)) -> hsep [ tex exi , tex $ primeIfUpper x , tex '.' , tex m ]  
  App (App (Con m) n) o | isEventPredicate m -> hsep [ tex m , text "(" , tex n , tex ',' , tex o, text ")"   ]
  App (Con m) n | isEventPredicate m -> hsep [ tex m , text "(" , tex n, text ")"   ] 
  App m n -> hcat $  [tex m,parens $ tex n] 
  Pair m n ->  hcat [text"\\langle", tex m ,text ",", tex n ,text"\\rangle"]
  L m  ->   hcat [text"inl(", tex m,text")" ]
  R m  ->   hcat [text"inr(", tex m,text")" ]
  Lam v n ->  hcat[text" \\lambda ", tex $ primeIfUpper v,text" . ", tex n ,text" "]
  Fst n ->  hcat [text"fst" , parens $  tex n ]
  Snd n ->  hcat [text"snd" , parens $ tex n ]
  Case m l r ->  hcat [text"case(",tex m ,text", ",tex l,text",",tex r,text")"]
  CaseO m l r ->  hcat [text"option(",tex m ,text", ",tex l,text",",tex r,text")"]




