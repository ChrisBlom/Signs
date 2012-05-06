module Term  where

{- 
- lambda term ADT
- parser
- pretty printer
- export to latex
-}


import Type
import Tex
import Prelude hiding (drop)
import Parse
import Data.Char

import Text.ParserCombinators.Parsec hiding (option)
import Text.ParserCombinators.Parsec.Expr
import Control.Monad
import Data.List hiding (drop)


import qualified Data.Map as Map

tests = 
      ["\\x.x"
      ,"\\x.\\f.\\d.option(x,f,d)"
      ]


type Variable = String

constantName (Con s _) = s

-- data type of terms
infixl 9 `App`
data Term
  -- basic
  = Var Variable
  | Con String Type
  | App (Term) (Term)
  | Lam Variable (Term)
  -- tuples
  | Pair (Term) (Term)
  | Fst (Term )
  | Snd (Term )
  -- sums (not used atm)
  | L (Term)
  | R (Term)
  | Case (Term) (Term) (Term)
  -- option
  | Nil
  | NotNil (Term)
  | CaseO (Term) (Term) (Term)
  deriving (Ord,Eq)

instance Parse Term where parseDef = term

term   = buildExpressionParser termtable (simpleterm term con) 
      <?> "expression"

term'   = buildExpressionParser termtable (simpleterm term' con')
      <?> "expression"


ident = identifier 

var = liftM Var ident


simpleterm trm constant = do {
 t <- choice
  [ pparens trm
  , omitted 
  , emptystring
  , identity
  , constant 
  , lam ident trm
  , forall_ ident trm
  , exists_ ident trm
  , option trm
  , var
-- , app (pparens trm <|> constant <|> var) (pparens trm)
  ] 
 ; spaces 
 ; return t
 }  <?> "simple expression"



app m n = m `chainl1` ( do { string " " ; n' <- n ; return (flip App) } )

                    
t = Atom "t"
tt = t :-> t
f = Atom "f" 
ff = f :-> f
fff = f :-> f :-> f


-- Parsing lambda terms
omitted     = reserved "*" >> return Nil
emptystring = reserved "_" >> return (Con "Eps" (Atom "f"))


identity = do
  reserved "id"
  return (Lam "x" (Var "x") )


  

lam vr trm = do
  string "\\"
  (optional spaces)
  var <- vr
  (optional spaces)
  string "."
  spaces
  term <- trm
  return (Lam var term)


forall_ vr trm = do 
  reserved "forall"
  spaces
  var <- vr
  spaces
  string "."
  spaces 
  term <- trm
  return (for_all var term)
  <?> "universal quantifier expression"
  
exists_ vr trm = do 
  reserved "exists"
  spaces
  var <- vr
  spaces
  string "."
  spaces 
  term <- trm
  return (exists var term)
  <?> "existential quantifier expression"

con  = choice 
 [ agent 
 , patient 
 , goal
 , do
   char '\"'
   x <- many $ noneOf "\""
   char '\"'
   return (Con x (Atom "f"))
 , do
   x <- upper
   xs <- many $ alphaNum <|> oneOf "_'-"
   spaces
   reserved "::"
   spaces
   typ <- typ
   return (Con (x:xs) typ)
 ]  
   
con' = (do
   char '\"'
   x <- many $ noneOf "\""
   char '\"'
   return (Con x (Atom "f"))
   )
  <|>
  do
   x <- oneOf "QWERTYUIOPASDFGHJKLZXCVBNM'" 
   xs <- many $ oneOf "QWERTYUIOPASDFGHJKLZXCVBNMqwertyuiopasdfghjklzxcvbnm'"
   return (Con (x:xs) Void)
   
   
option trm = do 
  { reserved "option"
  ; string "(" ; spaces
  ; x <- trm   ; spaces
  ; string "," ; spaces
  ; f <- trm   ; spaces
  ; comma      ; spaces
  ; d <- trm   ; spaces
  ; string ")" 
  ; return (CaseO x f d)
  }
  
agent = do 
  { reserved "AG"
  ; return $  Con "AG" ( (Atom "e" :-> (Atom "e" :-> Atom "t")) ) 
  }
  
patient  = do 
  { reserved "PAT"
  ; return  $ Con "PAT" ( (Atom "e" :-> (Atom "e" :-> Atom "t")) ) 
  }

goal  = do 
  { reserved "GOAL"
  ; return  $ Con "GOAL" ( (Atom "e" :-> (Atom "e" :-> Atom "t")) ) 
  }


termtable   =
  [
    [ postfix "^" (NotNil)]
 
  , [ binary "+" (.+) AssocRight ,   binary "/\\" (/\) AssocLeft]  
  , [ binary "\\/" (\/) AssocRight] 
  , [ binary "@" (composition) AssocLeft]   
  , [ binary "" (App) AssocLeft]   
  ]
  
  
nextFreshVar term = head $ (map (:[]) ['a'..]) \\ free term  
  
composition a b = let fv = head $ (map (:[]) ['a'..]) \\ free (App a b) in
    Lam fv $ a `App` (b `App` (Var fv))
  
  
f .+ g = (Con "+" (Atom "f" :-> Atom "f" :-> Atom "f")) `App` f `App` g
f /\ g = (Con "And" (Atom "t" :-> Atom "t" :-> Atom "t")) `App` f `App` g
f \/ g = (Con "Or" (Atom "t" :-> Atom "t" :-> Atom "t")) `App` f `App` g
neg f = (Con "Not" (Atom "t" :-> Atom "t")) `App` f

for_all var term = Con "forall" ( (Atom "e" :-> Atom "t") :-> Atom "t") `App`  (Lam var term)
exists  var term = Con "exists" ( (Atom "e" :-> Atom "t") :-> Atom "t") `App`  (Lam var term)

  
  
stringConcat a b = a .+ b
  

-- free : takes a term and returns a list with all free (unbound) variables in the term
free :: Term -> [Variable]
free term = case term of
  Con c t  -> []
  Nil     -> []
  NotNil v -> free v
  Var v       -> [v]
  Fst v       -> free v
  Snd v       -> free v
  L t         -> free t
  R t         -> free t
  App  u s   -> free u `union` free s
  Pair u s   -> free u `union` free s
  Lam x u    -> free u \\ [x]
  (Case m l r) -> foldr union [] $ map free [m,l,r]
  (CaseO m l r) -> foldr union [] $ map free [m,l,r]  
  

instance Tex Term where
 tex term = case term of
  Nil  -> text "\\ast"
  NotNil a -> hcat [text "\\overline{ " , tex a , text "}" ]
  Var c -> tex $  c
  Con s t -> text $ "{ \\sf " ++ s ++ "}"

  App (App (Con "Not" (Atom "f" :-> Atom "f" :-> Atom "f")) m) n ->  hcat [tex m ,text "\\bullet " ,tex n]
  App (App (Con "+" (Atom "f" :-> Atom "f" :-> Atom "f")) m) n ->  hcat [tex m ,text "\\bullet " ,tex n]
  App (App (Con "And" (Atom "t" :-> Atom "t" :-> Atom "t")) m) n ->   hcat [tex m ,text "\\wedge " ,tex n]
  App (App (Con "Or" (Atom "t" :-> Atom "t" :-> Atom "t")) m) n ->   hcat [tex m ,text "\\vee " ,tex n]
  

  App m n -> hcat [tex m,text "(", tex n, text ")"]
  Pair m n ->  hcat [text"\\langle", tex m ,text ",", tex n ,text"\\rangle"]
  L m  ->   hcat [text"inl(", tex m,text")" ]
  R m  ->   hcat [text"inr(", tex m,text")" ]
  Lam v n ->  hcat[text"( \\lambda ", tex v,text" . ", tex n ,text" )"]
  Fst n ->  hcat [text"fst" , parens $  tex n ]
  Snd n ->  hcat [text"snd" , parens $ tex n ]
  Case m l r ->  hcat [text"case(",tex m ,text", ",tex l,text",",tex r,text")"]
  CaseO m l r ->  hcat [text"caseO(",tex m ,text", ",tex l,text",",tex r,text")"]



instance Show (Term) where
 show term = case term of
  Nil ->  "*"
  NotNil a -> concat [ show a ,"^"]
  Var c ->  c

  Con "Eps" (Atom "f") -> "_"

  Con s (Atom "f") ->  show s
  Con s _ ->  s    --  Con s t -> s  concat ["(", s  , " :: " ,  show t,")"]

  App (App (Con "+" (Atom "f" :-> Atom "f" :-> Atom "f")) m) n ->  concat [show m , " + " , show n]
  App (App (Con "And" (Atom "t" :-> Atom "t" :-> Atom "t")) m) n ->  concat [show m , " /\\ " , show n]
  App (App (Con "Or" (Atom "t" :-> Atom "t" :-> Atom "t")) m) n ->  concat [show m , " \\/ " , show n]
  App (Con "Not" (Atom "t" :-> Atom "t") ) m  ->  concat ["!",show m]  
  
  App (App (Con "AG" (Atom "e" :-> Atom "e" :-> Atom "t")) m) n ->  concat ["AG(",show m , "," , show n,")"]
  App (App (Con "PAT" (Atom "e" :-> Atom "e" :-> Atom "t")) m) n ->  concat ["PAT(",show m , "," , show n,")"]
  App (App (Con "GOAL" (Atom "e" :-> Atom "e" :-> Atom "t")) m) n ->  concat ["(GOAL ",show m , " " , show n,")"]  


  App (Con "forall" ((Atom "e" :-> Atom "t") :-> Atom "t")) (Lam var term) -> concat ["forall ",var,".",show term]
  App (Con "exists" ((Atom "e" :-> Atom "t") :-> Atom "t")) (Lam var term) -> concat ["exists ",var,".",show term]
  
  
 -- App (App f a) b ->  concat [show f , "(" , show a, "," , show b , ")" ]
  
  App m n ->  concat [show m ,"(", show n ,")"]
  Pair m n ->  concat ["<", show m ,",", show n ,">"]
  L m  ->  concat ["L ", show m,"" ]
  R m  ->  concat ["R ", show m,"" ]
  Lam v n -> concat ["\\",v,".", show n ,""]
  Fst n -> concat ["fst " ,  show n ]
  Snd n -> concat ["snd " ,  show n]
  Case m l r -> concat ["case(",show m ,", ",show l,",",show r,")"]
  CaseO m l r -> concat ["\\option(",show m ,", ",show l,",",show r,")"]



texTerm "STRING" term = let tex' = texTerm "STRING" in case term of
  Nil   -> text "\\ast"
  NotNil a -> hcat [text "\\overline{ " , tex' a , text "}" ]
  Var c -> text $ addPrimeIfUpperCase c
  Con "" (Atom "f") -> text "\\epsilon"
  Con x (Atom "f") -> hcat [text "\\str{" , tex  x , text "}" ]
  Con x t -> hcat [tex x ,text "_{" ,  texStyle "STRING" t ,text"}" ]  
  App (App (Con "+" (Atom "f" :-> Atom "f" :-> Atom "f")) a) b -> hsep [tex' a,text "\\bullet",tex' b]
  App m n -> hsep $  [tex' m,parens $ tex' n]
  Pair m n ->  hcat [text"\\langle", tex' m ,text ",", tex' n ,text"\\rangle"]
  L m  ->   hcat [text"inl(", tex' m,text")" ]
  R m  ->   hcat [text"inr(", tex' m,text")" ]
  Lam v n ->  hcat[text" \\lambda ", tex $ addPrimeIfUpperCase v,text" . ", tex' n ,text" "]
  Fst n ->  hcat [text"fst" , parens $  tex' n ]
  Snd n ->  hcat [text"snd" , parens $ tex' n ]
  Case m l r ->  hcat [text"case(",tex' m ,text", ",tex' l,text",",tex' r,text")"]
  CaseO m l r ->  hcat [text"\\option(",tex' m ,text", ",tex' l,text",",tex' r,text")"]





texTerm style@"SEM" term = let tex' = texTerm "SEM" in case term of
  Nil   -> text "\\ast"
  NotNil a -> hcat [text "\\overline{ " , tex' a , text "}" ]
  Var "e" -> text $ "\\e"
  Var c -> text $ addPrimeIfUpperCase c

  Con "TRUE" (Atom "t") -> text "\\top"
  
  Con x t -> hcat [text "\\sem{",text $ map toLower x,text "_{" ,  texStyle style t ,text"}}" ]  
  
  App (App (Con "And" (Atom "t" :-> Atom "t" :-> Atom "t")) m) n ->   hcat [tex' m ,text "\\wedge " ,tex' n]
  App (App (Con "Or" (Atom "t" :-> Atom "t" :-> Atom "t")) m) n ->   hcat [tex' m ,text "\\vee " ,tex' n]
  App (Con "Not" (Atom "t" :-> Atom "t" )) m -> hcat [text "\\neg " , tex' m]
  App (Con "forall" ((Atom "e" :-> Atom "t") :-> Atom "t")) (Lam var term) -> hcat [text "\\forall ",texV var,text ".",tex' term]
  App (Con "exists" ((Atom "e" :-> Atom "t") :-> Atom "t")) (Lam var term) -> hcat [text "\\exists ",texV var,text ".",tex' term]
  
  App (Con "exists" ((Atom "e" :-> Atom "t") :-> Atom "t")) (Con c (Atom "e" :-> Atom "t")) -> hcat [text "\\exists(",tex' term]



  App (App (Con "AG" (Atom "e" :-> Atom "e" :-> Atom "t")) m) n ->  hcat [text "\\AG(",tex' m , text "," , tex' n,text ")"]
  App (App (Con "PAT" (Atom "e" :-> Atom "e" :-> Atom "t")) m) n ->  hcat [text "\\PAT(",tex' m , text "," , tex' n,text ")"]
  App (App (Con "GOAL" (Atom "e" :-> Atom "e" :-> Atom "t")) m) n ->  hcat [text "\\GOAL(",tex' m , text "," , tex' n,text ")"]  
  
  

  App m n -> hcat $  [tex' m,parens $ tex' n]
  Pair m n ->  hcat [text"\\langle", tex' m ,text ",", tex' n ,text"\\rangle"]
  L m  ->   hcat [text"inl(", tex' m,text")" ]
  R m  ->   hcat [text"inr(", tex' m,text")" ]
  Lam v n ->  hcat[text" \\lambda ", texV $ addPrimeIfUpperCase v,text" . ", tex' n ,text" "]
  Fst n ->  hcat [text"fst" , parens $  tex' n ]
  Snd n ->  hcat [text"snd" , parens $ tex' n ]
  Case m l r ->  hcat [text"case(",tex' m ,text", ",tex' l,text",",tex' r,text")"]
  CaseO m l r ->  hcat [text"\\option(",tex' m ,text", ",tex' l,text",",tex' r,text")"]

  
texTerm n x = error $ "missing case in texTerm for "++ n ++" for " ++ show x
texV x = text $ if x == "e" then "\\e" else x  


addPrimeIfUpperCase [c] 
  | isUpper c   = [toLower c , '\'' ]
  | otherwise   = [c]
addPrimeIfUpperCase x = x  



--hextend :: Term -> (Term -> a) -> a
hextendM f term =  let cmap' = hextendM f in
 case term  of
  constant@(Con c t) -> f constant
  Var c         -> return $ Var c
  App m n       -> liftM2 App (cmap' m) (cmap' n)
  Lam v m       -> cmap' m >>= (\x -> return $ Lam v x)
  Pair m n      -> liftM2 Pair (cmap' m) (cmap' n)
  Fst m         -> liftM Fst (cmap' m) 
  Snd n         -> liftM Snd (cmap' n) 
  L m           -> liftM L (cmap' m) 
  R n           -> liftM R (cmap' n) 
  Case o l r    -> liftM3 Case (cmap' o) (cmap' l) (cmap' r)
  Nil           -> return Nil
  NotNil j      -> liftM NotNil (cmap' j)
  CaseO o j d   -> liftM3 CaseO (cmap' o) (cmap' j) (cmap' d)
  

