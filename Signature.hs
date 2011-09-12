module Signature where

{- In the Signature module the definition of types, terms and signatures are given, 
   along with Show, Tex and Eq instances, and various utility functions
-}

import Tex
import Data.List 
import Prelude hiding ((^))
import Data.Char
-- type of variables
type Variable = String

sparens a = "(" ++ a ++ ")"


  
data Sign = Sign { abstract :: Term , concretes :: [Term] } deriving Eq


showTuple a b = concat [show a, " = " ,"<" ,concatMap show b,">"]

instance Show Sign where
  show s = showTuple (abstract s) (concretes s)
  
  
data Fragment = Fragment 
  { mappings    :: [ (Type,Type) ]
  , definitions :: [Sign]
  }
  

-- Definition of signatures
class (Show (ConstantOf a)  ,Eq (ConstantOf a)  ,Tex (ConstantOf a) 
      ,Show (AtomOf a)      ,Eq (AtomOf a)      ,Tex (AtomOf a)
      ) => Signature a where
  data ConstantOf a 
  data AtomOf a 
  allConstants :: a -> [ConstantOf a]


-- the datatype of types, parameterized by a signature
infixr 6 :-> 
data Type 
  = Atom String
  | TVar Variable
  | (Type) :-> (Type)
  | (Type) :+: (Type)
  | (Type) :*: (Type)
  | Option (Type)
  | Unit
  | Void
  

atomicType typ = case typ of
  Atom _  -> True
  TVar _  -> True
  Unit    -> True
  Void    -> True
  Option a -> atomicType a
  _       -> False
   

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
  -- sums
  | L (Term)
  | R (Term)
  | Case (Term) (Term) (Term)
  -- option
  | Nil
  | NotNil (Term)
  | CaseO (Term) (Term) (Term)


  
-- unique homomorphic extender over terms for functions that operate on constants
cmap f t = let cmap' = cmap f in case t of
  Con c t         -> f c
  Var c         -> Var c
  App m n       -> App (cmap' m) (cmap' n)
  Lam v m       -> Lam v (cmap' m)
  Pair m n      -> Pair (cmap' m) (cmap' n)
  Fst m         -> Fst (cmap' m) 
  Snd n         -> Snd (cmap' n) 
  L m           -> L (cmap' m) 
  R n           -> R (cmap' n) 
  Case o l r    -> Case (cmap' o) (cmap' l) (cmap' r)
  Nil           -> Nil
  NotNil j      -> NotNil (cmap' j)
  CaseO o j d   -> CaseO (cmap' o) (cmap' j) (cmap' d)
  
-- unique homomorphic extender over terms for functions that operate on variables
vamp f t = let vamp' = vamp f in case t of
  Con c t         -> Con c t
  Var c         -> Var (f c)
  App m n       -> App (vamp' m) (vamp' n)
  Lam v m       -> Lam (f v) (vamp' m)
  Pair m n      -> Pair (vamp' m) (vamp' n)
  Fst m         -> Fst (vamp' m) 
  Snd n         -> Snd (vamp' n) 
  L m           -> L (vamp' m) 
  R n           -> R (vamp' n) 
  Case o l r    -> Case (vamp' o) (vamp' l) (vamp' r)
  Nil           -> Nil
  NotNil j      -> NotNil (vamp' j)
  CaseO o j d   -> CaseO (vamp' o) (vamp' j) (vamp' d)
  

-- Type Classes for terms
instance  Eq (Term ) where

  Con a t == Con b t' = a == b
  Var a == Var b = a == b
  (Lam a x) == (Lam b  y) = a==b && x ==y
  (App a x) == (App b  y) = a==b && x ==y

  (Pair a x)== (Pair b  y) = a==b && x ==y
  (L a)  == (L b) = a == b
  (R a) == (R b) = a == b

  (Snd a )  == (Snd b) = a==b 
  (Fst a )  == (Fst b) = a==b 
  (Case a b c )  == (Case a' b' c' ) = and $ zipWith (==) [a,b,c] [a',b',c']
  (CaseO a b c )  == (CaseO a' b' c' ) = and $ zipWith (==) [a,b,c] [a',b',c']

  Nil == Nil = True
  NotNil a == NotNil b = a == b
  (==) _ _ = False

instance Show (Term) where
 show term = case term of
  Nil ->  "*"
  NotNil a -> concat ["{", show a ,"}"]
  Var c ->  show c
  Con s t ->  show s ++ ":" ++ show t
  App m n ->  concat ["(", show m ," ", show n ,")"]
  Pair m n ->  concat ["<", show m ,",", show n ,">"]
  L m  ->  concat ["L ", show m,"" ]
  R m  ->  concat ["R ", show m,"" ]
  Lam v n -> concat ["(\\",show v,".", show n ,")"]
  Fst n -> concat ["fst " ,  show n ]
  Snd n -> concat ["snd " ,  show n]
  Case m l r -> concat ["case(",show m ,", ",show l,",",show r,")"]
  CaseO m l r -> concat ["caseO(",show m ,", ",show l,",",show r,")"]


{-
instance (Signature s) => Tex (Term s) where
 tex term = case term of
  Nil   -> text "\\sim"
  NotNil a -> hcat [text "\\overline{ " , tex a , text "}" ]
  Var c -> tex $  c
  Con s -> text $ show s
  App m n -> parens $ hsep  $ map tex [m,n]
  Pair m n ->  hcat [text"\\langle", tex m ,text ",", tex n ,text"\\rangle"]
  L m  ->   hcat [text"inl(", tex m,text")" ]
  R m  ->   hcat [text"inr(", tex m,text")" ]
  Lam v n ->  hcat[text"( \\lambda ", tex v,text" . ", tex n ,text" )"]
  Fst n ->  hcat [text"fst" , parens $  tex n ]
  Snd n ->  hcat [text"snd" , parens $ tex n ]
  Case m l r ->  hcat [text"case(",tex m ,text", ",tex l,text",",tex r,text")"]
  CaseO m l r ->  hcat [text"caseO(",tex m ,text", ",tex l,text",",tex r,text")"]
-}


-- unique homomorphic extension of functions that operate on atomic types
amap f t = let amap' = amap f in case t of
  Atom a      -> f a
  TVar v      -> TVar v
  f :-> g     -> (amap' f) :-> (amap' g)
  f :*: g     -> (amap' f) :*: (amap' g)
  f :+: g     -> (amap' f) :+: (amap' g)
  Option a    -> Option (amap' a)
  Unit        -> Unit
  Void        -> Void
  

vmap f t = let vmap' = vmap f in case t of
  Atom a      -> []
  TVar v      -> f v
  f :-> g     -> (vmap' f) `union` (vmap' g)
  f :*: g     -> (vmap' f) `union` (vmap' g)
  f :+: g     -> (vmap' f) `union` (vmap' g)
  Option a    -> (vmap' a)
  Unit        -> []
  Void        -> []

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

  
-- Type Classes for types and terms
instance Eq (Type ) where
  Atom a == Atom b = a == b
  TVar a == TVar b = a == b
  (a :-> x) == (b :-> y) = a==b && x ==y
  (a :*: x) == (b :*: y) = a==b && x ==y
  (a :+: x) == (b :+: y) = a==b && x ==y  
  Void == Void = True
  Unit == Unit = True
  (Option a) == (Option b) = a == b
  (==) _ _ = False
instance Show Type where
  show t = case t of
    Atom a -> map toLower a
    TVar v -> map toUpper v
    (a :-> b) -> if( atomic a) then  concat [show a , "->" , show b] else sparens$ concat [show a , "->" , show b]
    (a :*: b) -> sparens$ concat [show a , "x" , show b]
    (a :+: b) -> sparens$ concat [show a , "+" , show b]    
    (Option a) -> concat [show a , "?"]        
    Unit -> "1" 
    Void -> "0"
    
    
atomic (a :-> b) = False
atomic (a :*: b) = False
atomic (a :+: b) = False
atomic _ = True
    
    
{-instance (Signature s,Tex (AtomOf s) ) => Tex (Type s) where
  tex t = case t of
    Atom a -> tex  a
    TVar v -> text $ show v
    (a :-> b) -> parens $ hsep [tex a , text "\\rightarrow" , tex b] 
    (a :*: b) -> hsep [tex a , text "\\otimes" , tex b]
    (a :+: b) -> hsep [tex a , text "\\oplus" , tex b]
    (Option a) -> hcat [tex a ,text "^?"]            
    Unit -> text $ "1" 
    Void -> text $ "0" -}
    
