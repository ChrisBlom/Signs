module Signature (Type(..) , Term(..)) where

{- In the Signature module the definition of types, terms and signatures are given, 
   along with Show, Tex and Eq instances, and various utility functions
-}

import Term
import Type
import Sign
import Tex
import Data.List
import Prelude hiding ((^))
import Data.Char
-- type of variables


sparens a = "(" ++ a ++ ")"



  
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



