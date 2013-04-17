module Reductions (reduce) where

{- In this module the various reduction operations for terms are defined
   
   The only exported funciton is reduce, which reduces a term to its normal form.
   
   The implemented reductions are:
   
   - Beta reduction     
   - Option reduction   
   - Sum reduction
   - Product reduction
   
   Variable renaming and capture avoiding substitution (required for beta-reduction)
   are are used in beta reduction
 -}
 
import Term

import Data.List 
import Prelude hiding ((^))
import qualified Data.Foldable as Fold


insertDef :: (String,Term) -> Term -> Term
insertDef (varName,def) inTerm = subst varName def inTerm


-- reductions : applies all the reductions until convergence
reduce :: Term -> Term
reduce = fixpoint reductions


fixpoint :: (Eq a) => (a -> a) -> a -> a
fixpoint f x
  | (f x) == x  = x
  | otherwise   = fixpoint f (f x)

-- reductions : applies one pass of the different reductions to a term.
reductions :: Term -> Term
reductions = foldr (.) id 
  [ beta_reduce
  , projection_reduce
  , sum_reduce
  , option_reduce
  ]
 
-- disjointVars : ensure the variables in different scopes are disjoint
disjointVars :: Term -> Term
disjointVars term = case term of
  (Case t l r) -> let overlap = intersect (vars l) (vars r) in 
    Case t l (renameList overlap (fresh $ vars $ term) r)
  Pair m n -> let overlap = intersect (vars m) (vars n) in 
    Pair m (renameList overlap (fresh $ vars $ term) n)    
  _ -> term

-- fresh : generates a list of fresh variables from a list of used variables
fresh :: [Variable] -> [Variable]
fresh t =  map (:[]) [ 'a'..] \\ t

--vars : takes a term and returns a list with variables in the term
vars :: Term -> [Variable]
vars term = case term of
  Con c t   -> []
  Var v       -> [v]
  Fst v       -> vars v
  Snd v       -> vars v  
  App  u s   -> vars u `union` vars s
  Pair u s   -> vars u `union` vars s
  Lam x u    -> vars u 
  L x         -> vars x
  R y         -> vars y
  NotNil a    -> vars a
  Nil        -> []
  CaseO m l r  -> foldr union [] $ map vars [m,l,r]  
  Case m l r  -> foldr union [] $ map vars [m,l,r]
  


-- variable renaming
rename :: Variable ->  Variable -> Term -> Term
rename old new term = let rename' = rename old new  in case term of
  Var v      | v == old -> Var new
  Var v                 -> Var v
  Con c t                -> Con c t
  Fst  m                -> Fst  (rename' m) 
  Snd  m                -> Snd  (rename' m)   
  Pair  m n             -> Pair (rename' m) (rename' n)  
  App  m n              -> App  (rename' m) (rename' n)
  Lam x m | x == old    -> Lam new (rename' m)
  Lam y m               -> Lam y (rename' m)
  L x                   -> L $ rename' x
  R x                   -> R $ rename' x
  Case a l r            -> Case (rename' a) (rename' l) (rename' r)
  Nil                   -> Nil
  NotNil a              -> NotNil (rename' a)
  CaseO a l r           -> CaseO (rename' a) (rename' l) (rename' r)

-- rename' : Renames multiple variables within a term
renameList ::  [Variable] -> [Variable] -> Term -> Term
renameList [] _ t = t
renameList (old:olds) (new:news) t = renameList olds news (rename old new t)

-- capture avoiding substitution
subst :: Variable -> Term -> Term -> Term
subst old new term = let subst' = subst old new in case term of
  Var v      | (v == old) -> new
  Var v      | (v /= old) -> Var v
  Lam x m | x == old -> Lam x m
  Lam y m | y /= old && y `notElem` free new -> Lam y (subst old new m)
  Lam y m | old /= y && y `elem` free new ->
      Lam y' (subst y (Var y') $ (rename y y' m)) where
        y' = head $ fresh $ free term 
  App   m n  -> App  (subst' m) (subst' n)
  Pair  m n  -> Pair (subst' m) (subst' n)
  Fst   n    -> Fst  (subst' n) 
  Snd   n    -> Snd  (subst' n) 
  Con s t -> Con s t 
  L m  -> L $ subst' m
  R n  -> R $ subst' n
  Nil  -> Nil
  NotNil a -> NotNil (subst' a)
  Case m l r  -> Case (subst' m) (subst' l) (subst' r)    
  CaseO m l r  -> CaseO (subst' m) (subst' l) (subst' r)    
  _ -> error $ "missing case in 'subst' for " ++ show term


-- Reduction of pairs
projection_reduce :: Term -> Term
projection_reduce t = case t of
  (Fst (Pair l r))      -> l
  (Snd (Pair l r))      -> r

  (Fst x)       	      -> Fst   (projection_reduce x)
  (Snd x)       	      -> Snd   (projection_reduce x)
  (Pair m n)            -> Pair  (projection_reduce m) (projection_reduce n)
  (App  m n)            -> App   (projection_reduce m) (projection_reduce n)
  (Lam v t)             -> Lam v (projection_reduce t)
  (L x)       	        -> L     (projection_reduce x)
  (R x)       	        -> R     (projection_reduce x)
  Nil                   -> Nil
  NotNil a              -> NotNil (projection_reduce a)
  t@(Var v)             -> t
  t@(Con c x)             -> t
  (Case  o f d)         -> Case  (projection_reduce o) (projection_reduce f) (projection_reduce d)  
  (CaseO o f d)         -> CaseO (projection_reduce o) (projection_reduce f) (projection_reduce d)
  
  
-- Reduction of options  
option_reduce :: Term -> Term 
option_reduce t = case t of
  (CaseO (NotNil x) f d) -> App f x
  (CaseO Nil        f d) -> d

  (CaseO o f d)         -> CaseO (option_reduce o) (option_reduce f) (option_reduce d)
  (Case  o f d)         -> Case  (option_reduce o) (option_reduce f) (option_reduce d)  
  (App  m n)            -> App   (option_reduce m) (option_reduce n)
  (Lam v t)             -> Lam v (option_reduce t)
  (Fst x)       	      -> Fst   (option_reduce x)
  (Snd x)       	      -> Snd   (option_reduce x)
  (Pair m n)            -> Pair  (option_reduce m) (option_reduce n)
  (L x)       	        -> L     (option_reduce x)
  (R x)       	        -> R     (option_reduce x)
  Nil                   -> Nil
  NotNil a              -> NotNil (option_reduce a)
  t@(Var v)             -> t
  t@(Con c x)             -> t
  
sum_reduce :: Term -> Term
sum_reduce t = case t of
  (Case (L x) f g)      -> App f x
  (Case (R x) f g)      -> App g x    

  (Case  o f d)         -> Case  (sum_reduce o) (sum_reduce f) (sum_reduce d)  
  (L x)       	        -> L     (sum_reduce x)
  (R x)       	        -> R     (sum_reduce x)

  (App  m n)            -> App   (sum_reduce m) (sum_reduce n)
  (Lam v t)             -> Lam v (sum_reduce t)
  (Fst x)       	      -> Fst   (sum_reduce x)
  (Snd x)       	      -> Snd   (sum_reduce x)
  (Pair m n)            -> Pair  (sum_reduce m) (sum_reduce n)
  Nil                   -> Nil
  NotNil a              -> NotNil (sum_reduce a)
  t@(Var v)             -> t
  t@(Con c x)             -> t
  (CaseO o f d)         -> CaseO (sum_reduce o) (sum_reduce f) (sum_reduce d)

beta_reduce :: Term -> Term
beta_reduce term = case term of
  (App  l@(Lam x t) u)  -> subst x u t
  (App  m n)            -> App   (beta_reduce m) (beta_reduce n)
  (Lam v t)             -> Lam v (beta_reduce t)
  (Fst x)       	      -> Fst   (beta_reduce x)
  (Snd x)       	      -> Snd   (beta_reduce x)
  (Pair m n)            -> Pair  (beta_reduce m) (beta_reduce n)
  (L x)       	        -> L     (beta_reduce x)
  (R x)       	        -> R     (beta_reduce x)
  Nil                   -> Nil
  NotNil a              -> NotNil (beta_reduce a)
  t@(Var v)               -> t
  t@(Con c x)              -> t
  (Case  o f d)         -> Case  (beta_reduce o) (beta_reduce f) (beta_reduce d)  
  (CaseO o f d)         -> CaseO (beta_reduce o) (beta_reduce f) (beta_reduce d) 

