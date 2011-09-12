module Inference
( Signature
, TI
, Subst
, typeOf
, mgu
, disp
, validSubst
) where

{- 
AlgorithW type inference algorithm, adapted for ACG terms
and extended for option types

Based on descriptions and code found in:

@article{grabmüller2006algorithm,
  title={Algorithm W Step by Step},
  author={Grabm{\\"u}ller, M.},
  year={2006},
  publisher={Citeseer}
}

-}

import Tex
import Signature
import Prelude hiding ((^))

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Monoid
import System.IO.Unsafe
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State


data Test = Test




validSubst result = unsafePerformIO $ do
  (x,state) <- runTI result
  return ( case x of Right _ -> True ; Left err -> False ) 

    

term0 :: Term     
term0 = Con "testB" (Atom "X")
 
term1 :: Term   
term1 = Con "TestA" (Atom "Y")  
 
term2 = Pair (Con "TestA" (Atom "X") ) (Con "TestB" (Atom "Y"))     

term3 = Lam "x" (App term1 (Var "x"))

term4 :: Term
term4 =  Lam "f" $ Lam "g" $ Lam "x" $ App (Var "f") $ App (Var "g") (Var "x")


data Scheme =  Scheme [Variable] (Type)

-- Substitutions : mapping from variables to signatures
type Subst sig = Map.Map Variable (Type)

newtype TypeEnv sig = TypeEnv (Map.Map String (Scheme))

class Types a  where
    ftv    ::  a -> Set.Set String
    doSub  ::  Subst sig -> a  -> a 

instance  Types Type where
    ftv (TVar n)      =  Set.singleton n
    ftv (Atom _)      =  Set.empty
    ftv ((:->) t1 t2) =  ftv t1 `Set.union` ftv t2
    ftv (t1 :*: t2)   =  ftv t1 `Set.union` ftv t2  
    ftv (t1 :+: t2)   =  ftv t1 `Set.union` ftv t2      
    ftv (Option t1)   =  ftv t1

    doSub s (TVar n)  =  case Map.lookup n s of
                               Nothing  -> TVar n
                               Just t   -> t
    doSub s (t1 :-> t2)  = (doSub s t1) :-> (doSub s t2)
    doSub s (t1 :*: t2)  = (doSub s t1) :*: (doSub s t2)    
    doSub s (Option t1)  = Option (doSub s t1) 
    doSub s (Atom a)     = Atom a      
    doSub s x            = error $ "missing case in doSub for " ++ show x

instance Types Scheme  where
    ftv (Scheme vars t)      =  (ftv t) `Set.difference` (Set.fromList vars)

    doSub s (Scheme vars t)  =  Scheme vars (doSub (foldr Map.delete s vars) t)

-- empty 
nullSubst  ::  Subst sig
nullSubst  =   Map.empty

-- composition of substitutions
composeSubst         :: Subst sig -> Subst sig -> Subst sig
composeSubst s1 s2   = (Map.map (doSub s1) s2) `Map.union` s1


remove                    ::  TypeEnv sig -> Variable -> TypeEnv sig
remove (TypeEnv env) var  =  TypeEnv (Map.delete var env)

instance Types (TypeEnv s ) where
    ftv (TypeEnv env)      =   foldr Set.union Set.empty (map ftv (Map.elems env) )
    doSub s (TypeEnv env)  =  TypeEnv (Map.map (doSub s) env)

generalize        :: TypeEnv sig -> (Type) -> Scheme
generalize env t  =   Scheme vars t
  where vars = Set.toList ((ftv t) `Set.difference` (ftv env))

data TIEnv = TIEnv  {}

data TIState sig  = TIState 
  { tiSupply :: Int
  , tiSubst  :: Subst sig
  }

type TI a sig = ErrorT String (ReaderT TIEnv (StateT (TIState sig) IO)) a

runTI :: TI a sig -> IO (Either String a, (TIState sig))
runTI t = 
    do (res, st) <- runStateT (runReaderT (runErrorT t) initTIEnv) initTIState
       return (res, st)
  where initTIEnv = TIEnv{}
        initTIState = TIState{tiSupply = 0,
                              tiSubst = Map.empty}

newTyVar :: Variable -> TI (Type) sig
newTyVar prefix =
    do  s <- get
        put s{tiSupply = tiSupply s + 1}
        return (TVar  (prefix ++"_" ++ show (tiSupply s)))
   

instantiate :: Scheme -> TI ((Type) ) sig
instantiate (Scheme vars t) = do
  nvars <- mapM (\ _ -> newTyVar "a") vars
  let s = Map.fromList (zip vars nvars)
  return $ doSub s t


-- returns the most general unifier of two types
mgu :: (Type) -> (Type) -> TI (Subst sig) sig

-- functions
mgu (l :-> r) (l' :-> r')  =  do  
  s1 <- mgu l l'
  s2 <- mgu (doSub s1 r) (doSub s1 r')
  return (s1 `composeSubst` s2)
-- tuples  
mgu (l :*: r) (l' :*: r')  =  do  
  s1 <- mgu l l'
  s2 <- mgu (doSub s1 r) (doSub s1 r')
  return (s1 `composeSubst` s2)
  
-- tuples  
mgu (Option l) (Option l')  =  do  
  s1 <- mgu l l'
  return (s1 )  
  
mgu (TVar u) t               =  varBind u t
mgu t (TVar u)               =  varBind u t
mgu (Atom _) (Atom _)        =  return nullSubst
mgu t1 t2                    =  throwError $ "types do not unify: \n expected \t: "  ++ show t1  ++
                                " \n but got \t: "  ++  show t2 ++ "\n"

varBind :: Variable -> (Type) -> TI (Subst sig) sig
varBind u t  | t == TVar u           =  return nullSubst
             | u `Set.member` ftv t  =  throwError $ "occur check fails: " ++ u ++
                                         " vs. "  ++ show t
             | otherwise             =  return (Map.singleton u t)

tiLit :: TypeEnv sig -> Term -> TI (Subst sig, (Type)) sig
tiLit _ (Con a t)   =  return (nullSubst, t)




ti :: TypeEnv sig -> (Term) -> TI (Subst sig, (Type)) sig
ti (TypeEnv env) (Var n) = 
    case Map.lookup n env of
       Nothing     ->  throwError $ "unbound variable: " ++ n
       Just sigma  ->  do  t <- instantiate sigma
                           return (nullSubst, t) 
ti env (Con l t) = tiLit env (Con l t)  
ti env (Lam n e) =
    do  tv <- newTyVar "a"
        let TypeEnv env' = remove env n
            env'' = TypeEnv (env' `Map.union` (Map.singleton n (Scheme [] tv)))
        (s1, t1) <- ti env'' e
        return (s1, (:->) (doSub s1 tv) t1)

ti env (App fun arg) = do
  tv <- newTyVar "a"
  (s1, t1) <- ti env fun
  (s2, t2) <- ti (doSub s1 env) arg
  s3 <- mgu (doSub s2 t1) (t2 :-> tv)
  return (s3 `composeSubst` s2 `composeSubst` s1, doSub s3 tv)
  
ti env (Pair e1 e2) = do
  (s1, t1) <- ti env e1
  (s2, t2) <- ti env e2
  return ( s2 `composeSubst` s1, t1 :*: t2)


ti env (Fst e1) = do
  a <- newTyVar "a"
  b <- newTyVar "b"
  (s1,t) <- ti env e1
  s2 <- mgu t (a :*: b)
  return (s2 `composeSubst` s1 , case doSub s2 t of (x :*: y) -> x )


ti env (Snd e1) = do
  a <- newTyVar "a"
  b <- newTyVar "b"
  (s1,t) <- ti env e1
  s2 <- mgu t (a :*: b)
  return (s2 `composeSubst` s1 , case doSub s2 t of (x :*: y) -> y )



ti env (Nil) = do
  tv <- newTyVar "a"
  s3 <- mgu ( tv) ( tv)
  return ( s3 , Option tv)


ti env (NotNil inner) = do
  tv <- newTyVar "a"
  (s1, t1) <- ti env inner
  s3 <- mgu  (tv) (Option t1)
  return (s3 `composeSubst` s1, doSub s3 tv)
          
ti env (CaseO o f d) = do
  tA <- newTyVar "a"
  tB <- newTyVar "b"

  (sD, typeD) <- ti env d  
  (sF, typeF) <- ti (doSub sD env) f 
  (sO, typeO) <- ti (doSub sF env) o

  s3 <- mgu (doSub sF typeD) (tB)     
  s1 <- mgu (doSub sD typeF) (tA :-> (doSub s3 tB) ) 
  s2 <- mgu (doSub s1 typeO) (doSub s1    (Option tA))


  return (foldr1 composeSubst [s3,s1,s2] , doSub s2 typeD )          
          
        
ti _ x = error$ "missing case in ti for " ++ show x

typeInference ::  Map.Map Variable (Scheme) -> Term -> TI (Type) sig
typeInference env e =
    do  (s, t) <- ti (TypeEnv env) e
        return (doSub s t)        
        
        

data Constraint sig 
  = CEquivalent (Type) (Type)
  | CExplicitInstance (Type) (Scheme)
  | CImplicitInstance (Type) (Set.Set Variable) (Type)



type Assum sig = [(String,Type)]
type CSet sig =  [Constraint sig]

bu :: Set.Set String -> (Term) -> TI (Assum sig, CSet sig, (Type)) sig
bu m (Var n) = do b <- newTyVar "b"
                  return ([(n, b)], [], b)
bu m (Con ( a) t) = do 
                  b <- newTyVar "b"
                  return ([], [CEquivalent b t], b)
bu m (App e1 e2) = do 
  (a1, c1, t1) <- bu m e1
  (a2, c2, t2) <- bu m e2
  b <- newTyVar "b"
  return ( a1 ++ a2 , c1 ++ c2 ++ [CEquivalent t1 ((:->) t2 b) ],   b)
  
bu m (Lam x body) =
    do b@(TVar vn) <- newTyVar "b"
       (a, c, t) <- bu (vn `Set.insert` m) body
       return (a `removeAssum` x, c ++ [CEquivalent t' b | (x', t') <- a,
                                        x == x'], (:->) b t)
                                        {-
bu m (ELet x e1 e2) =
    do (a1, c1, t1) <- bu m e1
       (a2, c2, t2) <- bu (x `Set.delete` m) e2
       return (a1 ++ removeAssum a2 x,
               c1 ++ c2 ++ [CImplicitInstance t' m t1 |
                            (x', t') <- a2, x' == x], t2)
-}
removeAssum [] _ = []
removeAssum ((n', _) : as) n | n == n' = removeAssum as n
removeAssum (a:as) n = a : removeAssum as n
        
test :: (Term ) -> IO ()
test e =
    do  (res, _) <- runTI (typeInference Map.empty e)
        case res of
          Left err  ->  putStrLn $ "error: " ++ err
          Right t   ->  putStrLn $ show e ++ " :: " ++ show t
          

typeOf e = unsafePerformIO $ do 
 (x,state) <- runTI (typeInference Map.empty e) 
 return ( case x of Right typ -> typ ; Left err -> error $ err ++ " in " ++ show e ) 
 
disp e = do 
 (x,state) <- runTI e
 return ( case x of Right typ -> typ ; Left err -> error err ) 
          
                    
