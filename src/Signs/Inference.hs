module Signs.Inference
( TI
, Subst
, typeOfE
, typeOf
, mgu
, validSubst
) where

{-
AlgorithW type inference algorithm, adapted for ACG and extended for option, product and sum types

Based on descriptions and code found in:

@article{grabmüller2006algorithm,
  title={Algorithm W Step by Step},
  author={Grabm{\\"u}ller, M.},
  year={2006},
  publisher={Citeseer}
}

-}

import Prelude hiding ((^))

import Signs.Tex
import Signs.Term
import Signs.Type

import Data.Functor.Identity

import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Monoid
import System.IO.Unsafe
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

-- | new type to wrap error messages about typing
newtype TypeError = TypeError { getString :: String }

instance Show TypeError where
  show (TypeError t) = "type error: " ++ t
instance Tex TypeError where
  tex = text . show

-- checks if two types are unifiable
unifiable a b = validSubst $ a `mgu` b

validSubst result = let (x,state) = runTI result in
  case x of
    Right _  -> True
    Left err -> False

typeOf :: Term -> Maybe Type
typeOf term = case typeOfE term of
  (Left  e) -> Nothing
  (Right t) -> Just t

-- returns the type of term, or an error message if the term is not well-typed
typeOfE :: Term -> Either TypeError Type
typeOfE term = fst $ runTI $ (typeInference Map.empty term)
-- Substitutions : mapping from variables to signatures

type Subst = Map.Map Variable (Type)

class Typelike a  where
    -- gets the set of free type variables
    ftv    ::  a -> Set.Set String
    -- performs a substitution on a type, replacing variables with types
    doSub  ::  Subst -> a  -> a

-- Typelike are
instance  Typelike Type where
    ftv (TVar n)      =  Set.singleton n
    ftv (Atom _)      =  Set.empty
    ftv (t1 :-> t2) =  ftv t1 `Set.union` ftv t2
    ftv (t1 :*: t2)   =  ftv t1 `Set.union` ftv t2
    ftv (t1 :+: t2)   =  ftv t1 `Set.union` ftv t2
    ftv (Option t1)   =  ftv t1
    ftv (Marker t1 _)   =  ftv t1

    doSub s (TVar n)  =  case Map.lookup n s of
                               Nothing  -> TVar n
                               Just t   -> t
    doSub s (t1 :-> t2)  = (doSub s t1) :-> (doSub s t2)
    doSub s (t1 :*: t2)  = (doSub s t1) :*: (doSub s t2)
    doSub s (t1 :+: t2)  = (doSub s t1) :+: (doSub s t2)
    doSub s (Option t1)  = Option (doSub s t1)
    doSub s (Marker t1 str )  = Marker (doSub s t1) str
    doSub s (Atom a)     = Atom a

    doSub s x            = error $ "missing case in doSub for " ++ show x

-- | Type enviroments
newtype TypeEnv = TypeEnv (Map.Map Variable (Scheme))

instance Typelike (TypeEnv  ) where
    ftv (TypeEnv env)      =   foldr Set.union Set.empty (map ftv (Map.elems env) )
    doSub s (TypeEnv env)  =  TypeEnv (Map.map (doSub s) env)


data Scheme =  Scheme [Variable] (Type)

instance Typelike Scheme  where
    ftv (Scheme vars typ)      =  (ftv typ) `Set.difference` (Set.fromList vars)
    doSub substitution (Scheme vars typ)  =  Scheme vars (doSub (foldr Map.delete substitution vars) typ)

-- empty
nullSubst :: Subst
nullSubst  = Map.empty

-- composition of substitutions
composeSubst :: Subst  -> Subst  -> Subst
composeSubst s1 s2   = (Map.map (doSub s1) s2) `Map.union` s1

remove ::  TypeEnv -> Variable -> TypeEnv
remove (TypeEnv env) var  =  TypeEnv (Map.delete var env)

generalize        :: TypeEnv  -> Type -> Scheme
generalize env t  =   Scheme vars t
  where vars = Set.toList ((ftv t) `Set.difference` (ftv env))

data TIState = TIState
  { tiUsed   :: [Variable]
  , tiSubst  :: Subst
  }

-- initial TIState : no variables used, no substitutions
initTIState :: TIState
initTIState = TIState {tiUsed = [] , tiSubst = Map.empty}

-- Type Inference monad : error (TypeError) or state (fresh vars and subs)
type TI a  = ExceptT TypeError (State TIState) a

runTI :: TI a  -> (Either TypeError a, TIState)
runTI inferencer = runState (runExceptT inferencer) initTIState

-- | get a fresh variable
newTyVar :: String -> TI Type
newTyVar prefix =
    do  s <- get
        let freshVar = head $ (map (:[]) ['a'..]) \\ (tiUsed s)
        put $ s { tiUsed = freshVar : (tiUsed s) }
        return (TVar freshVar)


instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- mapM (\ _ -> newTyVar "z") vars
  let s = Map.fromList (zip vars nvars)
  return $ doSub s t

-- returns the most general unifier of two types
mgu :: Type -> Type -> TI Subst
a .=. b = mgu a b

-- functions
mgu (l :-> r) (l' :-> r')  =  do
  s1 <- l .=. l'
  s2 <- (doSub s1 r) .=. (doSub s1 r')
  return (s1 `composeSubst` s2)
-- tuples
mgu (l :*: r) (l' :*: r')  =  do
  s1 <- l .=. l'
  s2 <- (doSub s1 r) .=. (doSub s1 r')
  return (s1 `composeSubst` s2)

-- tuples
mgu (Option l) (Option l')  =  l .=. l'
-- marked types
mgu (Marker l m) (Marker l' m' )  | m == m' =  l .=. l'
mgu (Marker l m) ( l' )   =  l .=. l'
mgu ( l' ) (Marker l m)   =  l .=. l'
-- vars
mgu (TVar u) t               =  varBind u t
mgu t (TVar u)               =  varBind u t
-- atoms
mgu (Atom x) (Atom y) | x == y  =  return nullSubst

-- fail:
mgu t1 t2 = throwError . TypeError . concat $
  ["types do not unify: \n expected \t: ",show t1," \n but got \t: ",show t2,"\n"]

varBind :: Variable -> (Type) -> TI Subst
varBind u t  | t == TVar u           =  return nullSubst
             | u `Set.member` ftv t  =  throwError . TypeError. concat $ ["occur check fails: ",u," vs. ",show t]
             | otherwise             =  return (Map.singleton u t)


tiLit :: TypeEnv -> Term -> TI (Subst,Type)
tiLit _ (Con a t)   =  return (nullSubst, t)


ti :: TypeEnv -> Term -> TI (Subst, Type)
ti (TypeEnv env) (Var n) =
    case Map.lookup n env of
       Nothing     ->  (throwError . TypeError $ "unbound variable: " ++ n)
       Just sigma  ->  do t <- instantiate sigma
                          return (nullSubst, t)

ti env (Con l t) = tiLit env (Con l t)
ti env (Lam n e) =
    do  tv <- newTyVar "z"
        let TypeEnv env' = remove env n
            env'' = TypeEnv (env' `Map.union` (Map.singleton n (Scheme [] tv)))
        (s1, t1) <- ti env'' e
        return (s1, (:->) (doSub s1 tv) t1)

ti env (App fun arg) = do
  tv <- newTyVar "z"
  (s1, t1) <- ti env fun
  (s2, t2) <- ti (doSub s1 env) arg
  s3 <- mgu (doSub s2 t1) (t2 :-> tv)
  return (s3 `composeSubst` s2 `composeSubst` s1, doSub s3 tv)

ti env (Pair e1 e2) = do
  (s1, t1) <- ti env e1
  (s2, t2) <- ti env e2
  return ( s2 `composeSubst` s1, t1 :*: t2)


ti env (Fst e1) = do
  a <- newTyVar "z"
  b <- newTyVar "y"
  (s1,t) <- ti env e1
  s2 <- mgu t (a :*: b)
  return (s2 `composeSubst` s1 , case doSub s2 t of (x :*: y) -> x )


ti env (Snd e1) = do
  a <- newTyVar "z"
  b <- newTyVar "y"
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
  tA <- newTyVar "z"
  tB <- newTyVar "y"

  (subO, typO) <- ti env o
  subO' <- (doSub subO typO) `mgu`  (Option tA)

  (subF, typF) <- ti env f
  subF' <- (doSub subF typF) `mgu`  (tA :-> tB)

  (subD, typD) <- ti env d
  subD' <- (doSub subD typD) `mgu`  (tB)

  return ( subD' `composeSubst`  subF' `composeSubst`  subO' , tB)



ti _ x = error $ "missing case in ti for " ++ show x

testO = Lam "v" $ Lam "o" $ CaseO ( Var "o" ) (Lam "o'" $ Var "v" `App` Var "o'" ) ( Con "x" (Atom "e" :-> Atom "t") )

exi =  Con "exists" ((Atom "e" :-> Atom "t"):-> Atom "t")

testOo = Lam "o" $ Lam "f" $ Lam "d" $ CaseO ( Var "o" ) (Var "f") ( Var "d"  )
testO2
  = Lam "v"
  $ Lam "o"
  $ Lam "s"
  $ Lam "e"
  $ CaseO ( Var "o")
          ( (Var "v")   )
          ( Lam "e" $ Lam "s'" $ exi `App` ( Lam "o'" $ (Var "v") `App` (Var "o'") `App` (Var "s'") `App` (Var "e") ))  `App` (Var "s") `App` (Var "e")

typeInference ::  Map.Map Variable (Scheme) -> Term -> TI (Type)
typeInference env e =
    do  (s, t) <- ti (TypeEnv env) e
        return (doSub s t)

data Constraint
  = CEquivalent (Type) (Type)
  | CExplicitInstance (Type) (Scheme)
  | CImplicitInstance (Type) (Set.Set Variable) (Type)

type Assum = [(String,Type)]
type CSet =  [Constraint]

bu :: Set.Set String -> (Term) -> TI (Assum, CSet, (Type))
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

removeAssum [] _ = []
removeAssum ((n', _) : as) n | n == n' = removeAssum as n
removeAssum (a:as) n = a : removeAssum as n

test :: (Term ) -> IO ()
test e =
    do  let (res, _) = runTI (typeInference Map.empty e)
        case res of
          Left err  ->  putStrLn $ "error while inferring types: " ++ getString err
          Right t   ->  putStrLn $ show e ++ " :: " ++ show t
