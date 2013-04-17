{-# LANGUAGE TypeFamilies, ScopedTypeVariables, UndecidableInstances, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, RankNTypes, GeneralizedNewtypeDeriving #-}
module Optionalization where

import Data.List 
import Prelude hiding (read)
import Control.Applicative

-- The datatype for optional values. (isomorphic to Data.Maybe)
data Optional a 
  = Present a 
  | Missing 
  deriving Eq

-- how to print Optional values
instance (Show a) => Show (Optional a) where
  show (Present a) = show a ++"^"
  show (Missing) = "*"

-- Datatype for entities
data E = Alice | Bob | Cake | Donald | Earl | Sand | Lolita deriving (Eq,Show,Enum,Bounded)
data S = A | B | C | D | E | F deriving (Eq,Show,Enum,Bounded)
type T = Bool

someone f = exists f



class IE a where
  type INT a :: *
  int :: (S -> a) -> INT a
  ext :: INT  a -> S -> a

instance IE E where
  type INT E = S -> E
  int = id
  ext = id

instance IE T where
  type INT T = S -> T
  ext = id
  int = id

instance (IE a,IE b) => IE (a -> b) where
  type INT (a -> b) = INT a -> INT b
  int f x   = int (\i -> f i ((ext x) i) )
  ext f i x = ext ( f (int (\_ -> x)) ) i

-- Finite : types with a finite domain
-- This restriction is required for used for quantification and showing
class (Enum a,Bounded a,Show a) => Finite a where
  domain :: (Enum a,Bounded a) => [a]
  domain =  [minBound..maxBound]

instance Finite E 
instance Finite S
instance Finite Bool
instance (Finite a,Finite b) => Finite (a,b)
instance (Finite a) => Finite (Marked a) 
instance (Finite a) => Finite (Optional a)
-- (actually functions with finite domains are also finite, but we dont need this here)

-- Some instances of Enum and Bounded, used for Show'ing of types
instance Enum a => Enum (Optional a) where 
 fromEnum Missing  = 0
 fromEnum (Present x) = 1 + fromEnum (x::a)
 toEnum 0 = Missing
 toEnum n = Present (toEnum $ n-1)
--
instance Bounded a => Bounded (Optional a) where
 minBound = Missing
 maxBound = Present (maxBound :: a)
-- products of Enumerable types are Enumerable
instance (Bounded a,Enum a,Enum b) => Enum (a,b) where 
 fromEnum (x,y)  = let cardX = 1 + fromEnum (maxBound :: a) in (fromEnum x) + ((fromEnum y) * cardX)
 toEnum n = let
   cardX = 1+fromEnum (maxBound :: a) 
   x = n `mod` cardX
   y = n `div` cardX
   in (toEnum x, toEnum y)


(><) :: (a->b) -> (x->y) -> (a,x) -> (b,y)
f >< g = \(x,y) -> (f x, g y)


-- char. functions of set can be shown (as sets)
instance (Finite a) => Show (a->Bool) where
  show f = braces . intercalate "," . map show . filter f $ (domain :: [a])
-- char. functions of binary relations can be shown (as functions and as relations)
instance (Finite a,Finite b)
         => Show (a->b->Bool) where
   show f = let
      productDomain = (domain :: [(a,b)])
      fun = ( \(n,str) -> concat [str,"\n\t",fill "o.w." n," |-> False"]) 
          $ ( id >< intercalate "\n" )
          $ ( \(pairs,n) -> (n,map ( \(x,fx) -> concat [ "\t",fill x n," |-> ",fx] ) pairs ))
          $ foldr ( \(arg,res)  (acc,n) -> ( (show arg , show res) : acc, n `max` (length $ show arg) )) ([],0)
          $ filter snd               -- only keep if result is true
          $ map (\x -> (x, uncurry f x) )                                 
          $ productDomain
      set = braces . intercalate "," . map show 
          $ filter (uncurry f)
          $ productDomain
      in "as function:\n" ++ fun ++"\n\nas set:\n\t" ++ set


fill x n = take n (x++repeat ' ')
-- char. functions of ternary relations can be shown (as functions and as relations)
instance (Finite a,Finite b,Finite c)
         => Show (a->b->c->Bool) where
   show f = let 
      uncurry3 f (x,y,z) = f x y z
      cartesian3 a b c= [ (a',b',c') | a' <- a , b' <- b , c' <- c]   
      productDom = cartesian3 (domain) (domain) (domain)
      fun = ( \(n,str) -> concat [str,"\n\t",fill "o.w." n," |-> False"]) 
          . ( id >< intercalate "\n" )
          . ( \(pairs,n) -> (n,map ( \(x,fx) -> concat ["\t",fill x n," |-> ",fx] ) pairs ))
          . foldr ( \(arg,res)  (acc,n) -> ( (show arg , show res) : acc, n `max` (length $ show arg) )) ([],0)
          . filter snd
          . map (\x -> (x, uncurry3 f x ) )  
          $ productDom
      set = braces . intercalate "," 
           . map show . filter (uncurry3 f)
           $ productDom
      in "as function:\n" ++ fun ++"\n\nas set:\n" ++ set

braces = (\x -> "{" ++ x++"}")      
  
-- existential quantification : implemented a the union over the image of a function
--The function to quantify over must have a finite domain, and its co-domain must be Bool
exists :: (Finite a) => (a -> Bool) -> Bool
exists f = let image = [ (f x) | x <- domain ] in or image

-- Closable type class : all Boolean types with finite domains
-- Think of it as a generalized exists, that quantifies over the first argument with the narrowest possible scope,
--  leaving the other arguments available for composition)
-- close (f : a -> t) = exists f                                                        :: t
-- close (f : a -> b -> t) = \(y :: b) -> exists (\(x :: a) -> f x y)                   :: b -> t
-- close (f : a -> b -> c -> t) = \(y::b) -> \(z :: c) -> exists (\(x :: a) -> f x y z) :: b -> c -> t
-- etc..
class Boolean b where
 close :: (Finite a) => (a -> b) -> b
instance Boolean Bool where
 close = exists
instance (Finite a,Boolean b) => Boolean (a->b) where 
 close f = \x -> close ( \y -> f y x ) 


read :: E -> E -> Bool
read pat ag = (ag,pat) `elem` [(Bob,Lolita)]

-- example verb denotation for eat : alice and bob eat cake
eat :: E -> E -> Bool
eat Cake Alice = True
eat Cake Bob = True
eat _ _ = False

--             by  to   patient
passIntroduce :: E -> E -> E -> Bool 
passIntroduce Bob Earl Alice = True -- Alice was introduced to Earl by Bob
passIntroduce Earl Alice Bob = True -- Bob  was introduced to Alice by Earl
passIntroduce _ _ _ = False


-- try : optionalizes the first argument, closes over the first argument when its missing
try :: (Finite a, Boolean b) => (a -> b) -> (Optional a -> b)
try f x = case x of
  Present x' -> f(x')
  Missing -> close f

-- Marker newtype : used to mark which arguments to are to be optionalized 
newtype Marked a = Marker a deriving (Eq,Show,Enum,Bounded)

-- try' : handles the marker (this is not needed in the paper)
try' :: (Finite a, Boolean b) => (Marked a -> b) -> (Optional a -> b)
try' f = try ( \x -> f (Marker x) )

-- marks the first argument for optionalization
mark1 :: (a -> b) -> (Marked a) -> b
mark1 f (Marker x) = f x

-- marks the second argument
mark2 :: (a -> b -> c) -> a -> (Marked b) -> c
mark2 f x (Marker y) = f x y


-- marked versions of eat and passive introduce
markedEat = mark1 eat
markedPassIntroduce = mark1 . mark2 $ passIntroduce

-- The general optionalization procedure, defined using type families
-- to allow case distinction on types
class Optionalizable a where
 type Optionalized a
 _OPT :: a -> (Optionalized a)

-- Optionalization does not affect basic types:
instance Optionalizable E where
  type (Optionalized E) = E
  _OPT = id
instance Optionalizable Bool where
  type (Optionalized Bool) = Bool
  _OPT = id  

-- Case 1, the first arg. is marked : apply try to optionalize it, and recursively apply _OPT to transform the rest
instance (Finite a                   -- the argument's domain must be finite (for quantification)
         ,Optionalizable b           -- the function result must optionalizable
         ,Boolean
         (Optionalized b)  -- the result of opt must be closable
         ) => Optionalizable (Marked a->b) where 
  type Optionalized (Marked a->b) = Optional a -> Optionalized b
  _OPT f = try' ( \x ->  _OPT(f x) )
  
-- Case 2, the first arg. is unmarked : abstract over first arg and recursively apply _OPT
-- (Any function with a finite domain would do, but as distinguishing Marked from other 
--  is types is a hassle in haskell, its only implemented for E)
instance (Optionalizable b
         ,Boolean
         (Optionalized b))
         => Optionalizable (E->b) where 
  type Optionalized ( E->b) = E -> Optionalized b
  _OPT f = ( \x ->  _OPT(f x) )  



main = print read