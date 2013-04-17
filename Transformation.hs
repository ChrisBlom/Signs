{-# LANGUAGE TypeFamilies, ScopedTypeVariables, FlexibleContexts, FlexibleInstances, ConstrainedClassMethods, MultiParamTypeClasses, FunctionalDependencies, PolymorphicComponents, RankNTypes, GeneralizedNewtypeDeriving #-}
module Optionalization where

import Data.List

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
data E = Alice | Bob | Cake | Donald | Earl | Sand deriving (Eq,Show,Enum,Bounded)

-- Finite : showable types with finite domains (used for quantification and showing)
class (Enum a,Bounded a,Show a) => Finite a where
  domain :: (Enum a,Bounded a) => [a]
  domain =  [minBound..maxBound]

instance Finite E 
instance Finite Bool
instance (Finite a,Finite b) => Finite (a,b)
instance (Finite a) => Finite (Marked a) 
instance (Finite a) => Finite (Optional a)
-- (actually functions with finite domains/codomains are also finite, but we dont need this here)

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
 fromEnum (x,y)  = let cardX = 1+ fromEnum (maxBound :: a) in (fromEnum x) + ((fromEnum y) * cardX)
 toEnum n = let
   cardX = 1+fromEnum (maxBound :: a) 
   x = n `mod` cardX
   y = n `div` cardX
   in (toEnum x, toEnum y)

-- char. functions of set can be shown (as sets)
instance (Finite a) => Show (a->Bool) where
  show f = braces . intercalate "," . map show . filter f $ (domain :: [a])
-- char. functions of binary relations can be shown (as functions and as relations)
instance (Finite a,Finite b)
         => Show (a->b->Bool) where
   show f = let 
      cartesian a b = [ (a',b') | a' <- a , b' <- b]      
      productDom = cartesian (domain) (domain) 
      fun = ( ++ "\no.w. |-> False")
          . intercalate "\n" 
          . map ( \(x,fx) -> concat [show x , " |-> " ,show fx] )
          . filter (\x -> snd x)
          . map (\x -> (x, uncurry f x ) )  
          $ productDom
      set = braces . intercalate "," . map show 
          . filter (uncurry f)
          $ productDom
      in "as function:\n" ++ fun ++"\n\nas set:\n" ++ set

-- char. functions of ternary relations can be shown (as functions and as relations)
instance (Finite a,Finite b,Finite c)
         => Show (a->b->c->Bool) where
   show f = let 
      uncurry3 f (x,y,z) = f x y z
      cartesian3 a b c= [ (a',b',c') | a' <- a , b' <- b , c' <- c]   
      productDom = cartesian3 (domain) (domain) (domain)
      fun = ( ++ "\no.w. |-> False") . intercalate "\n" 
          . map ( \(x,fx) -> concat [show x , " |-> " ,show fx] )
          . filter (\x -> snd x)
          . map (\x -> (x, uncurry3 f x ) )  
          $ productDom
      set = braces . intercalate "," 
           . map show . filter (uncurry3 f)
           $ productDom
      in "as function:\n" ++ fun ++"\n\nas set:\n" ++ set

braces = (\x -> "{" ++ x++"}")      
  
-- existential quantification : implemented the union over the image of a function, with a finite domain, that returns Booleans
exists :: (Finite a) => (a -> Bool) -> Bool
exists f = let image = [ (f x) | x <- domain ] in or image

-- Closable type class : all boolean types with finite domains
-- Think of it as a generalized exists, that quantifies over the first argument with the narrowest possible scope,
--  leaving the other arguments available for composition)
-- close (f : a -> t) = exists f                                                        :: t
-- close (f : a -> b -> t) = \(y :: b) -> exists (\(x :: a) -> f x y)                   :: b -> t
-- close (f : a -> b -> c -> t) = \(y::b) -> \(z :: c) -> exists (\(x :: a) -> f x y z) :: b -> c -> t
-- etc..
class Closable c where
 close :: (Finite a) => (a -> c) -> c
instance Closable Bool where
 close = exists
instance (Finite a,Closable c) => Closable (a->c) where 
 close f = \x -> close ( \y -> f y x ) 

-- example verb denotation for eat : alice and bob eat cake
eat :: E -> E -> Bool
eat Cake Alice = True
eat Cake Bob = True
eat _ _ = False

--             by  to   patient
passIntroduce Bob Earl Alice = True -- Alice was introduced to Earl by Bob
passIntroduce Earl Alice Bob = True -- Bob  was introduced to Alice by Earl
passIntroduce _ _ _ = False


-- try : optionalizes the first argument, closes over the first argument when its missing
try :: (Finite a, Closable b) => (a -> b) -> (Optional a -> b)
try f x = case x of
  Present x' -> f(x')
  Missing -> close f

-- Marker newtype : used to mark which arguments to are to be optionalized 
newtype Marked a = Marker a deriving (Eq,Show,Enum,Bounded)

-- try' : handles the marker
try' :: (Finite a, Closable b) => (Marked a -> b) -> (Optional a -> b)
try' f = try ( \x -> f (Marker x) )

-- marks the first argument
mark1 :: (a -> b) -> (Marked a) -> b
mark1 f (Marker x) = f x

-- marks the second argument
mark2 :: (a -> b -> c) -> a -> (Marked b) -> c
mark2 f x (Marker y) = f x y


-- marked versions of eat and passive introduce
markedEat = mark1 eat
markedPassIntroduce = mark1 . mark2 $ passIntroduce

-- The general optionalization procedure
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

-- first arg is marked : apply try, and recursively apply _OPT
instance (Finite a
         ,Optionalizable b
         ,Closable (Optionalized b))
         => Optionalizable (Marked a->b) where 
  type Optionalized (Marked a->b) = Optional a -> Optionalized b
  _OPT f = try' ( \x ->  _OPT(f x) )
  
-- first arg is unmarked : abstract over first arg and recursively apply _OPT
-- (For now, only E is unmarked, as distinguishing Marked from other types is a hassle in haskell)
instance (Optionalizable b
         ,Closable (Optionalized b))
         => Optionalizable (E->b) where 
  type Optionalized ( E->b) = E -> Optionalized b
  _OPT f = ( \x ->  _OPT(f x) )  

