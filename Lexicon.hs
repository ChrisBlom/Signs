module Lexicon where

import Signature
import Reductions
import Inference
  
import System.IO.Unsafe
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State

class (Signature a,Signature b) => Lexicon a b where
  constantMap :: ConstantOf a -> Term b
  atomicMap   :: AtomOf a -> Type b
  termMapping :: Term a -> Term b 
  typeMapping :: Type a -> Type b
  termMapping = cmap constantMap
  typeMapping = amap atomicMap 


class Mappable f a b where
  to :: b -> f a -> f b 
instance (Lexicon a b) => Mappable Type a b where
  to x = typeMapping 
instance (Lexicon a b) => Mappable Term a b where
  to x = termMapping  

  
check target term =  unsafePerformIO $ disp $ (to target $ typeOf term) `mgu`  ( typeOf $ to target term)
 
 
check2 target term =  validSubst $ (to target $ typeOf term) `mgu`  ( typeOf $ to target term) 
  
  
checkLexicon source target =  all (\x -> ( check2 target x)) (map Con (allConstants source))
 

  
  
  
  
