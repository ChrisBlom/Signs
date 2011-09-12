module Grammar where

import Signature
import Inference
import Reductions
import qualified Data.Map as Map
import Data.List

data Grammar = Grammar 
  { signatureNames :: (String,[String])
  , typemappings :: [Map.Map Type [Type]]
  , signs :: [Sign]
  }
  
  
  
  
  
  
  
instance Show Grammar where
  show g = concat $ intersperse "\n"
    [ show $ signatureNames g
    , show $typemappings g 
    , show $ signs g
    ]
  

