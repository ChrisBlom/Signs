module Signs.MyError where

import Data.Either
import Control.Monad.Error
import Control.Applicative

maybeToError msg f x = case x of
  (Just a) -> Right $ f a
  Nothing  -> Left $ msg (show x)

type MessageError a = Either ErrorMessage a

type ErrorMessage = String
type SuccesMessage = String

(f .|. g) x = case x of
  Left  x' -> Left  (f x')
  Right x' -> Right (g x')

left  f = (f .|. id)
right f = (id .|. f)

try (Right x) f = f x
try (Left x) f = putStrLn x
