module Misc.Silent where

import Data.Kind (Type)

data Silent (a :: Type -> Type) = Silent deriving (Show)

data Erased (a :: Type)

instance Show (Erased a) where
  show = absurd

absurd :: Erased a -> b
absurd x = case x of
