module Misc.Silent where

data Silent (a :: * -> *) = Silent deriving (Show)

data Erased (a :: *)

instance Show (Erased a) where
  show = absurd

absurd :: Erased a -> b
absurd x = case x of
