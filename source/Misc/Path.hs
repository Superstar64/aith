module Misc.Path where

import Misc.Isomorph

data Path = Path [String] String deriving (Show, Eq, Ord)

path :: Isomorph ([String], String) Path
path = Isomorph (uncurry Path) go
  where
    go (Path a b) = (a, b)
