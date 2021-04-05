module Misc.Path where

import Misc.Identifier (Identifier)
import Misc.Isomorph

data Path = Path [Identifier] Identifier deriving (Show, Eq, Ord)

path :: Isomorph ([Identifier], Identifier) Path
path = Isomorph (uncurry Path) go
  where
    go (Path a b) = (a, b)
