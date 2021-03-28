module Misc.Path where

import Misc.Identifier (Identifier)

data Path = Path [Identifier] Identifier deriving (Show, Eq, Ord)
