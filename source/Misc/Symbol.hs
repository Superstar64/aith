module Misc.Symbol where

import Misc.Isomorph

data Symbol = Symbol String deriving (Show)

symbol = Isomorph Symbol $ \(Symbol x) -> x
