module Misc.Util where

import Data.Bitraversable (bitraverse)
import Data.Foldable (toList)

firstM f = bitraverse f pure

secondM g = bitraverse pure g

zipWithM f a b = sequence $ zipWith f (toList a) (toList b)
