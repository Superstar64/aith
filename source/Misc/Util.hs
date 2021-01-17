module Misc.Util where

import Data.Bitraversable (bitraverse)
import Data.Foldable (toList)

firstM f = bitraverse f pure

zipWithM f a b = sequence $ zipWith f (toList a) (toList b)
