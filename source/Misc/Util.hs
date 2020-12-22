module Misc.Util where

import Data.Bitraversable (bitraverse)
import Data.Foldable (toList)
import Data.Type.Equality ((:~:) (..))

class Same a b where
  same :: Maybe (a :~: b)

firstM f = bitraverse f pure

zipWithM f a b = sequence $ zipWith f (toList a) (toList b)
