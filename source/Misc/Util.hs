module Misc.Util where

import Data.Bitraversable (bitraverse)
import Data.Foldable (toList)
import Data.Proxy (Proxy (..))
import Data.Type.Equality ((:~:) (..))

class Same a b where
  same :: Maybe (a :~: b)

same' :: Same a b => Proxy a -> Proxy b -> Maybe (a :~: b)
same' Proxy Proxy = same

proxyOf :: a -> Proxy a
proxyOf _ = Proxy

firstM f = bitraverse f pure

zipWithM f a b = sequence $ zipWith f (toList a) (toList b)
