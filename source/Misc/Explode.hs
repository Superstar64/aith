module Misc.Explode where

import Data.Void (Void, absurd)

class (Eq void, Ord void, Show void) => Explode void where
  explode :: void -> a

instance Explode Void where
  explode = absurd
