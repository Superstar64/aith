module Misc.Variables where

import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Misc.Identifier

data Variables p = Variables (Map Identifier p)

instance Semigroup p => Semigroup (Variables p) where
  Variables left <> Variables right = Variables $ Map.unionWith (<>) left right

instance Semigroup p => Monoid (Variables p) where
  mempty = Variables Map.empty
  mappend = (<>)

member key (Variables variables) = Map.member key variables

notMember key (Variables variables) = Map.notMember key variables

delete name (Variables variables) = Variables $ Map.delete name variables

singleton name position = Variables $ Map.singleton name position

toList (Variables variables) = Map.toList variables

fresh disallow canditate = fromJust $ find (flip notMember disallow) $ temporaries canditate
