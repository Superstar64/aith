module Misc.MonoidMap where

import qualified Data.Map as Map

-- boiler plate wrapper because map's default monoid instance is wrong
-- everything is forworded to vanilla map

newtype Map k v = Map {toMap :: Map.Map k v} deriving (Functor, Foldable, Traversable, Show)

instance (Ord k, Semigroup v) => Semigroup (Map k v) where
  Map left <> Map right = Map $ Map.unionWith (<>) left right

instance (Ord k, Semigroup v) => Monoid (Map k v) where
  mempty = Map Map.empty
  mappend = (<>)

member key (Map variables) = Map.member key variables

notMember key (Map variables) = Map.notMember key variables

insert k v (Map m) = Map $ Map.insert k v m

findWithDefault a k (Map m) = Map.findWithDefault a k m

mapKeysMonotonic f (Map m) = Map $ Map.mapKeysMonotonic f m

lookup k (Map m) = Map.lookup k m

empty = Map Map.empty

delete name (Map variables) = Map $ Map.delete name variables

singleton name position = Map $ Map.singleton name position

toList (Map variables) = Map.toList variables

fromList xs = Map $ Map.fromList xs

union (Map a) (Map b) = Map (a <> b)

filterWithKey f (Map m) = Map $ Map.filterWithKey f m

traverseWithKey f (Map m) = Map <$> Map.traverseWithKey f m

keys (Map m) = Map.keys m

keysSet (Map m) = Map.keysSet m

adjust f x (Map m) = Map $ Map.adjust f x m

infixl 9 !

Map m ! k = m Map.! k

infixl 9 !?

Map m !? k = m Map.!? k
