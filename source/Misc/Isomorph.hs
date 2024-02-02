module Misc.Isomorph where

import Control.Category (Category, id, (.))
import Data.Bifunctor (Bifunctor, bimap)
import Data.Functor.Compose (Compose (..))
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Prelude hiding (id, (.))

data Isomorph a b = Isomorph (a -> b) (b -> a)

instance Category Isomorph where
  id = Isomorph id id
  Isomorph f g . Isomorph f' g' = Isomorph (f . f') (g' . g)

inverse :: Isomorph a b -> Isomorph b a
inverse (Isomorph f g) = Isomorph g f

unit :: Isomorph ((), a) a
unit = Isomorph f g
  where
    f ((), x) = x
    g x = ((), x)

unit' :: Isomorph (a, ()) a
unit' = Isomorph f g
  where
    f (x, ()) = x
    g x = (x, ())

swap :: Isomorph (a, b) (b, a)
swap = Isomorph f g
  where
    f (a, b) = (b, a)
    g (a, b) = (b, a)

swap_1_2_of_3 :: Isomorph (b, (a, c)) (a, (b, c))
swap_1_2_of_3 = associate . firstI swap . associate'

swap_2_3_of_3 :: Isomorph ((a, c), b) ((a, b), c)
swap_2_3_of_3 = associate' . secondI swap . associate

swap_2_4_of_4 :: Isomorph (((a, b), c), d) (((a, d), c), b)
swap_2_4_of_4 = Isomorph (\(((a, b), c), d) -> (((a, d), c), b)) (\(((a, b), c), d) -> (((a, d), c), b))

swap_3_4_of_4 :: Isomorph (((a, b), c), d) (((a, b), d), c)
swap_3_4_of_4 = Isomorph (\(((a, b), c), d) -> (((a, b), d), c)) (\(((a, b), c), d) -> (((a, b), d), c))

associate :: Isomorph ((a, b), c) (a, (b, c))
associate = Isomorph f g
  where
    f ((a, b), c) = (a, (b, c))
    g (a, (b, c)) = ((a, b), c)

associate' = inverse associate

fmapI :: (Functor f) => Isomorph b a -> Isomorph (f b) (f a)
fmapI (Isomorph f g) = Isomorph (fmap f) (fmap g)

bimapI :: (Bifunctor p) => Isomorph a c -> Isomorph b d -> Isomorph (p a b) (p c d)
bimapI (Isomorph f g) (Isomorph f' g') = Isomorph (bimap f f') (bimap g g')

firstI iso = bimapI iso id

secondI iso = bimapI id iso

distribute :: Isomorph (a, Either b1 b2) (Either (a, b1) (a, b2))
distribute = Isomorph f g
  where
    f (a, Left b) = Left (a, b)
    f (a, Right b) = Right (a, b)
    g (Left (a, b)) = (a, Left b)
    g (Right (a, b)) = (a, Right b)

distribute' :: Isomorph (Either b1 b2, a) (Either (b1, a) (b2, a))
distribute' = Isomorph f g
  where
    f (Left a, b) = Left (a, b)
    f (Right a, b) = Right (a, b)
    g (Left (a, b)) = (Left a, b)
    g (Right (a, b)) = (Right a, b)

nonEmpty :: Isomorph (a, [a]) (NonEmpty a)
nonEmpty = Isomorph f g
  where
    f (a, b) = a :| b
    g (a :| b) = (a, b)

list :: Isomorph (Either (NonEmpty a) ()) [a]
list = Isomorph f g
  where
    f (Left (x :| xs)) = x : xs
    f (Right ()) = []
    g ([]) = Right ()
    g (x : xs) = Left (x :| xs)

-- swap between non empty list variants
swapNonEmpty :: Isomorph (a, [a]) ([a], a)
swapNonEmpty = Isomorph f g
  where
    f (x, []) = ([], x)
    f (x, a : as) = let (c, d) = f (a, as) in (x : c, d)
    g ([], x) = (x, [])
    g (a : as, x) = (a, uncurry (:) $ g (as, x))

-- shreads off duplicate elements
orderless :: (Ord k) => Isomorph [(k, v)] (Map k v)
orderless = Isomorph Map.fromList Map.toList

orderlessMulti :: (Ord k) => Isomorph [(k, v)] (Map k (NonEmpty v))
orderlessMulti = Isomorph to from
  where
    to = foldr (\(k, v) -> Map.insertWith (<>) k (v :| [])) Map.empty
    from = Map.foldrWithKey (\k vs -> (zip (repeat k) (NonEmpty.toList vs) ++)) []

tuple3 = Isomorph to from
  where
    to ((a, b), c) = (a, b, c)
    from (a, b, c) = ((a, b), c)

tuple3' = tuple3 . associate'

tuple4 = Isomorph to from
  where
    to (((a, b), c), d) = (a, b, c, d)
    from (a, b, c, d) = (((a, b), c), d)

tuple4' = Isomorph to from
  where
    to (a, ((b, c), d)) = (a, b, c, d)
    from (a, b, c, d) = (a, ((b, c), d))

compose = Isomorph Compose getCompose
