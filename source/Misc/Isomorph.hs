module Misc.Isomorph where

import Control.Category (Category, id, (.))
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Prelude hiding (id, (.))

data Isomorph a b = Isomorph (a -> b) (b -> a)

instance Category Isomorph where
  id = Isomorph id id
  Isomorph f g . Isomorph f' g' = Isomorph (f . f') (g' . g)

inverse :: Isomorph a b -> Isomorph b a
inverse (Isomorph f g) = Isomorph g f

evalInto :: Isomorph a a' -> (a -> b) -> a' -> b
evalInto i f e = f $ from e
  where
    (Isomorph _ from) = i

mapWith :: Isomorph a b -> (a -> a) -> b -> b
mapWith i f e = to $ f $ from e
  where
    (Isomorph to from) = i

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

associate :: Isomorph ((a, b), c) (a, (b, c))
associate = Isomorph f g
  where
    f ((a, b), c) = (a, (b, c))
    g (a, (b, c)) = ((a, b), c)

associate' = inverse associate

firstI :: Isomorph a b -> Isomorph (a, c) (b, c)
firstI (Isomorph f g) = Isomorph f' g'
  where
    f' (a, b) = (f a, b)
    g' (a, b) = (g a, b)

secondI :: Isomorph a b -> Isomorph (c, a) (c, b)
secondI (Isomorph f g) = Isomorph f' g'
  where
    f' (a, b) = (a, f b)
    g' (a, b) = (a, g b)

-- extract info from something already parsed

extractInfo :: (b -> a) -> Isomorph b (a, b)
extractInfo extract = Isomorph (\a -> (extract a, a)) snd

-- discord info, prefering the second

discardInfo :: (b -> a) -> Isomorph (a, b) b
discardInfo generate = inverse (extractInfo generate)

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

orderless :: Ord k => Isomorph [(k, v)] (Map k v)
orderless = Isomorph Map.fromList Map.toList

orderlessSet :: Ord k => Isomorph [k] (Set k)
orderlessSet = Isomorph Set.fromList Set.toList

maybe' :: Isomorph (Either () a) (Maybe a)
maybe' = Isomorph g f
  where
    g (Left ()) = Nothing
    g (Right x) = Just x
    f Nothing = Left ()
    f (Just x) = Right x

imap (Isomorph f g) = Isomorph (fmap f) (fmap g)

-- some helpers need by syntax

swap_1_4_associate :: Isomorph (a, (((b, c), d), e)) ((((a, e), b), c), d)
swap_1_4_associate = Isomorph (\(e, (((pm, c), π), σ)) -> ((((e, σ), pm), c), π)) (\((((e, σ), pm), c), π) -> (e, (((pm, c), π), σ)))

rotateLast3 :: Isomorph (((a, b), c), d) (((a, d), b), c)
rotateLast3 = Isomorph (\(((pm, c), π), σ) -> (((pm, σ), c), π)) (\(((pm, σ), c), π) -> (((pm, c), π), σ))

swapLast2 :: Isomorph (((a, b), c), d) (((a, b), d), c)
swapLast2 = associate' . secondI swap . associate
