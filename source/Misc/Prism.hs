module Misc.Prism where

import Control.Category (Category, id, (.))
import Control.Monad ((<=<))
import Data.List (uncons)
import Misc.Isomorph
import Prelude hiding (id, (.))

data Prism a b = Prism (a -> b) (b -> Maybe a)

instance Category Prism where
  id = Prism id Just
  Prism f g . Prism f' g' = Prism (f . f') (g' <=< g)

class ToPrism f where
  toPrism :: f a b -> Prism a b

instance ToPrism Prism where
  toPrism = id

instance ToPrism Isomorph where
  toPrism (Isomorph f g) = Prism f (Just . g)

assumeIsomorph :: Prism a b -> Isomorph a b
assumeIsomorph (Prism a b) = Isomorph a $ \x -> case b x of
  Just b -> b
  Nothing -> error "not isomorph"

cons :: Prism (a, [a]) [a]
cons = Prism (uncurry (:)) uncons

nil :: Prism () [a]
nil = Prism (const []) $ \case
  [] -> Just ()
  _ -> Nothing

singleton :: Prism a [a]
singleton = cons . secondP nil . toPrism (inverse unit')

just :: Prism a (Maybe a)
just = Prism Just id

nothing :: Prism () (Maybe a)
nothing = Prism (const Nothing) $ \case
  Nothing -> Just ()
  _ -> Nothing

left :: Prism a (Either a b)
left = Prism Left $ \case
  (Left x) -> Just x
  _ -> Nothing

right :: Prism a (Either b a)
right = Prism Right $ \case
  (Right x) -> Just x
  _ -> Nothing

firstP :: Prism a b1 -> Prism (a, b2) (b1, b2)
firstP (Prism f g) = Prism f' g'
  where
    f' (a, b) = (f a, b)
    g' (a, b) = do
      a' <- g a
      pure (a', b)

secondP :: Prism a1 b -> Prism (a2, a1) (a2, b)
secondP (Prism f g) = Prism f' g'
  where
    f' (a, b) = (a, f b)
    g' (a, b) = do
      b' <- g b
      pure (a, b')

foldlP :: Prism (b, a) b -> Isomorph (b, [a]) b
foldlP (Prism f g) = Isomorph f' g'
  where
    f' (x, xs) = foldl (curry f) x xs
    g' x = case g x of
      Nothing -> (x, [])
      Just (h, t) -> (first, items ++ [t])
        where
          (first, items) = g' h

foldrP :: Prism (a, b) b -> Isomorph ([a], b) b
foldrP (Prism f g) = Isomorph f' g'
  where
    f' (xs, x) = foldr (curry f) x xs
    g' x = case g x of
      Nothing -> ([], x)
      Just (h, t) -> (h : items, last)
        where
          (items, last) = g' t

-- note
-- this combinator may not be as safe as it appears (and as I originally thought)
-- `branch a a` never pick the second case

-- seemingly associative
-- not commutative
branch :: (ToPrism f, ToPrism g) => f a c -> g b c -> Prism (Either a b) c
branch a b = Prism pick prefer
  where
    (Prism f g) = toPrism a
    (Prism f' g') = toPrism b
    pick (Left x) = f x
    pick (Right x) = f' x
    prefer c = case g c of
      (Just x) -> Just $ Left x
      Nothing -> case g' c of
        (Just x) -> Just $ Right x
        Nothing -> Nothing

branch' :: Prism a c -> Prism b c -> Prism (Either a b) c
branch' = branch

branchDistribute :: (ToPrism f, ToPrism g) => f (x, a) c -> g (x, b) c -> Prism (x, Either a b) c
branchDistribute x y = branch x y . toPrism distribute

branchDistribute' :: (ToPrism f, ToPrism g) => f (a, x) c -> g (b, x) c -> Prism (Either a b, x) c
branchDistribute' x y = branch x y . toPrism distribute'
