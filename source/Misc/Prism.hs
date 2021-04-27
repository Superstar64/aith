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

cons :: Prism (a, [a]) [a]
cons = Prism (uncurry (:)) uncons

nil :: Prism () [a]
nil = Prism (const []) $ \case
  [] -> Just ()
  _ -> Nothing

just :: Prism a (Maybe a)
just = Prism Just $ \case
  Just x -> Just x
  Nothing -> Nothing

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

foldlP :: Prism (a, b) a -> Isomorph (a, [b]) a
foldlP (Prism f g) = Isomorph f' g'
  where
    f' (x, xs) = foldl (curry f) x xs
    g' x = case g x of
      Nothing -> (x, [])
      Just (a, b) -> (first, a' ++ [b])
        where
          (first, a') = g' a

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

branchDistribute :: (ToPrism f, ToPrism g) => f (a, b1) c -> g (a, b2) c -> Prism (a, Either b1 b2) c
branchDistribute x y = branch x y . toPrism distribute
