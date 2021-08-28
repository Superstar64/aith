module Environment where

import Data.Set (Set)
import qualified Data.Set as Set

data Use i = Use i | Everything | Branch (Use i) (Use i) | Empty | Combine (Use i) (Use i) | Remove i (Use i) deriving (Show)

useEverything = Everything

combine = Combine

useNothing = Empty

branch = Branch

branchAll = foldl Branch useEverything

combineAll = foldl combine useNothing

variablesUsed :: Ord i => Use i -> Set i
variablesUsed (Use x) = Set.singleton x
variablesUsed Everything = mempty
variablesUsed (Branch a b) = variablesUsed a <> variablesUsed b
variablesUsed Empty = mempty
variablesUsed (Combine a b) = variablesUsed a <> variablesUsed b
variablesUsed (Remove x a) = Set.delete x (variablesUsed a)

data Count = None | Single | Multiple

count :: Ord i => i -> (Use i) -> Count
count x (Use x') | x == x' = Single
count _ (Use _) = None
count _ Everything = Single
count x (Branch a b) = count x a `or` count x b
  where
    or None None = None
    or Single Single = Single
    or _ _ = Multiple
count _ Empty = None
count x (Combine a b) = count x a `and` count x b
  where
    and None c = c
    and c None = c
    and _ _ = Multiple
count x (Remove x' _) | x == x' = None
count x (Remove _ a) = count x a
