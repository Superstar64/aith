module Environment where

import Data.Set (Set)
import qualified Data.Set as Set
import Misc.Identifier (Identifier)

class Usage lΓ where
  useEverything :: lΓ
  branch :: lΓ -> lΓ -> lΓ
  useNothing :: lΓ
  combine :: lΓ -> lΓ -> lΓ

branchAll = foldl branch useEverything

combineAll = foldl combine useNothing

instance Usage () where
  useEverything = ()
  branch () () = ()
  useNothing = ()
  combine () () = ()

data Use = Use Identifier | Everything | Branch Use Use | Empty | Both Use Use | Remove Identifier Use deriving (Show)

instance Usage Use where
  useEverything = Everything
  branch = Branch
  useNothing = Empty
  combine = Both

variables :: Use -> Set Identifier
variables (Use x) = Set.singleton x
variables Everything = mempty
variables (Branch a b) = variables a <> variables b
variables Empty = mempty
variables (Both a b) = variables a <> variables b
variables (Remove x a) = Set.delete x (variables a)

data Count = None | Single | Multiple

count :: Identifier -> Use -> Count
count x (Use x') | x == x' = Single
count _ (Use _) = None
count _ Everything = Single
count x (Branch a b) = count x a `or` count x b
  where
    or None None = None
    or Single Single = Single
    or _ _ = Multiple
count _ Empty = None
count x (Both a b) = count x a `and` count x b
  where
    and None c = c
    and c None = c
    and _ _ = Multiple
count x (Remove x' _) | x == x' = None
count x (Remove _ a) = count x a
