module Misc.Identifier where

import Data.List (find)
import Data.Maybe (fromJust)
import Data.Set (member)

data Identifier = Identifier String deriving (Show, Eq, Ord)

temporaries (Identifier prefix) = map Identifier $ prefix : (map ((prefix ++) . show) [0 ..])

fresh disallow canditate = fromJust $ find (not . (flip member disallow)) $ temporaries canditate

substituteVariable _ ex x x' | x == x' = ex
substituteVariable variable _ _ x = variable x
