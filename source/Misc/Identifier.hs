module Misc.Identifier where

data Identifier = Identifier String deriving (Show, Eq, Ord)

temporaries (Identifier prefix) = map Identifier $ prefix : (map ((prefix ++) . show) [0 ..])

substituteVariable _ ex x x' | x == x' = ex
substituteVariable variable _ _ x = variable x
