module Misc.Path where

import Data.List.NonEmpty (NonEmpty (..), (<|))
import qualified Data.List.NonEmpty as NonEmpty
import Misc.Isomorph
import Misc.Symbol

newtype Path = Path {runPath :: NonEmpty String} deriving (Show, Eq, Ord)

path = Isomorph Path runPath

newtype SemiPath = SemiPath {runSemiPath :: [String]} deriving (Show, Eq, Ord)

semiPath = Isomorph SemiPath runSemiPath

combine :: SemiPath -> String -> Path
combine (SemiPath semi) name = Path (foldr (<|) (NonEmpty.singleton name) semi)

forget :: Path -> SemiPath
forget (Path (x :| xs)) = SemiPath (x : xs)

root = SemiPath []

directory (Path path) = SemiPath (NonEmpty.init path)

prepend (SemiPath []) path = path
prepend (SemiPath (p : ps)) (Path path) = Path $ (p :| ps) <> path

mangle :: Path -> Symbol
mangle (Path full) = Symbol $ (concat $ map (++ "_") $ extract <$> path) ++ name
  where
    extract x = x
    path = NonEmpty.init full
    name = NonEmpty.last full

startsWith :: SemiPath -> Path -> Maybe (Path)
startsWith (SemiPath []) path = Just path
startsWith (SemiPath (x : xs)) (Path (x' :| (p : ps))) | x == x' = startsWith (SemiPath xs) (Path (p :| ps))
startsWith _ _ = Nothing
