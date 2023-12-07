module Ast.Symbol where

import Data.List.NonEmpty (NonEmpty (..), (<|))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Set (Set)
import qualified Data.Set as Set
import Misc.Isomorph
import qualified Misc.Util as Util

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

data Symbol = Symbol String deriving (Show)

newtype TermIdentifier = TermIdentifier {runTermIdentifier :: String} deriving (Show, Eq, Ord)

newtype TermGlobalIdentifier = TermGlobalIdentifier {runTermGlobalIdentifier :: Path} deriving (Show, Eq, Ord)

newtype TypeIdentifier = TypeIdentifier {runTypeIdentifier :: String} deriving (Show, Eq, Ord)

newtype TypeGlobalIdentifier = TypeGlobalIdentifier {runTypeGlobalIdentifier :: Path} deriving (Show, Eq, Ord)

symbol = Isomorph Symbol $ \(Symbol x) -> x

class Fresh i where
  fresh :: Set i -> i -> i

instance Fresh TermIdentifier where
  fresh xs (TermIdentifier x)
    | xs <- Set.mapMonotonic runTermIdentifier xs = TermIdentifier (Util.fresh xs x)

instance Fresh TypeIdentifier where
  fresh xs (TypeIdentifier x)
    | xs <- Set.mapMonotonic runTypeIdentifier xs = TypeIdentifier (Util.fresh xs x)

globalTerm heading (TermIdentifier x) = TermGlobalIdentifier (combine heading x)

globalType heading (TypeIdentifier x) = TypeGlobalIdentifier (combine heading x)
