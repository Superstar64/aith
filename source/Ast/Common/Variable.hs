module Ast.Common.Variable where

import Data.Set (Set)
import qualified Data.Set as Set
import Misc.Path (Path)
import qualified Misc.Path as Path
import qualified Misc.Util as Util

newtype TermIdentifier = TermIdentifier {runTermIdentifier :: String} deriving (Show, Eq, Ord)

newtype TermGlobalIdentifier = TermGlobalIdentifier {runTermGlobalIdentifier :: Path} deriving (Show, Eq, Ord)

globalTerm heading (TermIdentifier x) = TermGlobalIdentifier (Path.combine heading x)

newtype TypeIdentifier = TypeIdentifier {runTypeIdentifier :: String} deriving (Show, Eq, Ord)

newtype TypeGlobalIdentifier = TypeGlobalIdentifier {runTypeGlobalIdentifier :: Path} deriving (Show, Eq, Ord)

newtype TypeLogical = TypeLogicalRaw Int deriving (Eq, Ord, Show)

globalType heading (TypeIdentifier x) = TypeGlobalIdentifier (Path.combine heading x)

class Fresh i where
  fresh :: Set i -> i -> i

instance Fresh TypeIdentifier where
  fresh c (TypeIdentifier x) = TypeIdentifier $ Util.fresh (Set.mapMonotonic runTypeIdentifier c) x

instance Fresh TermIdentifier where
  fresh c (TermIdentifier x) = TermIdentifier $ Util.fresh (Set.mapMonotonic runTermIdentifier c) x
