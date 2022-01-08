module Misc.Util where

import Control.Monad.State (get, modify)
import Control.Monad.Trans (lift)
import Data.Bitraversable (bitraverse)
import Data.Foldable (toList)
import Data.List (find)
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Data.Traversable (for)
import qualified Misc.MonoidMap as Map

firstM f = bitraverse f pure

secondM g = bitraverse pure g

zipWithM f a b = sequence $ zipWith f (toList a) (toList b)

temporaries' prefixes =
  prefixes ++ do
    i <- [0 ..]
    prefix <- prefixes
    pure $ prefix ++ show i

temporaries prefix = temporaries' [prefix]

fresh disallow canditate = fromJust $ find (flip Set.notMember disallow) $ temporaries canditate

-- https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search

data Mark = Unmarked | Temporary | Permanent deriving (Eq)

visitTopological quit nodes (p, path, global) =
  let visit = visitTopological quit nodes
   in do
        marks <- get
        case marks Map.! path of
          Permanent -> pure ()
          Temporary -> quit p path
          Unmarked -> do
            modify $ Map.insert path Temporary
            children <- nodes global path
            for children visit
            modify $ Map.insert path Permanent
            lift $ modify $ ((path, global) :)
