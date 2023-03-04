module Misc.Util where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (get, modify, runStateT)
import Data.Bitraversable (bitraverse)
import Data.Foldable (toList)
import Data.List (find)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Void (Void, absurd)

firstM f = bitraverse f pure

secondM g = bitraverse pure g

zipWithM f a b = sequence $ zipWith f (toList a) (toList b)

temporaries prefixes =
  prefixes ++ do
    i <- [0 ..]
    prefix <- prefixes
    pure $ prefix ++ show i

uppers = ((: []) <$> ['A' .. 'Z'])

fresh disallow canditate = fromJust $ find (flip Set.notMember disallow) $ temporaries [canditate]

-- https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search

data Mark = Temporary | Permanent deriving (Eq)

-- todo use ListT

-- dualed topological sort
-- if there is an edge from node `a` to `b`
-- then `b` will appear before `a`

-- nodes my depend on items not in given list
-- ie `topological [a,b]`, where `a` depends on `c`
sortTopological ::
  (Monad m, Ord k) =>
  (n -> k) ->
  (n -> m Void) ->
  (n -> m [n]) ->
  [n] ->
  m [n]
sortTopological view quit children items = go Map.empty items
  where
    go marks (item : items) = do
      (depend, marks') <- case Map.lookup (view item) marks of
        Nothing -> runStateT (visitTopological item) marks
        Just Temporary -> error "Unexpected temporary"
        Just Permanent -> pure ([], marks)
      (reverse depend ++) <$> go marks' items
    go _ [] = pure []

    -- builds a list in sTypeAndard topological sort to then get reversed by `go`
    visitTopological node = do
      marks <- get
      case Map.lookup (view node) marks of
        Just Permanent -> pure []
        Just Temporary -> fmap absurd $ lift $ quit node
        Nothing -> do
          modify $ Map.insert (view node) Temporary
          nodes <- lift $ children node
          depend <- for nodes visitTopological
          modify $ Map.insert (view node) Permanent
          pure (node : concat depend)
