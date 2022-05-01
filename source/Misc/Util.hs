module Misc.Util where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, execStateT, get, modify)
import Data.Bitraversable (bitraverse)
import Data.Foldable (toList)
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Data.Traversable (for)

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

data Mark = Temporary | Permanent deriving (Eq)

visitTopological ::
  (Ord k, Monad m) =>
  (n -> k) ->
  (n -> m ()) ->
  (n -> m [n]) ->
  n ->
  StateT (Map k Mark) (StateT [n] m) ()
visitTopological view quit children node = do
  marks <- get
  case Map.lookup (view node) marks of
    Just Permanent -> pure ()
    Just Temporary -> lift $ lift $ quit node
    Nothing -> do
      modify $ Map.insert (view node) Temporary
      nodes <- lift $ lift $ children node
      for nodes (visitTopological view quit children)
      modify $ Map.insert (view node) Permanent
      lift $ modify $ (node :)

sortTopological ::
  (Monad m, Ord k) =>
  (n -> k) ->
  (n -> m ()) ->
  (n -> m [n]) ->
  [n] ->
  m [n]
sortTopological view quit children items = execStateT (evalStateT (go items) Map.empty) []
  where
    go (item : items) = do
      marks <- get
      case Map.lookup (view item) marks of
        Nothing -> do
          visitTopological view quit children item
        Just Temporary -> error "Unexpected temporary"
        Just Permanent -> pure ()
      go items
    go [] = pure ()
