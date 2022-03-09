module Misc.Util where

import Control.Monad.State.Strict (StateT, get, modify)
import Control.Monad.Trans (lift)
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

data Mark = Unmarked | Temporary | Permanent deriving (Eq)

visitTopological ::
  (Ord k, Monad m) =>
  (n -> v) ->
  (n -> k) ->
  (n -> m ()) ->
  (n -> m [n]) ->
  n ->
  StateT (Map k Mark) (StateT [v] m) ()
visitTopological finish view quit children node = do
  marks <- get
  case marks Map.! view node of
    Permanent -> pure ()
    Temporary -> lift $ lift $ quit node
    Unmarked -> do
      modify $ Map.insert (view node) Temporary
      nodes <- lift $ lift $ children node
      for nodes (visitTopological finish view quit children)
      modify $ Map.insert (view node) Permanent
      lift $ modify $ (finish node :)

sortTopological ::
  (Monad m, Ord k) =>
  (k -> n) ->
  (n -> v) ->
  (n -> k) ->
  (n -> m ()) ->
  (n -> m [n]) ->
  StateT (Map k Mark) (StateT [v] m) ()
sortTopological index finish view quit children = do
  this <- get
  let item = find (\(_, mark) -> mark /= Permanent) (Map.toList this)
  case item of
    Nothing -> pure ()
    Just (path, _) -> do
      visitTopological finish view quit children (index path)
      sortTopological index finish view quit children
