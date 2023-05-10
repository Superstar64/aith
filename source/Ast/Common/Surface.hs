module Ast.Common.Surface where

import Ast.Common.Variable
import Data.Map (Map)
import qualified Data.Map as Map

data Variables p = Variables
  { termLocals :: Map TermIdentifier p,
    termGlobals :: Map TermGlobalIdentifier p,
    typeLocals :: Map TypeIdentifier p,
    typeGlobals :: Map TypeGlobalIdentifier p
  }

termLocal x p = Variables (Map.singleton x p) Map.empty Map.empty Map.empty

termGlobal x p = Variables Map.empty (Map.singleton x p) Map.empty Map.empty

typeLocal x p = Variables Map.empty Map.empty (Map.singleton x p) Map.empty

typeGlobal x p = Variables Map.empty Map.empty Map.empty (Map.singleton x p)

deleteTermLocal x variables = variables {termLocals = Map.delete x $ termLocals variables}

deleteTypeLocal x variables = variables {typeLocals = Map.delete x $ typeLocals variables}

instance Semigroup p => Semigroup (Variables p) where
  Variables a b c d <> Variables a' b' c' d' =
    let go = Map.unionWith (<>) in Variables (go a a') (go b b') (go c c') (go d d')

instance Semigroup p => Monoid (Variables p) where
  mappend = (<>)
  mempty = let go = Map.empty in Variables go go go go

class Alpha u where
  freeVariables :: Semigroup p => u p -> Variables p
