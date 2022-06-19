module Ast.Sort where

import Ast.Common
import Misc.Prism

data Sort = Kind | Representation | Size | Signedness deriving (Show, Eq, Ord)

kind = Prism (const Kind) $ \case
  Kind -> Just ()
  _ -> Nothing

representation = Prism (const Representation) $ \case
  Representation -> Just ()
  _ -> Nothing

size = Prism (const Size) $ \case
  Size -> Just ()
  _ -> Nothing

signedness = Prism (const Signedness) $ \case
  Signedness -> Just ()
  _ -> Nothing

instance Reduce Sort where
  reduce = id
