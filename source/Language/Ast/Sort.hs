module Language.Ast.Sort where

import Language.Ast.Common
import Misc.Prism

data Sort = Kind | Stage | Impact | Existance | Representation | Size | Signedness deriving (Show)

kind = Prism (const Kind) $ \case
  Kind -> Just ()
  _ -> Nothing

stage = Prism (const Stage) $ \case
  Stage -> Just ()
  _ -> Nothing

impact = Prism (const Impact) $ \case
  Impact -> Just ()
  _ -> Nothing

existance = Prism (const Existance) $ \case
  Existance -> Just ()
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

instance Substitute e x Sort where
  substitute _ _ = id
