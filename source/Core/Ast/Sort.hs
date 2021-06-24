module Core.Ast.Sort where

import Misc.Prism

data Sort = Kind | Stage | Impact | Existance | Representation deriving (Show)

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
