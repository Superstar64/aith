module Core.Ast.Sort where

import Misc.Prism

data Sort = Kind | Stage | Representation deriving (Show)

kind = Prism (const Kind) $ \case
  Kind -> Just ()
  _ -> Nothing

stage = Prism (const Stage) $ \case
  Stage -> Just ()
  _ -> Nothing

representation = Prism (const Representation) $ \case
  Representation -> Just ()
  _ -> Nothing

data PatternSort = Pattern

data TypePatternSort = TypePattern
