module TypeSystem.Kind where

data Kind = Kind

class EmbedKind a where
  kind :: a
