module TypeSystem.Type where

data Type s κ = Type s deriving (Show, Functor, Foldable, Traversable)

class CheckType s κ m p where
  checkType :: p -> κ -> m (Type s κ)

class EmbedType κ s where
  typex :: s -> κ
