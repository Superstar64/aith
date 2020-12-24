module TypeSystem.Type where

data Type s κ = Type s deriving (Show, Functor, Foldable, Traversable)

class CheckType m p κ s where
  checkType' :: p -> κ -> m (Type s κ)

checkType :: forall s κ m p. (CheckType m p κ s) => p -> κ -> m (Type s κ)
checkType = checkType'

class EmbedType s κ where
  typex' :: Type s κ -> κ

typex :: forall κ s. (EmbedType s κ) => s -> κ
typex s = typex' (Type s)
