module TypeSystem.Type where

data Type l s κ = Type l s deriving (Show, Functor, Foldable, Traversable)

class CheckType m p κ l s where
  checkType' :: p -> κ -> m (Type l s κ)

checkType :: forall l s κ m p. (CheckType m p κ l s) => p -> κ -> m (Type l s κ)
checkType = checkType'

class EmbedType l s κ where
  typex' :: Type l s κ -> κ

typex :: forall κ l s. (EmbedType l s κ) => l -> s -> κ
typex l s = typex' (Type l s)
