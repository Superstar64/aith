module TypeSystem.Type where

import Data.Proxy (Proxy (..))

data Type l s κ = Type l s deriving (Show, Functor, Foldable, Traversable)

class CheckType m p κ l s where
  checkType :: p -> κ -> m (Type l s κ)

checkType' :: (Functor f, CheckType f p κ l s) => Proxy l -> Proxy s -> p -> κ -> f (Proxy κ, Type l s κ)
checkType' Proxy Proxy p κ = (\x -> (Proxy, x)) <$> checkType p κ

class EmbedType l s κ where
  typex' :: Type l s κ -> κ

typex l s = typex' (Type l s)
