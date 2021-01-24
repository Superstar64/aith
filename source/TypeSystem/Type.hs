module TypeSystem.Type where

import TypeSystem.Kind
import TypeSystem.Methods

data Type ss s = Type s deriving (Show, Functor, Foldable, Traversable)

class EmbedType κ s where
  typex :: s -> κ

class CheckType s κ m p where
  checkType :: p -> κ -> m (Type ss s)

instance
  ( Monad m,
    EmbedKind κs,
    TypeCheck ss m s
  ) =>
  TypeCheckImpl m p (Type ss s) κs
  where
  typeCheckImpl _ (Type s) = do
    typeCheck @ss s
    pure kind

instance FreeVariables u s => FreeVariables u (Type ss s) where
  freeVariables (Type s) = freeVariables @u s

instance (EmbedType κ s, Substitute u s) => SubstituteImpl (Type ss s) u κ where
  substituteImpl ux x (Type s) = typex $ substitute ux x s
