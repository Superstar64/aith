module TypeSystem.Type where

import TypeSystem.Kind
import TypeSystem.Methods
import TypeSystem.Stage

data Type μs s = Type s deriving (Show, Functor, Foldable, Traversable)

class EmbedType κ s where
  typex :: s -> κ

class CheckType s κ m p where
  checkType :: p -> κ -> m (Type μs s)

instance
  ( Monad m,
    EmbedKind μκ,
    TypeCheck μs m s,
    CheckStage μs p m
  ) =>
  TypeCheckImpl m p (Type μs s) μκ
  where
  typeCheckImpl p (Type s) = do
    Stage <- checkStage p =<< typeCheck @μs s
    pure kind

instance FreeVariables u s => FreeVariables u (Type μs s) where
  freeVariables (Type s) = freeVariables @u s

instance (EmbedType κ s, Substitute u s) => SubstituteImpl (Type μs s) u κ where
  substituteImpl ux x (Type s) = typex $ substitute ux x s
