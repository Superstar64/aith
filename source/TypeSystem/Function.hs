module TypeSystem.Function where

import TypeSystem.Meta
import TypeSystem.Methods
import TypeSystem.Type

data Function s σ = Function σ σ

class EmbedFunction σ where
  function :: σ -> σ -> σ

class CheckFunction m p σ where
  checkFunction :: p -> σ -> m (Function s σ)

instance
  ( Monad m,
    Positioned σ p,
    EmbedType κ s,
    EmbedMeta s,
    CheckType s κ m p,
    TypeCheck κ m σ
  ) =>
  TypeCheckImpl m p (Function s σ) κ
  where
  typeCheckImpl _ (Function σ τ) = do
    Type _ <- checkType @s @κ (location σ) =<< typeCheck σ
    Type _ <- checkType @s @κ (location τ) =<< typeCheck τ
    pure $ typex @κ (meta @s)

instance (FreeVariables u σ) => FreeVariables u (Function s σ) where
  freeVariables (Function σ τ) = freeVariables @u σ <> freeVariables @u τ

instance
  ( EmbedFunction σ,
    Substitute u σ
  ) =>
  SubstituteImpl (Function s σ) u σ
  where
  substituteImpl ux x (Function σ τ) = function (substitute ux x σ) (substitute ux x τ)

instance
  ( EmbedFunction σ,
    Reduce σ
  ) =>
  ReduceImpl (Function s σ) σ
  where
  reduceImpl (Function σ τ) = function (reduce σ) (reduce τ)
