module TypeSystem.OfCourse where

import TypeSystem.Meta
import TypeSystem.Methods
import TypeSystem.Type

data OfCourse s σ = OfCourse σ

class EmbedOfCourse σ where
  ofCourse :: σ -> σ

class CheckOfCourse m p σ where
  checkOfCourse :: p -> σ -> m (OfCourse s σ)

instance
  ( Monad m,
    EmbedType κ s,
    CheckType s κ m p,
    EmbedMeta s,
    Positioned σ p,
    TypeCheck κ m σ
  ) =>
  TypeCheckImpl m p (OfCourse s σ) κ
  where
  typeCheckImpl _ (OfCourse σ) = do
    Type _ <- checkType @s @κ (location σ) =<< typeCheck σ
    pure $ typex (meta @s)

instance (FreeVariables u p σ) => FreeVariablesImpl u p (OfCourse s σ) where
  freeVariablesImpl _ (OfCourse σ) = freeVariables @u σ

instance
  ( EmbedOfCourse σ,
    Substitute u σ
  ) =>
  SubstituteImpl (OfCourse s σ) u σ
  where
  substituteImpl ux x (OfCourse σ) = ofCourse (substitute ux x σ)

instance
  ( EmbedOfCourse σ,
    Reduce σ
  ) =>
  ReduceImpl (OfCourse s σ) σ
  where
  reduceImpl (OfCourse σ) = ofCourse (reduce σ)
