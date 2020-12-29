module TypeSystem.OfCourse where

import TypeSystem.Methods
import TypeSystem.StageOfCourse
import TypeSystem.Type

data OfCourse s σ = OfCourse σ deriving (Show, Functor, Foldable, Traversable)

class EmbedOfCourse σ where
  ofCourse :: σ -> σ

class CheckOfCourse m p σ where
  checkOfCourse :: p -> σ -> m (OfCourse s σ)

instance
  ( Monad m,
    EmbedType s κ,
    CheckType m p κ s,
    EmbedStageOfCourse s,
    Positioned σ p,
    TypeCheck κ m σ
  ) =>
  TypeCheckImpl m p (OfCourse s σ) κ
  where
  typeCheckImpl _ (OfCourse σ) = do
    Type s <- checkType @s @κ (location σ) =<< typeCheck σ
    pure $ typex (stageOfCourse s)

instance (FreeVariables σ u) => FreeVariables (OfCourse s σ) u where
  freeVariables' (OfCourse σ) = freeVariables @u σ

instance
  ( σ ~ σ',
    EmbedOfCourse σ,
    Substitute u σ
  ) =>
  SubstituteImpl (OfCourse s σ) u σ'
  where
  substituteImpl ux x (OfCourse σ) = ofCourse (substitute ux x σ)
