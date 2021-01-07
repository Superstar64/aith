module TypeSystem.Forall where

import Data.Type.Equality ((:~:) (..))
import Misc.Util (Same, same)
import TypeSystem.Methods
import TypeSystem.Type

data Forall s pm' pm σ = Forall pm σ

class EmbedForall pm σ where
  forallx :: pm -> σ -> σ

class CheckForall' m p κ σ where
  checkForall' :: p -> σ -> m (κ, σ -> σ)

instance
  ( Monad m,
    Positioned σ p,
    EmbedType κ s,
    CheckType s κ m p,
    AugmentEnvironmentPattern m pm,
    Instantiate pm m pm',
    TypeCheck κ m σ
  ) =>
  TypeCheckImpl m p (Forall s pm pm' σ) κ
  where
  typeCheckImpl _ (Forall pm' σ) = do
    pm <- instantiate @pm pm'
    Type s <- checkType @s (location σ) =<< augmentEnvironmentPattern pm (typeCheck @κ σ)
    pure $ typex @κ s

instance
  ( FreeVariables σ u,
    FreeVariables pm u,
    RemoveBindings pm,
    Same u σ
  ) =>
  FreeVariables (Forall s pm' pm σ) u
  where
  freeVariables' (Forall pm σ) = case same @u @σ of
    Just Refl -> removeBindings pm (freeVariables @u σ)
    Nothing -> freeVariables @u pm <> freeVariables @u σ

instance
  ( σ ~ σ',
    EmbedForall pm σ,
    Substitute u σ,
    Substitute u pm,
    AvoidCapturePattern u pm σ
  ) =>
  SubstituteImpl (Forall s pm' pm σ') u σ
  where
  substituteImpl ux x (Forall pm σ) = forallx (substitute ux x pm') (substitute ux x σ')
    where
      (pm', σ') = avoidCapturePattern ux (pm, σ)

instance
  ( σ ~ σ',
    EmbedForall pm σ,
    Reduce pm,
    Reduce σ
  ) =>
  ReduceImpl (Forall s pm' pm σ) σ'
  where
  reduceImpl (Forall pm σ) = forallx (reduce pm) (reduce σ)
