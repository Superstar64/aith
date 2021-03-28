module TypeSystem.Forall where

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
    Augment m pm,
    Instantiate pm m pm',
    TypeCheck κ m σ
  ) =>
  TypeCheckImpl m p (Forall s pm pm' σ) κ
  where
  typeCheckImpl _ (Forall pm' σ) = do
    pm <- instantiate @pm pm'
    Type s <- checkType @s (location σ) =<< augment pm (typeCheck @κ σ)
    pure $ typex @κ s

instance
  ( FreeVariables u p σ,
    ModifyVariables u p pm
  ) =>
  FreeVariablesImpl u p (Forall s pm' pm σ)
  where
  freeVariablesImpl _ (Forall pm σ) = modifyVariables @u pm $ freeVariables @u σ

instance
  ( EmbedForall pm σ,
    CaptureAvoidingSubstitution u pm σ
  ) =>
  SubstituteImpl (Forall s pm' pm σ) u σ
  where
  substituteImpl ux x (Forall pm σ) = forallx (substitute ux x pm') (substituteShadow pm' ux x σ')
    where
      (pm', σ') = avoidCapture ux (pm, σ)

instance
  ( EmbedForall pm σ,
    Reduce pm,
    Reduce σ
  ) =>
  ReduceImpl (Forall s pm' pm σ) σ
  where
  reduceImpl (Forall pm σ) = forallx (reduce pm) (reduce σ)
