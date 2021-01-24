module TypeSystem.StageForall where

import TypeSystem.Meta
import TypeSystem.Methods
import TypeSystem.Type

data StageForall s pm' pm σ = StageForall pm σ

class EmbedStageForall pm σ where
  stageForall :: pm -> σ -> σ

class CheckStageForall' s m p σ where
  checkStageForall' :: p -> σ -> m (s -> σ)

instance
  ( Monad m,
    EmbedType κ s,
    EmbedMeta s,
    TypeCheck κ m σ,
    Augment m pm,
    Positioned σ p,
    CheckType s κ m p,
    Instantiate pm m pm'
  ) =>
  TypeCheckImpl m p (StageForall s pm pm' σ) κ
  where
  typeCheckImpl _ (StageForall pm' σ) = do
    pm <- instantiate @pm pm'
    Type _ <- checkType @s (location σ) =<< augment pm (typeCheck @κ σ)
    pure $ typex $ meta @s

instance (ModifyVariables u pm, FreeVariables u σ) => FreeVariables u (StageForall s pm' pm σ) where
  freeVariables (StageForall pm σ) = modifyVariables @u pm $ freeVariables @u σ

instance
  ( EmbedStageForall pm σ,
    CaptureAvoidingSubstitution u pm σ
  ) =>
  SubstituteImpl (StageForall s pm' pm σ) u σ
  where
  substituteImpl ux x (StageForall pm σ) = stageForall (substitute ux x pm') (substituteShadow pm' ux x σ')
    where
      (pm', σ') = avoidCapture ux (pm, σ)

instance
  ( EmbedStageForall pm σ,
    Reduce pm,
    Reduce σ
  ) =>
  ReduceImpl (StageForall s pm' pm σ) σ
  where
  reduceImpl (StageForall pm σ) = stageForall (reduce pm) (reduce σ)
