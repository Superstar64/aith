module TypeSystem.StageAbstraction where

import TypeSystem.Methods
import TypeSystem.StageForall

data StageAbstraction pm'' pm' pm e = StageAbstraction pm e

class EmbedStageAbstraction pm e where
  stageAbstraction :: pm -> e -> e

instance
  ( Monad m,
    EmbedStageForall pm σ,
    Strip pm' pm,
    TypeCheckLinear σ m e lΓ,
    Augment m pm',
    Instantiate pm' m pm''
  ) =>
  TypeCheckLinearImpl m p (StageAbstraction pm pm' pm'' e) σ lΓ
  where
  typeCheckLinearImpl _ (StageAbstraction pm'' e) = do
    pm' <- instantiate @pm' pm''
    (σ, lΓ) <- augment pm' (typeCheckLinear e)
    let pm = strip pm' :: pm
    pure (stageForall pm σ, lΓ)

instance (ModifyVariables u p pm, FreeVariables u p e) => FreeVariablesImpl u p (StageAbstraction pm'' pm' pm e) where
  freeVariablesImpl _ (StageAbstraction pm e) = modifyVariables @u pm (freeVariables @u e)

instance
  ( EmbedStageAbstraction pm e,
    CaptureAvoidingSubstitution u pm e
  ) =>
  SubstituteImpl (StageAbstraction pm'' pm' pm e) u e
  where
  substituteImpl ux x (StageAbstraction pm e) = stageAbstraction (substitute ux x pm') (substituteShadow pm' ux x e')
    where
      (pm', e') = avoidCapture ux (pm, e)

instance (EmbedStageAbstraction pm e, Reduce pm, Reduce e) => ReduceImpl (StageAbstraction pm'' pm' pm e) e where
  reduceImpl (StageAbstraction pm e) = stageAbstraction (reduce pm) (reduce e)
