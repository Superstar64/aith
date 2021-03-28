module TypeSystem.Abstraction where

import TypeSystem.Function
import TypeSystem.Linear
import TypeSystem.Methods

data Abstraction l pm' pm e = Abstraction pm e

class EmbedAbstraction pm e where
  abstraction :: pm -> e -> e

instance
  ( Monad m,
    EmbedFunction σ,
    Instantiate pm m pm',
    InternalType pm σ,
    Augment m pm,
    TypeCheck σ m e
  ) =>
  TypeCheckImpl m p (Abstraction l pm pm' e) σ
  where
  typeCheckImpl _ (Abstraction pm' e) = do
    pm <- instantiate @pm pm'
    let σ = internalType pm
    τ <- augment pm (typeCheck e)
    pure (function σ τ)

instance
  ( Monad m,
    EmbedFunction σ,
    EmbedLinear l,
    Instantiate pm m pm',
    InternalType pm σ,
    AugmentLinear m pm l lΓ,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (Abstraction l pm pm' e) σ lΓ
  where
  typeCheckLinearImpl _ (Abstraction pm' e) = do
    pm <- instantiate @pm pm'
    let σ = internalType pm
    (τ, lΓ) <- augmentLinear pm (linear @l) (typeCheckLinear e)
    pure (function σ τ, lΓ)

instance
  ( FreeVariables u p e,
    ModifyVariables u p pm
  ) =>
  FreeVariablesImpl u p (Abstraction l pm' pm e)
  where
  freeVariablesImpl _ (Abstraction pm e) = modifyVariables @u pm $ freeVariables @u e

instance
  ( EmbedAbstraction pm e,
    CaptureAvoidingSubstitution u pm e
  ) =>
  SubstituteImpl (Abstraction l pm' pm e) u e
  where
  substituteImpl ux x (Abstraction pm e) = abstraction (substitute ux x pm') (substituteShadow pm' ux x e')
    where
      (pm', e') = avoidCapture ux (pm, e)

instance
  ( EmbedAbstraction pm e,
    Reduce pm,
    Reduce e
  ) =>
  ReduceImpl (Abstraction l pm' pm e) e
  where
  reduceImpl (Abstraction pm e) = abstraction (reduce pm) (reduce e)
