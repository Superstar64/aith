module TypeSystem.Abstraction where

import Data.Type.Equality ((:~:) (..))
import Misc.Util (Same, same)
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
    AugmentEnvironmentPattern m pm,
    TypeCheck σ m e
  ) =>
  TypeCheckImpl m p (Abstraction l pm pm' e) σ
  where
  typeCheckImpl _ (Abstraction pm' e) = do
    pm <- instantiate @pm pm'
    let σ = internalType pm
    τ <- augmentEnvironmentPattern pm (typeCheck e)
    pure (function σ τ)

instance
  ( Monad m,
    EmbedFunction σ,
    EmbedLinear l,
    Instantiate pm m pm',
    InternalType pm σ,
    AugmentEnvironmentPatternLinear m pm l lΓ,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (Abstraction l pm pm' e) σ lΓ
  where
  typeCheckLinearImpl _ (Abstraction pm' e) = do
    pm <- instantiate @pm pm'
    let σ = internalType pm
    (τ, lΓ) <- augmentEnvironmentPatternLinear pm (linear @l) (typeCheckLinear e)
    pure (function σ τ, lΓ)

instance
  ( Same u e,
    FreeVariables e u,
    FreeVariables pm u,
    RemoveBindings pm
  ) =>
  FreeVariables (Abstraction l pm' pm e) u
  where
  freeVariables' (Abstraction pm e) = case same @u @e of
    Just Refl -> removeBindings pm $ freeVariables @u e
    Nothing -> freeVariables @u pm <> freeVariables @u e

instance
  ( e ~ e',
    EmbedAbstraction pm e,
    AvoidCapturePattern u pm e,
    Substitute u e,
    Substitute u pm
  ) =>
  SubstituteImpl (Abstraction l pm' pm e') u e
  where
  substituteImpl ux x (Abstraction pm e) = abstraction (substitute ux x pm') (substitute ux x e')
    where
      (pm', e') = avoidCapturePattern ux (pm, e)

instance
  ( e ~ e',
    EmbedAbstraction pm e,
    Reduce pm,
    Reduce e
  ) =>
  ReduceImpl (Abstraction l pm' pm e') e
  where
  reduceImpl (Abstraction pm e) = abstraction (reduce pm) (reduce e)
