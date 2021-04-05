module TypeSystem.Extern where

import Environment
import Misc.Symbol
import TypeSystem.Methods
import TypeSystem.Runtime
import TypeSystem.Type

data Extern κ s ρ σ = Extern Symbol σ

class EmbedExtern σ e where
  extern :: Symbol -> σ -> e

instance
  ( Monad m,
    Usage lΓ,
    TypeCheckInstantiate κ σ m σ',
    CheckType s κ m p,
    CheckRuntime s ρ m p
  ) =>
  TypeCheckLinearImpl m p (Extern κ s ρ σ') σ lΓ
  where
  typeCheckLinearImpl p (Extern _ σ') = do
    (κ, σ) <- typeCheckInstantiate @κ σ'
    Type s <- checkType @s p κ
    Runtime _ <- checkRuntime @s @ρ p s
    pure (σ, useNothing)

instance
  ( Semigroup p,
    FreeVariables u p σ
  ) =>
  FreeVariablesImpl u p (Extern κ s ρ σ)
  where
  freeVariablesImpl _ (Extern _ σ) = freeVariables @u σ

instance
  ( Substitute u σ,
    EmbedExtern σ e
  ) =>
  SubstituteImpl (Extern κ s ρ σ) u e
  where
  substituteImpl ux x (Extern sm σ) = extern sm (substitute ux x σ)

instance
  ( Reduce σ,
    EmbedExtern σ e
  ) =>
  ReduceImpl (Extern κ s ρ σ) e
  where
  reduceImpl (Extern sm σ) = extern sm (reduce σ)
