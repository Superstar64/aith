module TypeSystem.TypeApplication where

import Environment
import Misc.Util (firstM)
import TypeSystem.Forall
import TypeSystem.Methods

data TypeApplication κ σ e = TypeApplication e σ deriving (Show, Functor, Foldable, Traversable)

class EmbedTypeApplication σ e where
  typeApplication :: e -> σ -> e

instance
  ( Monad m,
    CheckForall' m p κ σ,
    Positioned e p,
    Usage lΓ,
    SameType m p κ,
    TypeCheckLinear σ m e lΓ,
    TypeCheckInstantiate κ σ m σ'
  ) =>
  TypeCheckLinearImpl m p (TypeApplication κ σ' e) σ lΓ
  where
  typeCheckLinearImpl p (TypeApplication e σ') = do
    ((κ, f), lΓ) <- firstM (checkForall' $ location e) =<< typeCheckLinear e
    (κ', σ) <- typeCheckInstantiate @κ σ'
    sameType p κ κ'
    pure (f σ, lΓ)

instance (FreeVariables σ u, FreeVariables e u) => FreeVariables (TypeApplication κ σ e) u where
  freeVariables' (TypeApplication e σ) = freeVariables @u e <> freeVariables @u σ

instance
  ( EmbedTypeApplication σ e,
    Substitute u e,
    Substitute u σ
  ) =>
  SubstituteImpl (TypeApplication κ σ e) u e
  where
  substituteImpl ux x (TypeApplication e σ) = typeApplication (substitute ux x e) (substitute ux x σ)

instance
  ( EmbedTypeApplication σ e,
    ReduceMatchAbstraction σ e,
    Substitute σ e,
    Reduce σ,
    Reduce e
  ) =>
  ReduceImpl (TypeApplication κ σ e) e
  where
  reduceImpl (TypeApplication e1 σ) = case reduceMatchAbstraction (reduce e1) of
    Just f -> f (reduce σ)
    Nothing -> typeApplication (reduce e1) (reduce σ)
