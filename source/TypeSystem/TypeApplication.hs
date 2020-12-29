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
    CheckForall m p κ σ,
    Positioned e p,
    Usage lΓ,
    SubstituteSame σ,
    SameType m p κ,
    TypeCheckLinear σ m e lΓ,
    TypeCheckInstantiate κ σ m σ'
  ) =>
  TypeCheckLinearImpl m p (TypeApplication κ σ' e) σ lΓ
  where
  typeCheckLinearImpl p (TypeApplication e σ2') = do
    (Forall x κ1 σ1, lΓ) <- firstM (checkForall $ location e) =<< typeCheckLinear e
    (κ2, σ2) <- typeCheckInstantiate @κ σ2'
    sameType p κ1 κ2
    pure (substituteSame σ2 x σ1, lΓ)

instance (FreeVariables σ u, FreeVariables e u) => FreeVariables (TypeApplication κ σ e) u where
  freeVariables' (TypeApplication e σ) = freeVariables @u e <> freeVariables @u σ

instance
  ( e ~ e',
    EmbedTypeApplication σ e,
    Substitute u e,
    Substitute u σ
  ) =>
  SubstituteImpl (TypeApplication κ σ e') u e
  where
  substituteImpl ux x (TypeApplication e σ) = typeApplication (substitute ux x e) (substitute ux x σ)

instance
  ( e ~ e',
    EmbedTypeApplication σ e,
    MatchAbstraction e,
    Substitute σ e,
    Reduce e
  ) =>
  ReduceImpl (TypeApplication κ σ e') e
  where
  reduceImpl (TypeApplication e1 σ) = case matchAbstraction (reduce e1) of
    Just (x, e) -> reduce $ substitute σ x e
    Nothing -> typeApplication (reduce e1) σ
