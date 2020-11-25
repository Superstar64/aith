module TypeSystem.TypeApplication where

import Data.Proxy (Proxy (..), asProxyTypeOf)
import Environment
import Misc.Util (firstM)
import TypeSystem.Forall
import TypeSystem.Methods
import TypeSystem.TypeAbstraction hiding (phonyκ)

data TypeApplication κ σ e = TypeApplication e σ deriving (Show, Functor, Foldable, Traversable)

phonyκ :: TypeApplication κ σ e -> Proxy κ
phonyκ _ = Proxy

class EmbedTypeApplication σ e where
  typeApplication' :: TypeApplication κ σ e -> e

typeApplication e σ = typeApplication' (TypeApplication e σ)

instance
  ( Monad m,
    CheckForall m p κ σ,
    Positioned e p,
    Usage lΓ,
    SubstituteSame σ,
    Instantiate m σ' σ,
    SameType m p κ,
    TypeCheckLinear m e σ lΓ,
    TypeCheck m σ' κ
  ) =>
  TypeCheckLinearImpl m p (TypeApplication κ σ' e) σ lΓ
  where
  typeCheckLinearImpl p f@(TypeApplication e σ2) = do
    (Forall x κ1 σ1, lΓ) <- firstM (checkForall $ location e) =<< typeCheckLinear e
    κ2 <- typeCheck σ2
    sameType p κ1 (flip asProxyTypeOf (phonyκ f) $ κ2)
    σ2' <- instantiate σ2
    pure (substituteSame σ2' x σ1, lΓ)

instance (FreeVariables σ u, FreeVariables e u) => FreeVariables (TypeApplication κ σ e) u where
  freeVariables u (TypeApplication e σ) = freeVariables u e <> freeVariables u σ

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
    CheckTypeAbstraction' e,
    Substitute σ e,
    Reduce e
  ) =>
  ReduceImpl (TypeApplication κ σ e') e
  where
  reduceImpl (TypeApplication e1 σ) = case checkTypeAbstraction' (reduce e1) of
    Just (x, e) -> reduce $ substitute σ x e
    Nothing -> typeApplication (reduce e1) σ
