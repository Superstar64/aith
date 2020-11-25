module TypeSystem.TypeAbstraction where

import Data.Proxy (Proxy (..))
import Data.Set as Set (delete)
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same')
import TypeSystem.Forall
import TypeSystem.Methods
import TypeSystem.Variable

data TypeAbstraction σ κ κ' e = TypeAbstraction Identifier κ' e deriving (Show, Functor, Foldable, Traversable)

phonyσ :: TypeAbstraction σ κ κ' e -> Proxy σ
phonyσ _ = Proxy

phonyκ :: TypeAbstraction σ κ κ' e -> Proxy κ
phonyκ _ = Proxy

class EmbedTypeAbstraction κ' e where
  typeAbstraction' :: TypeAbstraction σ κ κ' e -> e

typeAbstraction x κ e = typeAbstraction' (TypeAbstraction x κ e)

class CheckTypeAbstraction' e where
  checkTypeAbstraction' :: e -> Maybe (Identifier, e)

instance
  ( Monad m,
    EmbedForall κ σ,
    Instantiate m κ' κ,
    AugmentEnvironment m p κ,
    TypeCheckLinear m e σ lΓ
  ) =>
  TypeCheckLinearImpl m p (TypeAbstraction σ' κ κ' e) σ lΓ
  where
  typeCheckLinearImpl p f@(TypeAbstraction x κ' e) = do
    κ <- instantiate' (phonyκ f) κ'
    (σ, lΓ) <- augmentEnvironment p x κ (typeCheckLinear e)
    pure (forallx x κ σ, lΓ)

instance (FreeVariables κ' u, FreeVariables e u, Same u σ) => FreeVariables (TypeAbstraction σ κ κ' e) u where
  freeVariables u f@(TypeAbstraction x κ e) = case same' u (phonyσ f) of
    Just Refl -> Set.delete x $ freeVariables u e
    Nothing -> freeVariables u κ <> freeVariables u e

instance
  ( e ~ e',
    EmbedTypeAbstraction κ' e,
    EmbedVariable σ,
    FreeVariables u σ,
    Substitute σ e,
    Substitute u e,
    Substitute u κ'
  ) =>
  SubstituteImpl (TypeAbstraction σ κ κ' e') u e
  where
  substituteImpl ux x1 f@(TypeAbstraction x2 κ e) = typeAbstraction x2' (substitute ux x1 κ) (substitute ux x1 e')
    where
      (x2', e') = avoidCapture (phonyσ f) (freeVariables (phonyσ f) ux) (x2, e)

instance (e ~ e', EmbedTypeAbstraction κ' e, Reduce e) => ReduceImpl (TypeAbstraction σ κ κ' e') e where
  reduceImpl (TypeAbstraction x κ e) = typeAbstraction x κ $ reduce e
