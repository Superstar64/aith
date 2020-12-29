module TypeSystem.TypeAbstraction where

import Data.Set as Set (delete)
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same)
import TypeSystem.Forall
import TypeSystem.Methods
import TypeSystem.Variable

data TypeAbstraction κs κ' σ κ e = TypeAbstraction Identifier κ e deriving (Show, Functor, Foldable, Traversable)

class EmbedTypeAbstraction κ e where
  typeAbstraction :: Identifier -> κ -> e -> e

instance
  ( Monad m,
    EmbedForall κ σ,
    AugmentEnvironment m p κ,
    TypeCheckInstantiate κs κ m κ',
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (TypeAbstraction κs κ σ' κ' e) σ lΓ
  where
  typeCheckLinearImpl p (TypeAbstraction x κ' e) = do
    κ <- instantiate @κs @κ κ'
    (σ, lΓ) <- augmentEnvironment p x κ (typeCheckLinear e)
    pure (forallx x κ σ, lΓ)

instance (FreeVariables κ u, FreeVariables e u, Same u σ) => FreeVariables (TypeAbstraction κs κ' σ κ e) u where
  freeVariables' (TypeAbstraction x κ e) = case same @u @σ of
    Just Refl -> Set.delete x $ freeVariables @u e
    Nothing -> freeVariables @u κ <> freeVariables @u e

instance
  ( e ~ e',
    EmbedTypeAbstraction κ e,
    EmbedVariable σ,
    FreeVariables u σ,
    Substitute σ e,
    Substitute u e,
    Substitute u κ
  ) =>
  SubstituteImpl (TypeAbstraction κs κ' σ κ e') u e
  where
  substituteImpl ux x1 (TypeAbstraction x2 κ e) = typeAbstraction x2' (substitute ux x1 κ) (substitute ux x1 e')
    where
      (x2', e') = avoidCapture @σ (freeVariables @σ ux) (x2, e)

instance (e ~ e', EmbedTypeAbstraction κ e, Reduce e) => ReduceImpl (TypeAbstraction κs κ' σ κ e') e where
  reduceImpl (TypeAbstraction x κ e) = typeAbstraction x κ $ reduce e
