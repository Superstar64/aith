module TypeSystem.TypeAbstraction where

import Data.Type.Equality ((:~:) (..))
import Misc.Util (Same, same)
import TypeSystem.Forall
import TypeSystem.Methods

data TypeAbstraction σ pm'' pm' pm e = TypeAbstraction pm e deriving (Show, Functor, Foldable, Traversable)

class EmbedTypeAbstraction pm e where
  typeAbstraction :: pm -> e -> e

instance
  ( Monad m,
    EmbedForall pm σ,
    Instantiate pm' m pm'',
    AugmentEnvironmentPattern m pm',
    Strip pm' pm,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (TypeAbstraction σ' pm pm' pm'' e) σ lΓ
  where
  typeCheckLinearImpl _ (TypeAbstraction pm'' e) = do
    pm' <- instantiate @pm' pm''
    (σ, lΓ) <- augmentEnvironmentPattern pm' (typeCheckLinear e)
    let pm = strip pm' :: pm
    pure (forallx pm σ, lΓ)

instance
  ( FreeVariables e u,
    Same u σ,
    FreeVariables pm u,
    RemoveBindings pm
  ) =>
  FreeVariables (TypeAbstraction σ pm'' pm' pm e) u
  where
  freeVariables' (TypeAbstraction pm e) = case same @u @σ of
    Just Refl -> removeBindings pm $ freeVariables @u e
    Nothing -> freeVariables @u pm <> freeVariables @u e

instance
  ( e ~ e',
    EmbedTypeAbstraction pm e,
    Substitute u e,
    Substitute u pm,
    AvoidCapturePattern u pm e
  ) =>
  SubstituteImpl (TypeAbstraction σ pm'' pm' pm e') u e
  where
  substituteImpl ux x (TypeAbstraction pm e) = typeAbstraction (substitute ux x pm') (substitute ux x e')
    where
      (pm', e') = avoidCapturePattern ux (pm, e)

instance
  ( e ~ e',
    EmbedTypeAbstraction pm e,
    Reduce pm,
    Reduce e
  ) =>
  ReduceImpl (TypeAbstraction σ pm'' pm' pm e') e
  where
  reduceImpl (TypeAbstraction pm e) = typeAbstraction (reduce pm) (reduce e)
