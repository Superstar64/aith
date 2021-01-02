module TypeSystem.Bind where

import Data.Type.Equality ((:~:) (..))
import Environment
import Misc.Util (Same, same)
import TypeSystem.Linear
import TypeSystem.Methods

data Bind l pm' pm e = Bind pm e e deriving (Show, Functor, Foldable, Traversable)

class EmbedBind pm e where
  bind :: pm -> e -> e -> e

instance
  ( Monad m,
    EmbedLinear l,
    Positioned e p,
    SameType m p σ,
    TypeCheckInstantiate σ pm m pm',
    Usage lΓ,
    AugmentEnvironmentPattern m pm p l σ lΓ,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (Bind l pm pm' e) σ lΓ
  where
  typeCheckLinearImpl p (Bind pm' e1 e2) = do
    (τ', pm) <- typeCheckInstantiate @σ @pm pm'
    (τ, lΓ1) <- typeCheckLinear e1
    sameType p τ τ'
    (σ, lΓ2) <- augmentEnvironmentPattern pm (linear @l) p (typeCheckLinear e2)
    pure (σ, combine lΓ1 lΓ2)

instance
  ( Same e u,
    FreeVariables pm u,
    RemoveBindings pm,
    FreeVariables e u
  ) =>
  FreeVariables (Bind l pm' pm e) u
  where
  freeVariables' (Bind pm e1 e2) = case same @e @u of
    Just Refl -> freeVariables @u e1 <> removeBindings pm (freeVariables @u e2)
    Nothing -> freeVariables @u pm <> freeVariables @u e1 <> freeVariables @u e2

instance
  ( e ~ e',
    EmbedBind pm e,
    AvoidCapturePattern u pm e,
    Substitute u pm,
    Substitute u e
  ) =>
  SubstituteImpl (Bind l pm' pm e) u e'
  where
  substituteImpl ux x (Bind pm e1 e2) = bind (substitute ux x pm') (substitute ux x e1) (substitute ux x e2')
    where
      (pm', e2') = avoidCapturePattern ux (pm, e2)

instance (e ~ e', ReducePattern pm e, Reduce e) => ReduceImpl (Bind l pm' pm e) e' where
  reduceImpl (Bind pm e1 e2) = reducePattern pm (reduce e1) (reduce e2)
