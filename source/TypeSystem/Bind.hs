module TypeSystem.Bind where

import Environment
import TypeSystem.Linear
import TypeSystem.Methods

data Bind l pm' pm e = Bind pm e e

class EmbedBind pm e where
  bind :: pm -> e -> e -> e

instance
  ( Monad m,
    EmbedLinear l,
    Positioned e p,
    SameType m p σ,
    Instantiate pm m pm',
    InternalType pm σ,
    Usage lΓ,
    AugmentLinear m pm l lΓ,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (Bind l pm pm' e) σ lΓ
  where
  typeCheckLinearImpl p (Bind pm' e1 e2) = do
    pm <- instantiate @pm pm'
    let τ' = internalType pm :: σ
    (τ, lΓ1) <- typeCheckLinear e1
    sameType p τ τ'
    (σ, lΓ2) <- augmentLinear pm (linear @l) (typeCheckLinear e2)
    pure (σ, combine lΓ1 lΓ2)

instance
  ( FreeVariables pm u,
    ModifyVariables u pm,
    FreeVariables e u
  ) =>
  FreeVariables (Bind l pm' pm e) u
  where
  freeVariables' (Bind pm e1 e2) = freeVariables @u e1 <> modifyVariables @u pm (freeVariables @u e2)

instance
  ( EmbedBind pm e,
    AvoidCapture u pm e,
    Substitute u pm,
    Substitute u e
  ) =>
  SubstituteImpl (Bind l pm' pm e) u e
  where
  substituteImpl ux x (Bind pm e1 e2) = bind (substitute ux x pm') (substitute ux x e1) (substitute ux x e2')
    where
      (pm', e2') = avoidCapture ux (pm, e2)

instance
  ( ReducePattern pm e,
    Reduce pm,
    Reduce e
  ) =>
  ReduceImpl (Bind l pm' pm e) e
  where
  reduceImpl (Bind pm e1 e2) = reducePattern (reduce pm) (reduce e1) (reduce e2)
