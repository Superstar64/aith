module TypeSystem.StageApplication where

import Misc.Util (firstM)
import TypeSystem.Methods
import TypeSystem.StageForall

data StageApplication μ s' s e = StageApplication e s

class EmbedStageApplication s e where
  stageApplication :: e -> s -> e

instance
  ( Monad m,
    Positioned e p,
    SameType m p μ,
    TypeCheckInstantiate μ s m s',
    TypeCheckLinear σ m e lΓ,
    CheckStageForall' μ s m p σ
  ) =>
  TypeCheckLinearImpl m p (StageApplication μ s s' e) σ lΓ
  where
  typeCheckLinearImpl p (StageApplication e s') = do
    ((μ, f), lΓ) <- firstM (checkStageForall' $ location e) =<< typeCheckLinear e
    (μ', s) <- typeCheckInstantiate @μ @s s'
    sameType p μ μ'
    pure $ (f s, lΓ)

instance (FreeVariables u s, FreeVariables u e) => FreeVariables u (StageApplication μ s' s e) where
  freeVariables (StageApplication e s) = freeVariables @u e <> freeVariables @u s

instance
  ( EmbedStageApplication s e,
    Substitute u s,
    Substitute u e
  ) =>
  SubstituteImpl (StageApplication μ s' s e) u e
  where
  substituteImpl ux x (StageApplication e s) = stageApplication (substitute ux x e) (substitute ux x s)

instance
  ( EmbedStageApplication s e,
    ReduceMatchAbstraction s e,
    Reduce s,
    Reduce e
  ) =>
  ReduceImpl (StageApplication μ s' s e) e
  where
  reduceImpl (StageApplication e s) = case reduceMatchAbstraction (reduce e) of
    Just f -> f (reduce s)
    Nothing -> stageApplication (reduce e) (reduce s)
