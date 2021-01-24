module TypeSystem.StageApplication where

import Misc.Util (firstM)
import TypeSystem.Methods
import TypeSystem.StageForall

data StageApplication s' s e = StageApplication e s

class EmbedStageApplication s e where
  stageApplication :: e -> s -> e

instance
  ( Monad m,
    CheckStageForall' s m p σ,
    Positioned e p,
    Instantiate s m s',
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (StageApplication s s' e) σ lΓ
  where
  typeCheckLinearImpl _ (StageApplication e s') = do
    (f, lΓ) <- firstM (checkStageForall' $ location e) =<< typeCheckLinear e
    s <- instantiate @s s'
    pure $ (f s, lΓ)

instance (FreeVariables u s, FreeVariables u e) => FreeVariables u (StageApplication s' s e) where
  freeVariables (StageApplication e s) = freeVariables @u e <> freeVariables @u s

instance
  ( EmbedStageApplication s e,
    Substitute u s,
    Substitute u e
  ) =>
  SubstituteImpl (StageApplication s' s e) u e
  where
  substituteImpl ux x (StageApplication e s) = stageApplication (substitute ux x e) (substitute ux x s)

instance
  ( EmbedStageApplication s e,
    ReduceMatchAbstraction s e,
    Reduce s,
    Reduce e
  ) =>
  ReduceImpl (StageApplication s' s e) e
  where
  reduceImpl (StageApplication e s) = case reduceMatchAbstraction (reduce e) of
    Just f -> f (reduce s)
    Nothing -> stageApplication (reduce e) (reduce s)
