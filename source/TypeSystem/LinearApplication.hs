module TypeSystem.LinearApplication where

import Misc.Util (firstM)
import TypeSystem.LinearForall
import TypeSystem.Methods

data LinearApplication ls l' l e = LinearApplication e l

class EmbedLinearApplication l e where
  linearApplication' :: LinearApplication ls l' l e -> e

linearApplication l e = linearApplication' (LinearApplication l e)

instance
  ( Monad m,
    CheckLinearForall m p σ,
    TypeCheckInstantiate ls l m l',
    Substitute l σ,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (LinearApplication ls l l' e) σ lΓ
  where
  typeCheckLinearImpl p (LinearApplication e l') = do
    l <- instantiate @ls @l l'
    (LinearForall x σ, lΓ) <- firstM (checkLinearForall p) =<< typeCheckLinear e
    pure (substitute l x σ, lΓ)

instance (FreeVariables l u, FreeVariables e u) => FreeVariables (LinearApplication ls l' l e) u where
  freeVariables' (LinearApplication l e) = freeVariables @u l <> freeVariables @u e

instance
  ( e ~ e',
    EmbedLinearApplication l e,
    Substitute u l,
    Substitute u e
  ) =>
  SubstituteImpl (LinearApplication ls l' l e) u e'
  where
  substituteImpl ux x (LinearApplication e l) = linearApplication (substitute ux x e) (substitute ux x l)

instance
  ( e ~ e',
    EmbedLinearApplication l e,
    MatchAbstraction e,
    Substitute l e,
    Reduce e
  ) =>
  ReduceImpl (LinearApplication ls l' l e) e'
  where
  reduceImpl (LinearApplication e l) = case matchAbstraction (reduce e) of
    Just (x, e) -> reduce (substitute l x e)
    Nothing -> linearApplication (reduce e) l
