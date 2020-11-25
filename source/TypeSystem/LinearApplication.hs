module TypeSystem.LinearApplication where

import Misc.Util (firstM)
import TypeSystem.LinearAbstraction
import TypeSystem.LinearForall
import TypeSystem.Methods

data LinearApplication l e = LinearApplication e l

class EmbedLinearApplication l e where
  linearApplication' :: LinearApplication l e -> e

linearApplication l e = linearApplication' (LinearApplication l e)

instance (FreeVariables l u, FreeVariables e u) => FreeVariables (LinearApplication l e) u where
  freeVariables u (LinearApplication l e) = freeVariables u l <> freeVariables u e

instance (Monad m, CheckLinearForall m p σ, Substitute l σ, TypeCheckLinear m e σ lΓ) => TypeCheckLinearImpl m p (LinearApplication l e) σ lΓ where
  typeCheckLinearImpl p (LinearApplication e l) = do
    (LinearForall x σ, lΓ) <- firstM (checkLinearForall p) =<< typeCheckLinear e
    pure (substitute l x σ, lΓ)

instance (e ~ e', EmbedLinearApplication l e, Substitute u l, Substitute u e) => SubstituteImpl (LinearApplication l e) u e' where
  substituteImpl ux x (LinearApplication e l) = linearApplication (substitute ux x e) (substitute ux x l)

instance (e ~ e', EmbedLinearApplication l e, CheckLinearAbstraction' e, Substitute l e, Reduce e) => ReduceImpl (LinearApplication l e) e' where
  reduceImpl (LinearApplication e l) = case checkLinearAbstraction' (reduce e) of
    Just (x, e) -> reduce (substitute l x e)
    Nothing -> linearApplication (reduce e) l
