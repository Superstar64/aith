module TypeSystem.LinearAbstraction where

import qualified Data.Set as Set
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same)
import TypeSystem.LinearForall
import TypeSystem.Linearity
import TypeSystem.Methods
import TypeSystem.Variable

data LinearAbstraction ls l e = LinearAbstraction Identifier e

class EmbedLinearAbstraction e where
  linearAbstraction' :: LinearAbstraction ls l e -> e

linearAbstraction x e = linearAbstraction' (LinearAbstraction x e)

instance
  ( Monad m,
    EmbedLinearForall σ,
    EmbedLinearity ls,
    AugmentEnvironment m p ls,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (LinearAbstraction ls l e) σ lΓ
  where
  typeCheckLinearImpl p (LinearAbstraction x e) = do
    (σ, lΓ) <- augmentEnvironment p x (linearity @ls) (typeCheckLinear e)
    pure (linearForall x σ, lΓ)

instance (FreeVariables e u, Same u l) => FreeVariables (LinearAbstraction ls l e) u where
  freeVariables' (LinearAbstraction x e) = case same @u @l of
    Just Refl -> Set.delete x $ freeVariables @u e
    Nothing -> freeVariables @u e

instance
  ( e ~ e',
    EmbedLinearAbstraction e,
    EmbedVariable l,
    FreeVariables u l,
    Substitute l e,
    Substitute u e
  ) =>
  SubstituteImpl (LinearAbstraction ls l e) u e'
  where
  substituteImpl ux x1 (LinearAbstraction x2 e) = linearAbstraction x2' (substitute ux x1 e')
    where
      (x2', e') = avoidCapture @l (freeVariables @l ux) (x2, e)

instance (e ~ e', EmbedLinearAbstraction e, Reduce e) => ReduceImpl (LinearAbstraction ls l e') e where
  reduceImpl (LinearAbstraction x e) = linearAbstraction x (reduce e)
