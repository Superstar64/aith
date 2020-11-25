module TypeSystem.LinearAbstraction where

import Data.Proxy (Proxy (..))
import qualified Data.Set as Set
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same')
import TypeSystem.LinearForall hiding (phonyl)
import TypeSystem.Methods
import TypeSystem.Variable

data LinearAbstraction l e = LinearAbstraction Identifier e

phonyl :: LinearAbstraction l e -> Proxy l
phonyl _ = Proxy

class EmbedLinearAbstraction e where
  linearAbstraction' :: LinearAbstraction l e -> e

linearAbstraction x e = linearAbstraction' (LinearAbstraction x e)

class CheckLinearAbstraction' e where
  checkLinearAbstraction' :: e -> Maybe (Identifier, e)

instance (FreeVariables e u, Same u l) => FreeVariables (LinearAbstraction l e) u where
  freeVariables u f@(LinearAbstraction x e) = case same' u (phonyl f) of
    Just Refl -> Set.delete x $ freeVariables u e
    Nothing -> freeVariables u e

instance (e ~ e', EmbedLinearAbstraction e, EmbedVariable l, FreeVariables u l, Substitute l e, Substitute u e) => SubstituteImpl (LinearAbstraction l e) u e' where
  substituteImpl ux x1 f@(LinearAbstraction x2 e) = linearAbstraction x2' (substitute ux x1 e')
    where
      (x2', e') = avoidCapture (phonyl f) (freeVariables (phonyl f) ux) (x2, e)

instance (Monad m, EmbedLinearForall σ, AugmentEnvironmentWithLinear m p, TypeCheckLinear m e σ lΓ) => TypeCheckLinearImpl m p (LinearAbstraction l e) σ lΓ where
  typeCheckLinearImpl p (LinearAbstraction x e) = do
    (σ, lΓ) <- augmentEnvironmentWithLinear p x (typeCheckLinear e)
    pure (linearForall x σ, lΓ)

instance (e ~ e', EmbedLinearAbstraction e, Reduce e) => ReduceImpl (LinearAbstraction l e') e where
  reduceImpl (LinearAbstraction x e) = linearAbstraction x (reduce e)
