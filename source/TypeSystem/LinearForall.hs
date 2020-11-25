module TypeSystem.LinearForall where

import Data.Proxy (Proxy (..), asProxyTypeOf)
import Data.Set as Set (delete)
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same')
import TypeSystem.Linear
import TypeSystem.Methods
import TypeSystem.Type
import TypeSystem.Variable

data LinearForall l s σ = LinearForall Identifier σ deriving (Show, Functor, Foldable, Traversable)

phonyl :: LinearForall l s σ -> Proxy l
phonyl _ = Proxy

phonys :: LinearForall l s σ -> Proxy s
phonys _ = Proxy

class EmbedLinearForall σ where
  linearForall' :: LinearForall l s σ -> σ

linearForall x σ = linearForall' (LinearForall x σ)

class CheckLinearForall m p σ where
  checkLinearForall :: p -> σ -> m (LinearForall l s σ)

instance (Monad m, EmbedType l s κ, EmbedLinear l, SubstituteSame l, Positioned σ p, AugmentEnvironmentWithLinear m p, CheckType m p κ l s, TypeCheck m σ κ) => TypeCheckImpl m p (LinearForall l s σ) κ where
  typeCheckImpl p f@(LinearForall x σ) = do
    (z, Type l s) <- checkType' (phonyl f) (phonys f) (location σ) =<< augmentEnvironmentWithLinear p x (typeCheck σ)
    pure $ flip asProxyTypeOf z $ typex (substituteSame linear x l) s

instance (Same u l, FreeVariables σ u) => FreeVariables (LinearForall l s σ) u where
  freeVariables u f@(LinearForall x σ) = case same' u (phonyl f) of
    Just Refl -> Set.delete x $ freeVariables u σ
    Nothing -> freeVariables u σ

instance
  ( σ ~ σ',
    EmbedLinearForall σ,
    EmbedVariable l,
    FreeVariables u l,
    Substitute l σ,
    Substitute u σ
  ) =>
  SubstituteImpl (LinearForall l s σ') u σ
  where
  substituteImpl ux x1 f@(LinearForall x2 σ) = linearForall x2' (substitute ux x1 σ')
    where
      (x2', σ') = avoidCapture (phonyl f) (freeVariables (phonyl f) ux) (x2, σ)
