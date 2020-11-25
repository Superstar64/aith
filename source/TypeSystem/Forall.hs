module TypeSystem.Forall where

import Data.Proxy (Proxy (..), asProxyTypeOf)
import Data.Set as Set (delete)
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, proxyOf, same')
import TypeSystem.Methods
import TypeSystem.Type
import TypeSystem.Variable

data Forall l s κ σ = Forall Identifier κ σ deriving (Show, Functor, Foldable, Traversable)

phonyl :: Forall l s κ σ -> Proxy l
phonyl _ = Proxy

phonys :: Forall l s κ σ -> Proxy s
phonys _ = Proxy

class EmbedForall κ σ where
  forallx' :: Forall l s κ σ -> σ

forallx x κ σ = forallx' (Forall x κ σ)

class CheckForall m p κ σ where
  checkForall :: p -> σ -> m (Forall l s κ σ)

instance (FreeVariables σ u, FreeVariables κ u, Same u σ) => FreeVariables (Forall l s κ σ) u where
  freeVariables u (Forall x κ σ) = case same' u (proxyOf σ) of
    Just Refl -> Set.delete x (freeVariables u σ)
    Nothing -> freeVariables u κ <> freeVariables u σ

instance (σ ~ σ', EmbedVariable σ, EmbedForall κ σ, Substitute u σ, Substitute u κ, Substitute σ σ', FreeVariables u σ) => SubstituteImpl (Forall l s κ σ') u σ where
  substituteImpl ux x1 (Forall x2 κ σ) = forallx x2' (substitute ux x1 κ) (substitute ux x1 σ')
    where
      (x2', σ') = avoidCapture (proxyOf σ) (freeVariables (proxyOf σ) ux) (x2, σ)

instance
  ( Monad m,
    Instantiate m κ' κ,
    Positioned σ p,
    AugmentEnvironment m p κ,
    EmbedType l s κ,
    CheckType m p κ l s,
    TypeCheck m σ κ
  ) =>
  TypeCheckImpl m p (Forall l s κ' σ) κ
  where
  typeCheckImpl p f@(Forall x κ1' σ) = do
    κ1 <- instantiate κ1'
    (z, Type l s) <- checkType' (phonyl f) (phonys f) (location σ) =<< augmentEnvironment p x κ1 (typeCheck σ)
    pure $ flip asProxyTypeOf (proxyOf κ1) $ flip asProxyTypeOf z $ typex l s
