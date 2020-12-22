module TypeSystem.LinearForall where

import Data.Set as Set (delete)
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same)
import TypeSystem.Linear
import TypeSystem.Multiplicity
import TypeSystem.Methods
import TypeSystem.Type
import TypeSystem.Variable

data LinearForall ls l s σ = LinearForall Identifier σ deriving (Show, Functor, Foldable, Traversable)

class EmbedLinearForall σ where
  linearForall' :: LinearForall ls l s σ -> σ

linearForall x σ = linearForall' (LinearForall x σ)

class CheckLinearForall m p σ where
  checkLinearForall :: p -> σ -> m (LinearForall ls l s σ)

instance
  ( Monad m,
    EmbedType l s κ,
    EmbedMultiplicity ls,
    EmbedLinear l,
    SubstituteSame l,
    Positioned σ p,
    AugmentEnvironment m p ls,
    CheckType m p κ l s,
    TypeCheck κ m σ
  ) =>
  TypeCheckImpl m p (LinearForall ls l s σ) κ
  where
  typeCheckImpl p (LinearForall x σ) = do
    Type l s <- checkType @l @s (location σ) =<< augmentEnvironment p x (multiplicity @ls) (typeCheck @κ σ)
    pure $ typex @κ (substituteSame linear x l) s

instance (Same u l, FreeVariables σ u) => FreeVariables (LinearForall ls l s σ) u where
  freeVariables' (LinearForall x σ) = case same @u @l of
    Just Refl -> Set.delete x $ freeVariables @u σ
    Nothing -> freeVariables @u σ

instance
  ( σ ~ σ',
    EmbedLinearForall σ,
    EmbedVariable l,
    FreeVariables u l,
    Substitute l σ,
    Substitute u σ
  ) =>
  SubstituteImpl (LinearForall ls l s σ') u σ
  where
  substituteImpl ux x1 (LinearForall x2 σ) = linearForall x2' (substitute ux x1 σ')
    where
      (x2', σ') = avoidCapture @l (freeVariables @l ux) (x2, σ)
