module TypeSystem.Forall where

import Data.Set as Set (delete)
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same)
import TypeSystem.Methods
import TypeSystem.Type
import TypeSystem.Variable

data Forall κs s κ σ = Forall Identifier κ σ deriving (Show, Functor, Foldable, Traversable)

class EmbedForall κ σ where
  forallx' :: Forall κs s κ σ -> σ

forallx x κ σ = forallx' (Forall x κ σ)

class CheckForall m p κ σ where
  checkForall :: p -> σ -> m (Forall κs s κ σ)

instance
  ( Monad m,
    Positioned σ p,
    AugmentEnvironment m p κ,
    TypeCheckInstantiate κs κ m κ',
    EmbedType s κ,
    CheckType m p κ s,
    TypeCheck κ m σ
  ) =>
  TypeCheckImpl m p (Forall κs s κ' σ) κ
  where
  typeCheckImpl p (Forall x κ1' σ) = do
    κ1 <- instantiate @κs @κ κ1'
    Type s <- checkType @s (location σ) =<< augmentEnvironment p x κ1 (typeCheck @κ σ)
    pure $ typex @κ s

instance (FreeVariables σ u, FreeVariables κ u, Same u σ) => FreeVariables (Forall κs s κ σ) u where
  freeVariables' (Forall x κ σ) = case same @u @σ of
    Just Refl -> Set.delete x (freeVariables @u σ)
    Nothing -> freeVariables @u κ <> freeVariables @u σ

instance
  ( σ ~ σ',
    EmbedVariable σ,
    EmbedForall κ σ,
    Substitute u σ,
    Substitute u κ,
    Substitute σ σ',
    FreeVariables u σ
  ) =>
  SubstituteImpl (Forall κs s κ σ') u σ
  where
  substituteImpl ux x1 (Forall x2 κ σ) = forallx x2' (substitute ux x1 κ) (substitute ux x1 σ')
    where
      (x2', σ') = avoidCapture @σ (freeVariables @σ ux) (x2, σ)
