module TypeSystem.Macro where

import TypeSystem.Methods
import TypeSystem.StageMacro
import TypeSystem.Type

data Macro ls l' s' l σ = Macro l σ σ deriving (Show, Functor, Foldable, Traversable)

class EmbedMacro l σ where
  macro' :: Macro ls l' s l σ -> σ

macro l σ τ = macro' (Macro l σ τ)

class CheckMacro' m p σ where
  checkMacro' :: p -> σ -> m (σ, σ)

instance
  ( Monad m,
    TypeCheckInstantiate ls l m l',
    Positioned σ p,
    EmbedType l s κ,
    EmbedStageMacro s,
    CheckType m p κ l s,
    TypeCheck κ m σ
  ) =>
  TypeCheckImpl m p (Macro ls l s l' σ) κ
  where
  typeCheckImpl _ (Macro l' σ τ) = do
    l <- instantiate @ls @l l'
    Type _ s1 <- checkType @l @s @κ (location σ) =<< typeCheck σ
    Type _ s2 <- checkType @l @s @κ (location τ) =<< typeCheck τ
    pure $ typex @κ l (stageMacro s1 s2)

instance (FreeVariables l u, FreeVariables σ u) => FreeVariables (Macro ls l' s l σ) u where
  freeVariables' (Macro l σ τ) = freeVariables @u l <> freeVariables @u σ <> freeVariables @u τ

instance
  ( σ ~ σ',
    EmbedMacro l σ,
    Substitute u l,
    Substitute u σ
  ) =>
  SubstituteImpl (Macro ls l' s l σ') u σ
  where
  substituteImpl ux x (Macro l σ τ) = macro (substitute ux x l) (substitute ux x σ) (substitute ux x τ)
