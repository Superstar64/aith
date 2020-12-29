module TypeSystem.Macro where

import TypeSystem.Methods
import TypeSystem.StageMacro
import TypeSystem.Type

data Macro s σ = Macro σ σ deriving (Show, Functor, Foldable, Traversable)

class EmbedMacro σ where
  macro :: σ -> σ -> σ

class CheckMacro m p σ where
  checkMacro :: p -> σ -> m (Macro s σ)

instance
  ( Monad m,
    Positioned σ p,
    EmbedType s κ,
    EmbedStageMacro s,
    CheckType m p κ s,
    TypeCheck κ m σ
  ) =>
  TypeCheckImpl m p (Macro s σ) κ
  where
  typeCheckImpl _ (Macro σ τ) = do
    Type s1 <- checkType @s @κ (location σ) =<< typeCheck σ
    Type s2 <- checkType @s @κ (location τ) =<< typeCheck τ
    pure $ typex @κ (stageMacro s1 s2)

instance (FreeVariables σ u) => FreeVariables (Macro s σ) u where
  freeVariables' (Macro σ τ) = freeVariables @u σ <> freeVariables @u τ

instance
  ( σ ~ σ',
    EmbedMacro σ,
    Substitute u σ
  ) =>
  SubstituteImpl (Macro s σ') u σ
  where
  substituteImpl ux x (Macro σ τ) = macro (substitute ux x σ) (substitute ux x τ)
