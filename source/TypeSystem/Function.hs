module TypeSystem.Function where

import TypeSystem.Methods
import TypeSystem.StageFunction
import TypeSystem.Type

data Function s σ = Function σ σ

class EmbedFunction σ where
  function :: σ -> σ -> σ

class CheckFunction m p σ where
  checkFunction :: p -> σ -> m (Function s σ)

instance
  ( Monad m,
    Positioned σ p,
    EmbedType κ s,
    EmbedStageFunction s,
    CheckType s κ m p,
    TypeCheck κ m σ
  ) =>
  TypeCheckImpl m p (Function s σ) κ
  where
  typeCheckImpl _ (Function σ τ) = do
    Type s1 <- checkType @s @κ (location σ) =<< typeCheck σ
    Type s2 <- checkType @s @κ (location τ) =<< typeCheck τ
    pure $ typex @κ (stageFunction s1 s2)

instance (FreeVariables σ u) => FreeVariables (Function s σ) u where
  freeVariables' (Function σ τ) = freeVariables @u σ <> freeVariables @u τ

instance
  ( σ ~ σ',
    EmbedFunction σ,
    Substitute u σ
  ) =>
  SubstituteImpl (Function s σ') u σ
  where
  substituteImpl ux x (Function σ τ) = function (substitute ux x σ) (substitute ux x τ)

instance
  ( σ ~ σ',
    EmbedFunction σ,
    Reduce σ
  ) =>
  ReduceImpl (Function s σ) σ'
  where
  reduceImpl (Function σ τ) = function (reduce σ) (reduce τ)
