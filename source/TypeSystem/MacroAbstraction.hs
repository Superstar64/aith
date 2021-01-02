module TypeSystem.MacroAbstraction where

import Data.Type.Equality ((:~:) (..))
import Misc.Util (Same, same)
import TypeSystem.Linear
import TypeSystem.Macro
import TypeSystem.Methods

data MacroAbstraction l pm' pm e = MacroAbstraction pm e deriving (Show, Functor, Foldable, Traversable)

class EmbedMacroAbstraction pm e where
  macroAbstraction :: pm -> e -> e

instance
  ( Monad m,
    EmbedMacro σ,
    EmbedLinear l,
    TypeCheckInstantiate σ pm m pm',
    AugmentEnvironmentPattern m pm p l σ lΓ,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (MacroAbstraction l pm pm' e) σ lΓ
  where
  typeCheckLinearImpl p (MacroAbstraction pm' e) = do
    (σ, pm) <- typeCheckInstantiate @σ @pm pm'
    (τ, lΓ) <- augmentEnvironmentPattern pm (linear @l) p (typeCheckLinear e)
    pure (macro σ τ, lΓ)

instance
  ( Same u e,
    FreeVariables e u,
    FreeVariables pm u,
    RemoveBindings pm
  ) =>
  FreeVariables (MacroAbstraction l pm' pm e) u
  where
  freeVariables' (MacroAbstraction pm e) = case same @u @e of
    Just Refl -> removeBindings pm $ freeVariables @u e
    Nothing -> freeVariables @u pm <> freeVariables @u e

instance
  ( e ~ e',
    EmbedMacroAbstraction pm e,
    AvoidCapturePattern u pm e,
    Substitute u e,
    Substitute u pm
  ) =>
  SubstituteImpl (MacroAbstraction l pm' pm e') u e
  where
  substituteImpl ux x (MacroAbstraction pm e) = macroAbstraction (substitute ux x pm') (substitute ux x e')
    where
      (pm', e') = avoidCapturePattern ux (pm, e)

instance (e ~ e', EmbedMacroAbstraction pm e, Reduce e) => ReduceImpl (MacroAbstraction l pm' pm e') e where
  reduceImpl (MacroAbstraction pm e) = macroAbstraction pm (reduce e)
