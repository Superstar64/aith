module TypeSystem.MacroAbstraction where

import Data.Set as Set (delete)
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same)
import TypeSystem.Linear
import TypeSystem.Macro
import TypeSystem.Methods
import TypeSystem.Variable

data MacroAbstraction l κ σ e = MacroAbstraction Identifier σ e deriving (Show, Functor, Foldable, Traversable)

class EmbedMacroAbstraction σ e where
  macroAbstraction' :: MacroAbstraction l κ σ e -> e

macroAbstraction x σ e = macroAbstraction' (MacroAbstraction x σ e)

instance
  ( Monad m,
    EmbedMacro σ,
    EmbedLinear l,
    AugmentEnvironmentLinear m p l σ lΓ,
    TypeCheckInstantiate κ σ m σ',
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (MacroAbstraction l κ σ' e) σ lΓ
  where
  typeCheckLinearImpl p (MacroAbstraction x σ' e) = do
    σ <- instantiate @κ σ'
    (τ, lΓ) <- augmentEnvironmentLinear p x (linear @l) σ (typeCheckLinear e)
    pure (macro σ τ, lΓ)

instance
  ( FreeVariables σ u,
    FreeVariables e u,
    Same u e
  ) =>
  FreeVariables (MacroAbstraction l κ σ e) u
  where
  freeVariables' (MacroAbstraction x σ e) = case same @u @e of
    Just Refl -> Set.delete x $ freeVariables @u e
    Nothing -> freeVariables @u σ <> freeVariables @u e

instance
  ( e ~ e',
    EmbedMacroAbstraction σ e,
    EmbedVariable e,
    FreeVariables u e,
    Substitute u σ,
    Substitute u e,
    Substitute e e'
  ) =>
  SubstituteImpl (MacroAbstraction l κ σ e') u e
  where
  substituteImpl ux x1 (MacroAbstraction x2 σ e) = macroAbstraction x2' (substitute ux x1 σ) (substitute ux x1 e')
    where
      (x2', e') = avoidCapture @e (freeVariables @e ux) (x2, e)

instance (e ~ e', EmbedMacroAbstraction σ e, Reduce e) => ReduceImpl (MacroAbstraction l κ σ e') e where
  reduceImpl (MacroAbstraction x σ e) = macroAbstraction x σ (reduce e)
