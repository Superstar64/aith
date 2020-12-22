module TypeSystem.MacroAbstraction where

import Data.Set as Set (delete)
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same)
import TypeSystem.Macro
import TypeSystem.Methods
import TypeSystem.Variable

data MacroAbstraction ls l' κ l σ e = MacroAbstraction Identifier l σ e deriving (Show, Functor, Foldable, Traversable)

class EmbedMacroAbstraction l σ e where
  macroAbstraction' :: MacroAbstraction ls l' κ l σ e -> e

macroAbstraction x l σ e = macroAbstraction' (MacroAbstraction x l σ e)

instance
  ( Monad m,
    EmbedMacro l σ,
    AugmentEnvironmentLinear m p σ lΓ,
    TypeCheckInstantiate κ σ m σ',
    TypeCheckInstantiate ls l m l',
    Capture m p l lΓ,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (MacroAbstraction ls l κ l' σ' e) σ lΓ
  where
  typeCheckLinearImpl p (MacroAbstraction x l' σ' e) = do
    l <- instantiate @ls @l l'
    σ <- instantiate @κ σ'
    (τ, lΓ) <- augmentEnvironmentLinear p x σ (typeCheckLinear e)
    capture p l lΓ
    pure (macro l σ τ, lΓ)

instance
  ( FreeVariables l u,
    FreeVariables σ u,
    FreeVariables e u,
    Same u e
  ) =>
  FreeVariables (MacroAbstraction ls l' κ l σ e) u
  where
  freeVariables' (MacroAbstraction x l σ e) = case same @u @e of
    Just Refl -> Set.delete x $ freeVariables @u e
    Nothing -> freeVariables @u l <> freeVariables @u σ <> freeVariables @u e

instance
  ( e ~ e',
    EmbedMacroAbstraction l σ e,
    EmbedVariable e,
    FreeVariables u e,
    Substitute u l,
    Substitute u σ,
    Substitute u e,
    Substitute e e'
  ) =>
  SubstituteImpl (MacroAbstraction ls l' κ l σ e') u e
  where
  substituteImpl ux x1 (MacroAbstraction x2 l σ e) = macroAbstraction x2' (substitute ux x1 l) (substitute ux x1 σ) (substitute ux x1 e')
    where
      (x2', e') = avoidCapture @e (freeVariables @e ux) (x2, e)

instance (e ~ e', EmbedMacroAbstraction l σ e, Reduce e) => ReduceImpl (MacroAbstraction ls l' κ l σ e') e where
  reduceImpl (MacroAbstraction x l σ e) = macroAbstraction x l σ (reduce e)
