module TypeSystem.MacroAbstraction where

import Data.Proxy (Proxy (..))
import Data.Set as Set (delete)
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, proxyOf, same')
import TypeSystem.Macro hiding (phonyl)
import TypeSystem.Methods
import TypeSystem.Variable

data MacroAbstraction l l' σ e = MacroAbstraction Identifier l' σ e deriving (Show, Functor, Foldable, Traversable)

phonyl :: MacroAbstraction l l' σ e -> Proxy l
phonyl _ = Proxy

class EmbedMacroAbstraction l' σ e where
  macroAbstraction' :: MacroAbstraction l l' σ e -> e

class CheckMacroAbstraction' e where
  checkMacroAbstraction' :: e -> Maybe (Identifier, e)

macroAbstraction x l σ e = macroAbstraction' (MacroAbstraction x l σ e)

instance
  ( Monad m,
    EmbedMacro l σ,
    AugmentEnvironmentLinear m p σ lΓ,
    InstantiateType m σ' σ,
    Instantiate m l' l,
    Capture m p l lΓ,
    TypeCheckLinear m e σ lΓ
  ) =>
  TypeCheckLinearImpl m p (MacroAbstraction l l' σ' e) σ lΓ
  where
  typeCheckLinearImpl p f@(MacroAbstraction x l' σ' e) = do
    l <- instantiate' (phonyl f) l'
    σ <- instantiateType σ'
    (τ, lΓ) <- augmentEnvironmentLinear p x σ (typeCheckLinear e)
    capture p l lΓ
    pure (macro l σ τ, lΓ)

instance (FreeVariables l' u, FreeVariables σ u, FreeVariables e u, Same u e) => FreeVariables (MacroAbstraction l l' σ e) u where
  freeVariables u (MacroAbstraction x l σ e) = case same' u (proxyOf e) of
    Just Refl -> Set.delete x $ freeVariables u e
    Nothing -> freeVariables u l <> freeVariables u σ <> freeVariables u e

instance
  ( e ~ e',
    EmbedMacroAbstraction l' σ e,
    EmbedVariable e,
    FreeVariables u e,
    Substitute u l',
    Substitute u σ,
    Substitute u e,
    Substitute e e'
  ) =>
  SubstituteImpl (MacroAbstraction l l' σ e') u e
  where
  substituteImpl ux x1 (MacroAbstraction x2 l σ e) = macroAbstraction x2' (substitute ux x1 l) (substitute ux x1 σ) (substitute ux x1 e')
    where
      (x2', e') = avoidCapture (proxyOf e) (freeVariables (proxyOf e) ux) (x2, e)

instance (e ~ e', EmbedMacroAbstraction l' σ e, Reduce e) => ReduceImpl (MacroAbstraction l l' σ e') e where
  reduceImpl (MacroAbstraction x l σ e) = macroAbstraction x l σ (reduce e)
