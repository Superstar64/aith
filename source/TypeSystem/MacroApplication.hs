module TypeSystem.MacroApplication where

import Environment
import Misc.Util (firstM)
import TypeSystem.Macro
import TypeSystem.Methods

data MacroApplication e = MacroApplication e e deriving (Show, Functor, Foldable, Traversable)

class EmbedMacroApplication e where
  macroApplication :: e -> e -> e

instance
  ( Monad m,
    Usage lΓ,
    Positioned e p,
    CheckMacro m p σ,
    SameType m p σ,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (MacroApplication e) σ lΓ
  where
  typeCheckLinearImpl _ (MacroApplication e1 e2) = do
    (Macro σ τ, lΓ1) <- firstM (checkMacro $ location e1) =<< typeCheckLinear e1
    (σ', lΓ2) <- typeCheckLinear e2
    sameType (location e2) σ σ'
    pure (τ, combine lΓ1 lΓ2)

instance FreeVariables e u => FreeVariables (MacroApplication e) u where
  freeVariables' e = foldMap (freeVariables @u) e

instance (e ~ e', EmbedMacroApplication e, Substitute u e) => SubstituteImpl (MacroApplication e') u e where
  substituteImpl ux x (MacroApplication e1 e2) = macroApplication (substitute ux x e1) (substitute ux x e2)

instance
  ( e ~ e',
    EmbedMacroApplication e,
    ReduceMatchAbstraction e' e,
    Substitute e e',
    Reduce e
  ) =>
  ReduceImpl (MacroApplication e') e
  where
  reduceImpl (MacroApplication e1 e2) = case reduceMatchAbstraction (reduce e1) of
    Just f -> f (reduce e2)
    Nothing -> macroApplication (reduce e1) (reduce e2)
