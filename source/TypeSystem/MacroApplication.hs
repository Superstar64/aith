module TypeSystem.MacroApplication where

import Environment
import Misc.Util (firstM)
import TypeSystem.Macro
import TypeSystem.MacroAbstraction
import TypeSystem.Methods

data MacroApplication e = MacroApplication e e deriving (Show, Functor, Foldable, Traversable)

class EmbedMacroApplication e where
  macroApplication' :: MacroApplication e -> e

macroApplication e1 e2 = macroApplication' $ MacroApplication e1 e2

instance
  ( Monad m,
    Usage lΓ,
    Positioned e p,
    CheckMacro' m p σ,
    SameType m p σ,
    TypeCheckLinear m e σ lΓ
  ) =>
  TypeCheckLinearImpl m p (MacroApplication e) σ lΓ
  where
  typeCheckLinearImpl _ (MacroApplication e1 e2) = do
    ((σ, τ), lΓ1) <- firstM (checkMacro' $ location e1) =<< typeCheckLinear e1
    (σ', lΓ2) <- typeCheckLinear e2
    sameType (location e2) σ σ'
    pure (τ, combine lΓ1 lΓ2)

instance FreeVariables e u => FreeVariables (MacroApplication e) u where
  freeVariables u e = foldMap (freeVariables u) e

instance (e ~ e', EmbedMacroApplication e, Substitute u e) => SubstituteImpl (MacroApplication e') u e where
  substituteImpl ux x (MacroApplication e1 e2) = macroApplication (substitute ux x e1) (substitute ux x e2)

instance
  ( e ~ e',
    EmbedMacroApplication e,
    CheckMacroAbstraction' e,
    Substitute e e',
    Reduce e
  ) =>
  ReduceImpl (MacroApplication e') e
  where
  reduceImpl (MacroApplication e1 e2) = case checkMacroAbstraction' (reduce e1) of
    Just (x, e) -> reduce (substitute (reduce e2) x e)
    Nothing -> macroApplication (reduce e1) (reduce e2)
