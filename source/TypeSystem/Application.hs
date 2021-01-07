module TypeSystem.Application where

import Environment
import Misc.Util (firstM)
import TypeSystem.Function
import TypeSystem.Methods

data Application e = Application e e

class EmbedApplication e where
  application :: e -> e -> e

instance
  ( Monad m,
    Positioned e p,
    SameType m p σ,
    CheckFunction m p σ,
    TypeCheck σ m e
  ) =>
  TypeCheckImpl m p (Application e) σ
  where
  typeCheckImpl _ (Application e1 e2) = do
    Function σ τ <- checkFunction (location e1) =<< typeCheck e1
    σ' <- typeCheck e2
    sameType (location e2) σ σ'
    pure τ

instance
  ( Monad m,
    Usage lΓ,
    Positioned e p,
    CheckFunction m p σ,
    SameType m p σ,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (Application e) σ lΓ
  where
  typeCheckLinearImpl _ (Application e1 e2) = do
    (Function σ τ, lΓ1) <- firstM (checkFunction $ location e1) =<< typeCheckLinear e1
    (σ', lΓ2) <- typeCheckLinear e2
    sameType (location e2) σ σ'
    pure (τ, combine lΓ1 lΓ2)

instance FreeVariables e u => FreeVariables (Application e) u where
  freeVariables' (Application e1 e2) = freeVariables @u e1 <> freeVariables @u e2

instance (e ~ e', EmbedApplication e, Substitute u e) => SubstituteImpl (Application e') u e where
  substituteImpl ux x (Application e1 e2) = application (substitute ux x e1) (substitute ux x e2)

instance
  ( e ~ e',
    EmbedApplication e,
    ReduceMatchAbstraction e' e,
    Substitute e e',
    Reduce e
  ) =>
  ReduceImpl (Application e') e
  where
  reduceImpl (Application e1 e2) = case reduceMatchAbstraction (reduce e1) of
    Just f -> f (reduce e2)
    Nothing -> application (reduce e1) (reduce e2)
