module TypeSystem.Macro where

import Data.Proxy (Proxy (..), asProxyTypeOf)
import TypeSystem.Methods
import TypeSystem.StageMacro
import TypeSystem.Type

data Macro l s l' σ = Macro l' σ σ deriving (Show, Functor, Foldable, Traversable)

phonyl :: Macro l s l' σ -> Proxy l
phonyl _ = Proxy

phonys :: Macro l s l' σ -> Proxy s
phonys _ = Proxy

class EmbedMacro l' σ where
  macro' :: Macro l s l' σ -> σ

macro l σ τ = macro' (Macro l σ τ)

class CheckMacro' m p σ where
  checkMacro' :: p -> σ -> m (σ, σ)

instance (FreeVariables l' u, FreeVariables σ u) => FreeVariables (Macro l s l' σ) u where
  freeVariables u (Macro l σ τ) = freeVariables u l <> freeVariables u σ <> freeVariables u τ

instance
  ( σ ~ σ',
    EmbedMacro l' σ,
    Substitute u l',
    Substitute u σ
  ) =>
  SubstituteImpl (Macro l s l' σ') u σ
  where
  substituteImpl ux x (Macro l σ τ) = macro (substitute ux x l) (substitute ux x σ) (substitute ux x τ)

instance
  ( Monad m,
    Instantiate m l' l,
    Positioned σ p,
    EmbedType l s κ,
    EmbedStageMacro s,
    CheckType m p κ l s,
    TypeCheck m σ κ
  ) =>
  TypeCheckImpl m p (Macro l s l' σ) κ
  where
  typeCheckImpl _ f@(Macro l' σ τ) = do
    l <- instantiate' (phonyl f) l'
    (z, Type _ s1) <- checkType' (phonyl f) (phonys f) (location σ) =<< typeCheck σ
    (z', Type _ s2) <- checkType' (phonyl f) (phonys f) (location τ) =<< typeCheck τ
    pure $ flip asProxyTypeOf z $ flip asProxyTypeOf z' $ typex l (stageMacro s1 s2)
