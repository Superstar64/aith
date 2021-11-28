module Language.TypeCheck.Variable where

import Language.Ast.Common
import Language.Ast.Kind
import Language.Ast.Type
import Misc.MonoidMap (Map)
import qualified Misc.MonoidMap as Map

data TypeEquation p
  = TypeEquation p TypeUnify TypeUnify
  | TypeSkolemBound p (Bound (Pattern TypeIdentifier KindUnify Internal) [TypeEquation p])
  deriving (Show)

instance Functor TypeEquation where
  fmap f (TypeEquation p σ σ') = TypeEquation (f p) σ σ'
  fmap f (TypeSkolemBound p (Bound pm eqs)) = TypeSkolemBound (f p) (Bound pm $ (fmap . fmap) f eqs)

instance Convert TypeIdentifier (TypeEquation p) where
  convert σ x (TypeEquation p σ1 σ2) = TypeEquation p (convert σ x σ1) (convert σ x σ2)
  convert σ x (TypeSkolemBound p λ) = TypeSkolemBound p (convert σ x λ)

instance
  Substitute
    TypeUnify
    TypeLogicalRaw
    (TypeEquation p)
  where
  substitute σ x (TypeEquation p σ1 σ2) = TypeEquation p (substitute σ x σ1) (substitute σ x σ2)
  substitute σ x (TypeSkolemBound p λ) = TypeSkolemBound p (substitute σ x λ)

data KindEquation p = KindEquation p KindUnify KindUnify deriving (Show)

instance Functor KindEquation where
  fmap f (KindEquation p κ κ') = KindEquation (f p) κ κ'

instance
  Substitute
    (Kind KindLogicalRaw Internal)
    KindLogicalRaw
    (KindEquation p)
  where
  substitute κ x (KindEquation p κ1 κ2) = KindEquation p (substitute κ x κ1) (substitute κ x κ2)

newtype Substitution x σ = Substitution (Map x σ) deriving (Show)

applySubstitution (Substitution θ) σ = foldr (\(x, τ) -> substitute τ x) σ (Map.toList θ)

identitySubstitution = Substitution $ Map.empty

singleSubstitution x σ = Substitution $ Map.singleton x σ

-- from unification theory
-- https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf

composeSubsitutions notIdentity (Substitution σ) (Substitution θ) = Substitution $ Map.union σ2 θ1
  where
    σ1 = applySubstitution (Substitution θ) <$> σ
    θ1 = foldr Map.delete θ (Map.keys σ)
    σ2 = Map.filterWithKey notIdentity σ1

instance Semigroup (Substitution TypeLogicalRaw TypeUnify) where
  (<>) = composeSubsitutions check
    where
      check x (CoreType _ (TypeLogical x')) | x == x' = False
      check _ _ = True

instance Monoid (Substitution TypeLogicalRaw TypeUnify) where
  mempty = identitySubstitution

instance Semigroup (Substitution KindLogicalRaw KindUnify) where
  (<>) = composeSubsitutions check
    where
      check x (CoreKind _ (KindLogical x')) | x == x' = False
      check _ _ = True

instance Monoid (Substitution KindLogicalRaw KindUnify) where
  mempty = identitySubstitution
