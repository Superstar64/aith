module TypeCheck.Substitute where

import Ast.Common
import Ast.Kind
import Ast.Type
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)

data Equation p
  = TypeEquation p TypeUnify TypeUnify
  | TypeSkolemBound p (Bound (Pattern TypeIdentifier KindUnify Internal) [Equation p]) (Set Constraint)
  | KindEquation p KindUnify KindUnify
  | KindMember p TypeUnify KindUnify
  | TypePredicate p Constraint TypeUnify
  deriving (Show)

instance Functor Equation where
  fmap f (TypeEquation p σ σ') = TypeEquation (f p) σ σ'
  fmap f (TypeSkolemBound p (Bound pm eqs) c) = TypeSkolemBound (f p) (Bound pm $ (fmap . fmap) f eqs) c
  fmap f (KindEquation p κ κ') = KindEquation (f p) κ κ'
  fmap f (KindMember p σ κ) = KindMember (f p) σ κ
  fmap f (TypePredicate p c σ) = TypePredicate (f p) c σ

instance Convert TypeIdentifier (Equation p) where
  convert σ x (TypeEquation p σ1 σ2) = TypeEquation p (convert σ x σ1) (convert σ x σ2)
  convert σ x (TypeSkolemBound p λ c) = TypeSkolemBound p (convert σ x λ) c
  convert _ _ eq@(KindEquation _ _ _) = eq
  convert σ x (KindMember p σ' κ) = KindMember p (convert σ x σ') κ
  convert σ x (TypePredicate p c τ) = TypePredicate p c (convert σ x τ)

instance
  Substitute
    TypeUnify
    TypeLogicalRaw
    (Equation p)
  where
  substitute σ x (TypeEquation p σ1 σ2) = TypeEquation p (substitute σ x σ1) (substitute σ x σ2)
  substitute σ x (TypeSkolemBound p λ c) = TypeSkolemBound p (substitute σ x λ) c
  substitute _ _ eq@(KindEquation _ _ _) = eq
  substitute σ x (KindMember p σ' κ) = KindMember p (substitute σ x σ') κ
  substitute σ x (TypePredicate p c τ) = TypePredicate p c (substitute σ x τ)

instance Substitute KindUnify KindLogicalRaw (Equation p) where
  substitute κ x (TypeEquation p σ1 σ2) = TypeEquation p (substitute κ x σ1) (substitute κ x σ2)
  substitute κ x (TypeSkolemBound p λ c) = TypeSkolemBound p (substitute κ x λ) c
  substitute κ x (KindEquation p κ1 κ2) = KindEquation p (substitute κ x κ1) (substitute κ x κ2)
  substitute κ x (KindMember p σ κ') = KindMember p (substitute κ x σ) (substitute κ x κ')
  substitute κ x (TypePredicate p c τ) = TypePredicate p c (substitute κ x τ)

data Substitution = Substitution
  { typeSubstitution :: Map TypeLogicalRaw TypeUnify,
    kindSubstitution :: Map KindLogicalRaw KindUnify
  }
  deriving (Show)

applySubstitution (Substitution θ θ') = (flip . foldr) (\(x, κ) -> substitute κ x) (Map.toList θ') . (flip . foldr) (\(x, τ) -> substitute τ x) (Map.toList θ)

identitySubstitution = Substitution Map.empty Map.empty

singleTypeSubstitution x σ = Substitution (Map.singleton x σ) Map.empty

singleKindSubstitution x σ = Substitution Map.empty (Map.singleton x σ)

-- from unification theory
-- https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf

composeSubsitutions (Substitution θ1 θ2) (Substitution θ1' θ2') = Substitution (composeSubsitutionsMap checkType θ1 θ1') (composeSubsitutionsMap checkKind θ2 θ2')
  where
    composeSubsitutionsMap notIdentity σ θ = Map.union σ2 θ1
      where
        σ1 = (flip . foldr) (\(x, τ) -> substitute τ x) (Map.toList θ) <$> σ
        θ1 = foldr Map.delete θ (Map.keys σ)
        σ2 = Map.filterWithKey notIdentity σ1
    checkType x (CoreType _ (TypeLogical x')) | x == x' = False
    checkType _ _ = True
    checkKind x (CoreKind _ (KindLogical x')) | x == x' = False
    checkKind _ _ = True

instance Semigroup Substitution where
  (<>) = composeSubsitutions

instance Monoid Substitution where
  mempty = identitySubstitution
