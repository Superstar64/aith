module Language.TypeCheck.Variable where

import Language.Ast.Common
import Language.Ast.Kind
import Language.Ast.Sort
import Language.Ast.Term
import Language.Ast.Type
import Misc.MonoidMap (Map)
import qualified Misc.MonoidMap as Map

newtype LogicVariableType = LogicVariableType Int deriving (Eq, Ord, Show)

newtype LogicVariableKind = LogicVariableKind Int deriving (Eq, Ord, Show)

type TypeUnify = Type KindUnify LogicVariableType Internal

type KindUnify = Kind LogicVariableKind Internal

type TypeSchemeUnify = TypeScheme KindUnify LogicVariableType Internal Internal

type InstantiationUnify = Instantiation KindUnify TypeUnify Internal

instance FreeVariables LogicVariableType Internal TypeUnify where
  freeVariables (CoreType _ (TypeExtra x)) = Map.singleton x Internal
  freeVariables (CoreType _ σ) = foldTypeF mempty mempty go σ
    where
      go = freeVariables

instance FreeVariables LogicVariableKind Internal TypeUnify where
  freeVariables (CoreType _ σ) = foldTypeF mempty go go σ
    where
      go = freeVariables

instance FreeVariables LogicVariableKind Internal KindUnify where
  freeVariables (CoreKind _ (KindExtra x)) = Map.singleton x Internal
  freeVariables (CoreKind _ κ) = foldKindF mempty freeVariables κ

instance Substitute TypeUnify LogicVariableType TypeUnify where
  substitute ux x (CoreType _ (TypeExtra x')) | x == x' = ux
  substitute ux x (CoreType p σ) = CoreType p $ mapTypeF id id go σ
    where
      go = substitute ux x

instance Substitute KindUnify LogicVariableKind KindUnify where
  substitute ux x (CoreKind _ (KindExtra x')) | x == x' = ux
  substitute ux x (CoreKind p κ) = CoreKind p $ mapKindF id go κ
    where
      go = substitute ux x

instance Substitute KindUnify LogicVariableKind (TypeScheme KindUnify LogicVariableType Internal p) where
  substitute ux x (CoreTypeScheme p σ) = CoreTypeScheme p $ mapTypeSchemeF go go go σ
    where
      go = substitute ux x

instance FreeVariablesInternal LogicVariableType TypeUnify where
  freeVariablesInternal = freeVariables

instance FreeVariablesInternal LogicVariableKind TypeUnify where
  freeVariablesInternal = freeVariables

instance FreeVariablesInternal LogicVariableKind KindUnify where
  freeVariablesInternal = freeVariables

instance Substitute TypeUnify LogicVariableType (TermPattern InstantiationUnify KindUnify TypeUnify p) where
  substitute ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go go pm
    where
      go = substitute ux x

instance Substitute KindUnify LogicVariableKind (TermPattern InstantiationUnify KindUnify TypeUnify p) where
  substitute ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go go pm
    where
      go = substitute ux x

instance Substitute TypeUnify LogicVariableType (Term InstantiationUnify KindUnify TypeUnify p) where
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTermF go id go go go e
    where
      go = substitute ux x

instance Substitute KindUnify LogicVariableKind (Term InstantiationUnify KindUnify TypeUnify p) where
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTermF go go go go go e
    where
      go = substitute ux x

instance Substitute KindUnify LogicVariableKind TypeUnify where
  substitute ux x (CoreType p σ) = CoreType p $ mapTypeF id go go σ
    where
      go = substitute ux x

instance Substitute TypeUnify x KindUnify where
  substitute _ _ = id

instance
  (Substitute TypeUnify LogicVariableType u) =>
  Substitute TypeUnify LogicVariableType (Bound (TermPattern InstantiationUnify KindUnify TypeUnify p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  (Substitute KindUnify LogicVariableKind u) =>
  Substitute KindUnify LogicVariableKind (Bound (TermPattern InstantiationUnify KindUnify TypeUnify p) u)
  where
  substitute = substituteHigher substitute substitute

instance Substitute TypeUnify LogicVariableType InstantiationUnify where
  substitute ux x (InstantiateType x' σ θ) = InstantiateType x' (substitute ux x σ) (substitute ux x θ)
  substitute ux x (InstantiateKind x' κ θ) = InstantiateKind x' κ (substitute ux x θ)
  substitute _ _ InstantiateEmpty = InstantiateEmpty

instance Substitute KindUnify LogicVariableKind InstantiationUnify where
  substitute ux x (InstantiateType x' σ θ) = InstantiateType x' σ (substitute ux x θ)
  substitute ux x (InstantiateKind x' κ θ) = InstantiateKind x' (substitute ux x κ) (substitute ux x θ)
  substitute _ _ InstantiateEmpty = InstantiateEmpty

instance
  ( Substitute KindUnify LogicVariableKind u
  ) =>
  Substitute KindUnify LogicVariableKind (Bound (Pattern TypeIdentifier KindUnify p) u)
  where
  substitute = substituteHigher substitute substitute

-- todo avoiding captures breaks this, figure out what to do
instance
  ( Substitute KindUnify LogicVariableKind u,
    Convert KindIdentifier u
  ) =>
  Substitute KindUnify LogicVariableKind (Bound (Pattern KindIdentifier Sort p) u)
  where
  substitute ux x (Bound pm κ) = Bound pm (substitute ux x κ)

data TypeEquation p σ = TypeEquation p σ σ
  deriving (Show, Functor)

data KindEquation p κ = KindEquation p κ κ deriving (Show, Functor)

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

instance Semigroup (Substitution LogicVariableType TypeUnify) where
  (<>) = composeSubsitutions check
    where
      check x (CoreType _ (TypeExtra x')) | x == x' = False
      check _ _ = True

instance Monoid (Substitution LogicVariableType TypeUnify) where
  mempty = identitySubstitution

instance Semigroup (Substitution LogicVariableKind KindUnify) where
  (<>) = composeSubsitutions check
    where
      check x (CoreKind _ (KindExtra x')) | x == x' = False
      check _ _ = True

instance Monoid (Substitution LogicVariableKind KindUnify) where
  mempty = identitySubstitution
