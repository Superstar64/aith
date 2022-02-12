module Ast.Type where

import Ast.Common
import Ast.Kind
import Ast.Sort
import Data.Bitraversable (bitraverse)
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
import Misc.Isomorph
import Misc.Prism

data TypeSchemeF λκ λσ σ
  = MonoType σ
  | ImplicitForall λσ (Set Constraint)
  | ImplicitKindForall λκ
  deriving (Show)

data TypeScheme κ vσ p' p
  = CoreTypeScheme
      p
      ( TypeSchemeF
          (Bound (Pattern KindIdentifier Sort p) (TypeScheme κ vσ p' p))
          (Bound (Pattern TypeIdentifier κ p) (TypeScheme κ vσ p' p))
          (Type κ vσ p')
      )
  deriving (Show)

type TypeSchemeAuto p = Maybe (TypeScheme (KindAuto p) Void p p)

type TypeSchemeUnify = TypeScheme KindUnify TypeLogicalRaw Internal Internal

type TypeSchemeInfer = TypeScheme (Kind Void Internal) Void Internal Internal

instance UnInfer TypeSchemeInfer (TypeSchemeAuto Internal) where
  unInfer = Just . mapTypeScheme unInfer absurd id id

data Instantiation κ σ p
  = InstantiateType TypeIdentifier σ (Instantiation κ σ p)
  | InstantiateKind KindIdentifier κ (Instantiation κ σ p)
  | InstantiateEmpty
  deriving (Show)

type InstantiationUnify = Instantiation KindUnify TypeUnify Internal

type InstantiationInfer = Instantiation KindInfer TypeInfer Internal

data Constraint
  = Copy
  deriving (Eq, Ord, Show)

data TypeF v λ κ σ
  = TypeVariable TypeIdentifier
  | TypeLogical v
  | Macro σ σ
  | Forall λ (Set Constraint)
  | OfCourse σ
  | FunctionPointer σ σ σ
  | FunctionLiteralType σ σ σ
  | Pair σ σ
  | Effect σ σ
  | Reference σ σ
  | Number κ κ
  deriving (Show)

data Type κ vσ p = CoreType p (TypeF vσ (Bound (Pattern TypeIdentifier κ p) (Type κ vσ p)) κ (Type κ vσ p)) deriving (Show)

type TypeAuto p = Maybe (Type (KindAuto p) Void p)

type TypeUnify = Type KindUnify TypeLogicalRaw Internal

type TypeInfer = Type KindInfer Void Internal

instance UnInfer TypeInfer (TypeAuto Internal) where
  unInfer = Just . mapType unInfer absurd id

instance Functor (TypeScheme κ vσ p') where
  fmap f = runIdentity . traverseTypeScheme pure pure pure (Identity . f)

traverseTypeSchemeF ::
  Applicative m =>
  (λκ -> m λκ') ->
  (λσ -> m λσ') ->
  (σ -> m σ') ->
  TypeSchemeF λκ λσ σ ->
  m (TypeSchemeF λκ' λσ' σ')
traverseTypeSchemeF f g h σ =
  case σ of
    MonoType σ -> pure MonoType <*> h σ
    ImplicitForall λ c -> pure ImplicitForall <*> g λ <*> pure c
    ImplicitKindForall λ -> pure ImplicitKindForall <*> f λ

mapTypeSchemeF f g h = runIdentity . traverseTypeSchemeF (Identity . f) (Identity . g) (Identity . h)

foldTypeSchemeF f g h = getConst . traverseTypeSchemeF (Const . f) (Const . g) (Const . h)

traverseTypeScheme ::
  Applicative m =>
  (κ -> m κ') ->
  (vσ -> m vσ') ->
  (p1 -> m p1') ->
  (p2 -> m p2') ->
  TypeScheme κ vσ p1 p2 ->
  m (TypeScheme κ' vσ' p1' p2')
traverseTypeScheme f g h i (CoreTypeScheme p σ) =
  let recurse = traverseTypeScheme f g h i
   in pure CoreTypeScheme <*> i p <*> traverseTypeSchemeF (bitraverse (traversePattern pure pure i) recurse) (bitraverse (traversePattern pure f i) recurse) (traverseType f g h) σ

mapTypeScheme f g h i = runIdentity . traverseTypeScheme (Identity . f) (Identity . g) (Identity . h) (Identity . i)

traverseTypeF ::
  Applicative m =>
  (v -> m v') ->
  (λ -> m λ') ->
  (κ -> m κ') ->
  (σ -> m σ') ->
  TypeF v λ κ σ ->
  m (TypeF v' λ' κ' σ')
traverseTypeF f i h g σ = case σ of
  TypeVariable x -> pure TypeVariable <*> pure x
  TypeLogical v -> pure TypeLogical <*> f v
  Macro σ τ -> pure Macro <*> g σ <*> g τ
  Forall λ c -> pure Forall <*> i λ <*> pure c
  OfCourse σ -> pure OfCourse <*> g σ
  FunctionPointer σ π τ -> pure FunctionPointer <*> g σ <*> g π <*> g τ
  FunctionLiteralType σ π τ -> pure FunctionLiteralType <*> g σ <*> g π <*> g τ
  Pair σ τ -> pure Pair <*> g σ <*> g τ
  Effect π σ -> pure Effect <*> g π <*> g σ
  Reference π σ -> pure Reference <*> g π <*> g σ
  Number ρ ρ' -> pure Number <*> h ρ <*> h ρ'

mapTypeF f i h g = runIdentity . traverseTypeF (Identity . f) (Identity . i) (Identity . h) (Identity . g)

foldTypeF f i h g = getConst . traverseTypeF (Const . f) (Const . i) (Const . h) (Const . g)

traverseType :: Applicative m => (κ -> m κ') -> (vσ -> m vσ') -> (p -> m p') -> Type κ vσ p -> m (Type κ' vσ' p')
traverseType f g h (CoreType p σ) =
  let recurse = traverseType f g h
   in pure CoreType <*> h p <*> traverseTypeF g (bitraverse (traversePattern pure f h) recurse) f recurse σ

mapType f g h = runIdentity . traverseType (Identity . f) (Identity . g) (Identity . h)

coreTypeScheme = Isomorph (uncurry CoreTypeScheme) $ \(CoreTypeScheme p σ) -> (p, σ)

monoType = Prism MonoType $ \case
  (MonoType σ) -> Just σ
  _ -> Nothing

forallx = Prism (uncurry ImplicitForall) $ \case
  (ImplicitForall λ c) -> Just (λ, c)
  _ -> Nothing

kindForall = Prism ImplicitKindForall $ \case
  (ImplicitKindForall λ) -> Just λ
  _ -> Nothing

coreType = Isomorph (uncurry CoreType) $ \(CoreType p σ) -> (p, σ)

typeVariable = Prism TypeVariable $ \case
  (TypeVariable x) -> Just x
  _ -> Nothing

typeExtra = Prism TypeLogical $ \case
  (TypeLogical v) -> Just v
  _ -> Nothing

macro = Prism (uncurry Macro) $ \case
  (Macro σ τ) -> Just (σ, τ)
  _ -> Nothing

explicitForall = Prism (uncurry Forall) $ \case
  (Forall λ c) -> Just (λ, c)
  _ -> Nothing

ofCourse = Prism OfCourse $ \case
  (OfCourse σ) -> Just σ
  _ -> Nothing

functionPointer = Prism (uncurry $ uncurry FunctionPointer) $ \case
  (FunctionPointer σ π τ) -> Just ((σ, π), τ)
  _ -> Nothing

functionLiteralType = Prism (uncurry $ uncurry FunctionLiteralType) $ \case
  (FunctionLiteralType σ π τ) -> Just ((σ, π), τ)
  _ -> Nothing

copy = Prism (const Copy) $ \case
  Copy -> Just ()

runtimePair = Prism (uncurry Pair) $ \case
  (Pair σ τ) -> Just (σ, τ)
  _ -> Nothing

effect = Prism (uncurry Effect) $ \case
  (Effect π σ) -> Just (π, σ)
  _ -> Nothing

reference = Prism (uncurry Reference) $ \case
  (Reference π σ) -> Just (π, σ)
  _ -> Nothing

number = Prism (uncurry Number) $ \case
  (Number ρ ρ') -> Just (ρ, ρ')
  _ -> Nothing

instance Functor (Type κ vσ) where
  fmap f = runIdentity . traverseType pure pure (Identity . f)

instance FreeVariables TypeIdentifier (TypeScheme κ vσ p p) where
  freeVariables (CoreTypeScheme _ σ) = foldTypeSchemeF go go go σ
    where
      go = freeVariables

instance
  ( Convert KindIdentifier κ
  ) =>
  Convert TypeIdentifier (TypeScheme κ vσ p' p)
  where
  convert ux x (CoreTypeScheme p σ) = CoreTypeScheme p $ mapTypeSchemeF go go go σ
    where
      go = convert ux x

instance
  ( Convert KindIdentifier κ,
    FreeVariables KindIdentifier κ
  ) =>
  Substitute (Type κ vσ p) TypeIdentifier (TypeScheme κ vσ p p)
  where
  substitute ux x (CoreTypeScheme p σ) = CoreTypeScheme p $ mapTypeSchemeF go go go σ
    where
      go = substitute ux x

instance
  ( Convert KindIdentifier κ
  ) =>
  Convert KindIdentifier (TypeScheme κ vσ p' p)
  where
  convert ux x (CoreTypeScheme p σ) = CoreTypeScheme p $ mapTypeSchemeF go go go σ
    where
      go = convert ux x

instance
  ( FreeVariables KindIdentifier κ,
    Substitute κ KindIdentifier κ,
    Convert KindIdentifier κ
  ) =>
  Substitute κ KindIdentifier (TypeScheme κ vσ p p)
  where
  substitute ux x (CoreTypeScheme p σ) = CoreTypeScheme p $ mapTypeSchemeF go go go σ
    where
      go = substitute ux x

instance FreeVariables TypeIdentifier (Type κ vσ p) where
  freeVariables (CoreType _ (TypeVariable x)) = Set.singleton x
  freeVariables (CoreType _ σ) = foldTypeF mempty freeVariables mempty freeVariables σ

instance FreeVariables TypeLogicalRaw TypeUnify where
  freeVariables (CoreType _ (TypeLogical x)) = Set.singleton x
  freeVariables (CoreType _ σ) = foldTypeF mempty go mempty go σ
    where
      go = freeVariables

instance Convert TypeIdentifier (Type κ vσ p) where
  convert ux x (CoreType p (TypeVariable x')) | x == x' = CoreType p $ TypeVariable ux
  convert ux x (CoreType p σ) = CoreType p $ mapTypeF id go id go σ
    where
      go = convert ux x

instance Substitute (Type κ vσ p) TypeIdentifier (Type κ vσ p) where
  substitute ux x (CoreType _ (TypeVariable x')) | x == x' = ux
  substitute ux x (CoreType p σ) = CoreType p $ mapTypeF id go id go σ
    where
      go = substitute ux x

instance Substitute TypeUnify TypeLogicalRaw TypeUnify where
  substitute ux x (CoreType _ (TypeLogical x')) | x == x' = ux
  substitute ux x (CoreType p σ) = CoreType p $ mapTypeF id go id go σ
    where
      go = substitute ux x

instance
  ( FreeVariables TypeIdentifier σ
  ) =>
  FreeVariables TypeIdentifier (Instantiation κ σ p)
  where
  freeVariables InstantiateEmpty = mempty
  freeVariables (InstantiateType _ σ θ) = freeVariables σ <> freeVariables θ
  freeVariables (InstantiateKind _ _ θ) = freeVariables θ

instance
  (Convert TypeIdentifier σ) =>
  Convert TypeIdentifier (Instantiation κ σ p)
  where
  convert _ _ InstantiateEmpty = InstantiateEmpty
  convert ux x (InstantiateType x' σ θ) = InstantiateType x' (convert ux x σ) (convert ux x θ)
  convert ux x (InstantiateKind x' κ θ) = InstantiateKind x' κ (convert ux x θ)

instance
  ( Substitute σ TypeIdentifier σ
  ) =>
  Substitute σ TypeIdentifier (Instantiation κ σ p)
  where
  substitute _ _ InstantiateEmpty = InstantiateEmpty
  substitute ux x (InstantiateType x' σ θ) = InstantiateType x' (substitute ux x σ) (substitute ux x θ)
  substitute ux x (InstantiateKind x' κ θ) = InstantiateKind x' κ (substitute ux x θ)

instance
  ( Convert KindIdentifier σ,
    Convert KindIdentifier κ
  ) =>
  Convert KindIdentifier (Instantiation κ σ p)
  where
  convert _ _ InstantiateEmpty = InstantiateEmpty
  convert ux x (InstantiateType x' σ θ) = InstantiateType x' (convert ux x σ) (convert ux x θ)
  convert ux x (InstantiateKind x' κ θ) = InstantiateKind x' (convert ux x κ) (convert ux x θ)

instance
  ( Substitute κ KindIdentifier κ,
    Substitute κ KindIdentifier σ
  ) =>
  Substitute κ KindIdentifier (Instantiation κ σ p)
  where
  substitute _ _ InstantiateEmpty = InstantiateEmpty
  substitute ux x (InstantiateType x' σ θ) = InstantiateType x' (substitute ux x σ) (substitute ux x θ)
  substitute ux x (InstantiateKind x' κ θ) = InstantiateKind x' (substitute ux x κ) (substitute ux x θ)

instance Substitute TypeUnify TypeLogicalRaw InstantiationUnify where
  substitute ux x (InstantiateType x' σ θ) = InstantiateType x' (substitute ux x σ) (substitute ux x θ)
  substitute ux x (InstantiateKind x' κ θ) = InstantiateKind x' κ (substitute ux x θ)
  substitute _ _ InstantiateEmpty = InstantiateEmpty

instance Substitute KindUnify KindLogicalRaw InstantiationUnify where
  substitute ux x (InstantiateType x' σ θ) = InstantiateType x' (substitute ux x σ) (substitute ux x θ)
  substitute ux x (InstantiateKind x' κ θ) = InstantiateKind x' (substitute ux x κ) (substitute ux x θ)
  substitute _ _ InstantiateEmpty = InstantiateEmpty

instance Bindings TypeIdentifier (Instantiation κ σ p) where
  bindings InstantiateEmpty = mempty
  bindings (InstantiateType x _ θ) = Set.singleton x <> bindings θ
  bindings (InstantiateKind _ _ θ) = bindings θ

instance Bindings KindIdentifier (Instantiation κ σ p) where
  bindings InstantiateEmpty = mempty
  bindings (InstantiateType _ _ θ) = bindings θ
  bindings (InstantiateKind x _ θ) = Set.singleton x <> bindings θ

instance Rename TypeIdentifier (Instantiation κ σ p) where
  rename _ _ InstantiateEmpty = InstantiateEmpty
  rename ux x (InstantiateType x' σ θ) | x == x' = InstantiateType ux σ (rename ux x θ)
  rename ux x (InstantiateType x' σ θ) = InstantiateType x' σ (rename ux x θ)
  rename ux x (InstantiateKind x' κ θ) = InstantiateKind x' κ (rename ux x θ)

instance Rename KindIdentifier (Instantiation κ σ p) where
  rename _ _ InstantiateEmpty = InstantiateEmpty
  rename ux x (InstantiateType x' σ θ) = InstantiateType x' σ (rename ux x θ)
  rename ux x (InstantiateKind x' κ θ) | x == x' = InstantiateKind ux κ (rename ux x θ)
  rename ux x (InstantiateKind x' κ θ) = InstantiateKind x' κ (rename ux x θ)

instance
  ( FreeVariables KindIdentifier κ
  ) =>
  FreeVariables KindIdentifier (Type κ vσ p)
  where
  freeVariables (CoreType _ σ) = foldTypeF mempty go go go σ
    where
      go = freeVariables

instance FreeVariables KindLogicalRaw TypeUnify where
  freeVariables (CoreType _ σ) = foldTypeF mempty go go go σ
    where
      go = freeVariables

instance
  ( Convert KindIdentifier κ
  ) =>
  Convert KindIdentifier (Type κ vσ p)
  where
  convert ux x (CoreType p σ) = CoreType p $ mapTypeF id go go go σ
    where
      go = convert ux x

instance
  ( Substitute κ KindIdentifier κ
  ) =>
  Substitute κ KindIdentifier (Type κ vσ p)
  where
  substitute ux x (CoreType p σ) = CoreType p $ mapTypeF id go go go σ
    where
      go = substitute ux x

instance Substitute KindUnify KindLogicalRaw TypeUnify where
  substitute ux x (CoreType p σ) = CoreType p $ mapTypeF id go go go σ
    where
      go = substitute ux x

instance FreeVariables TermIdentifier (Type κ v p) where
  freeVariables = mempty

instance Semigroup p => FreeVariablesPositioned TermIdentifier p (Type κ v p') where
  freeVariablesPositioned _ = mempty

instance Convert TermIdentifier (Type κ v p) where
  convert _ _ = id

instance Substitute TypeUnify x KindUnify where
  substitute _ _ = id

instance Reduce (Type κ vσ p) where
  reduce = id

instance Reduce (Instantiation κ vσ p) where
  reduce = id

instance Substitute σ x (Set Constraint) where
  substitute _ _ = id

instance Location (Type κ vσ) where
  location (CoreType p _) = p
