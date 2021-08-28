module Language.Ast.Type where

import Data.Bitraversable (bitraverse)
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.Void (Void, absurd)
import Language.Ast.Common
import Language.Ast.Kind
import Language.Ast.Sort
import Misc.Isomorph
import Misc.MonoidMap as Map
import Misc.Prism

data TypeSchemeF λκ λσ σ
  = MonoType σ
  | Forall λσ
  | KindForall λκ
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

type TypeSchemeInfer = TypeScheme (Kind Void Internal) Void Internal Internal

instance UnInfer TypeSchemeInfer (TypeSchemeAuto Internal) where
  unInfer = Just . mapTypeScheme unInfer absurd id id

data Instantiation κ σ p
  = InstantiateType TypeIdentifier σ (Instantiation κ σ p)
  | InstantiateKind KindIdentifier κ (Instantiation κ σ p)
  | InstantiateEmpty
  deriving (Show)

type InstantiationInfer = Instantiation KindInfer TypeInfer Internal

data TypeF v σ
  = TypeVariable TypeIdentifier
  | TypeExtra v
  | Macro σ σ
  | Implied σ σ
  | OfCourse σ
  | FunctionPointer σ σ
  | FunctionLiteralType σ σ
  | Copy σ
  | RuntimePair σ σ
  | RegionTransformer σ σ
  | RegionReference σ σ
  deriving (Show)

data Type κ vσ p = CoreType p (TypeF vσ (Type κ vσ p)) deriving (Show)

type TypeAuto p = Maybe (Type (KindAuto p) Void p)

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
    Forall λ -> pure Forall <*> g λ
    KindForall λ -> pure KindForall <*> f λ

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
  (σ -> m σ') ->
  TypeF v σ ->
  m (TypeF v' σ')
traverseTypeF f g σ = case σ of
  TypeVariable x -> pure TypeVariable <*> pure x
  TypeExtra v -> pure TypeExtra <*> f v
  Macro σ τ -> pure Macro <*> g σ <*> g τ
  Implied σ τ -> pure Implied <*> g σ <*> g τ
  OfCourse σ -> pure OfCourse <*> g σ
  FunctionPointer σ τ -> pure FunctionPointer <*> g σ <*> g τ
  FunctionLiteralType σ τ -> pure FunctionLiteralType <*> g σ <*> g τ
  Copy σ -> pure Copy <*> g σ
  RuntimePair σ τ -> pure RuntimePair <*> g σ <*> g τ
  RegionTransformer π σ -> pure RegionTransformer <*> g π <*> g σ
  RegionReference π σ -> pure RegionReference <*> g π <*> g σ

mapTypeF f g = runIdentity . traverseTypeF (Identity . f) (Identity . g)

foldTypeF f g = getConst . traverseTypeF (Const . f) (Const . g)

traverseType :: Applicative m => (κ -> m κ') -> (vσ -> m vσ') -> (p -> m p') -> Type κ vσ p -> m (Type κ' vσ' p')
traverseType f g h (CoreType p σ) =
  let recurse = traverseType f g h
   in pure CoreType <*> h p <*> traverseTypeF g recurse σ

mapType f g h = runIdentity . traverseType (Identity . f) (Identity . g) (Identity . h)

coreTypeScheme = Isomorph (uncurry CoreTypeScheme) $ \(CoreTypeScheme p σ) -> (p, σ)

monoType = Prism MonoType $ \case
  (MonoType σ) -> Just σ
  _ -> Nothing

forallx = Prism Forall $ \case
  (Forall λ) -> Just λ
  _ -> Nothing

kindForall = Prism KindForall $ \case
  (KindForall λ) -> Just λ
  _ -> Nothing

coreType = Isomorph (uncurry CoreType) $ \(CoreType p σ) -> (p, σ)

typeVariable = Prism TypeVariable $ \case
  (TypeVariable x) -> Just x
  _ -> Nothing

typeExtra = Prism TypeExtra $ \case
  (TypeExtra v) -> Just v
  _ -> Nothing

macro = Prism (uncurry Macro) $ \case
  (Macro σ τ) -> Just (σ, τ)
  _ -> Nothing

implied = Prism (uncurry Implied) $ \case
  (Implied σ τ) -> Just (σ, τ)
  _ -> Nothing

ofCourse = Prism OfCourse $ \case
  (OfCourse σ) -> Just σ
  _ -> Nothing

functionPointer = Prism (uncurry FunctionPointer) $ \case
  (FunctionPointer σ τs) -> Just (σ, τs)
  _ -> Nothing

functionLiteralType = Prism (uncurry FunctionLiteralType) $ \case
  (FunctionLiteralType σ τs) -> Just (σ, τs)
  _ -> Nothing

copy = Prism Copy $ \case
  (Copy σ) -> Just σ
  _ -> Nothing

runtimePair = Prism (uncurry RuntimePair) $ \case
  (RuntimePair σ τ) -> Just (σ, τ)
  _ -> Nothing

regionTransformer = Prism (uncurry RegionTransformer) $ \case
  (RegionTransformer π σ) -> Just (π, σ)
  _ -> Nothing

regionReference = Prism (uncurry RegionReference) $ \case
  (RegionReference π σ) -> Just (π, σ)
  _ -> Nothing

instance Functor (Type κ vσ) where
  fmap f = runIdentity . traverseType pure pure (Identity . f)

instance Semigroup p => FreeVariables TypeIdentifier p (TypeScheme κ vσ p p) where
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
  ( Convert KindIdentifier κ
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
  ( FreeVariablesInternal KindIdentifier κ,
    Substitute κ KindIdentifier κ,
    Convert KindIdentifier κ
  ) =>
  Substitute κ KindIdentifier (TypeScheme κ vσ p p)
  where
  substitute ux x (CoreTypeScheme p σ) = CoreTypeScheme p $ mapTypeSchemeF go go go σ
    where
      go = substitute ux x

instance Semigroup p => FreeVariables TypeIdentifier p (Type κ vσ p) where
  freeVariables (CoreType p (TypeVariable x)) = Map.singleton x p
  freeVariables (CoreType _ σ) = foldTypeF mempty freeVariables σ

instance Convert TypeIdentifier (Type κ vσ p) where
  convert ux x (CoreType p (TypeVariable x')) | x == x' = CoreType p $ TypeVariable ux
  convert ux x (CoreType p σ) = CoreType p $ mapTypeF id go σ
    where
      go = convert ux x

instance Substitute (Type κ vσ p) TypeIdentifier (Type κ vσ p) where
  substitute ux x (CoreType _ (TypeVariable x')) | x == x' = ux
  substitute ux x (CoreType p σ) = CoreType p $ mapTypeF id go σ
    where
      go = substitute ux x

instance
  ( Substitute σ TypeIdentifier σ
  ) =>
  Substitute σ TypeIdentifier (Instantiation κ σ p)
  where
  substitute _ _ InstantiateEmpty = InstantiateEmpty
  substitute ux x (InstantiateType x' σ θ) = InstantiateType x' (substitute ux x σ) (substitute ux x θ)
  substitute ux x (InstantiateKind x' κ θ) = InstantiateKind x' κ (substitute ux x θ)

instance
  ( Substitute κ KindIdentifier κ,
    Substitute κ KindIdentifier σ
  ) =>
  Substitute κ KindIdentifier (Instantiation κ σ p)
  where
  substitute _ _ InstantiateEmpty = InstantiateEmpty
  substitute ux x (InstantiateType x' σ θ) = InstantiateType x' (substitute ux x σ) (substitute ux x θ)
  substitute ux x (InstantiateKind x' κ θ) = InstantiateKind x' (substitute ux x κ) (substitute ux x θ)

instance FreeVariablesInternal TypeIdentifier (Type κ vσ p) where
  freeVariablesInternal = freeVariables . fmap (const Internal)

-- todo refill when types can contain kinds
instance FreeVariablesInternal KindIdentifier (Type κ vσ p) where
  freeVariablesInternal = mempty

instance Convert KindIdentifier (Type κ vσ p) where
  convert _ _ = id

instance Substitute κ KindIdentifier (Type κ vσ p) where
  substitute _ _ = id

instance Reduce (Type κ vσ p) where
  reduce = id

instance Reduce (Instantiation κ vσ p) where
  reduce = id

instance Location (Type κ vσ) where
  location (CoreType p _) = p
