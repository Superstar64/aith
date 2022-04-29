module Ast.Type where

import Ast.Common
import Ast.Kind
import Ast.Sort
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
import Misc.Isomorph
import Misc.Prism
import qualified Misc.Util as Util

newtype TypeIdentifier = TypeIdentifier {runTypeIdentifier :: String} deriving (Show, Eq, Ord)

newtype TypeLogical = TypeLogicalRaw Int deriving (Eq, Ord, Show)

data TypeSchemeF λκ λσ σ ς
  = MonoType σ
  | -- bounded, constraints, lower bounds
    ImplicitForall (λσ ς) (Set Constraint) [σ]
  | ImplicitKindForall (λκ ς)
  deriving (Show)

data InstantiationF κ σ θ
  = InstantiateType σ θ
  | InstantiateKind κ θ
  | InstantiateEmpty
  deriving (Show)

data Constraint
  = Copy
  deriving (Eq, Ord, Show)

data TypeF v λ κ σ
  = TypeVariable TypeIdentifier
  | TypeLogical v
  | Inline σ σ
  | Forall (λ σ) (Set Constraint) [σ]
  | OfCourse σ
  | FunctionPointer σ σ σ
  | FunctionLiteralType σ σ σ
  | Pair σ σ
  | Effect σ σ
  | Reference σ σ
  | Number κ κ
  deriving (Show)

traverseTypeSchemeF ::
  Applicative m =>
  (λκ ς -> m (λκ' ς')) ->
  (λσ ς -> m (λσ' ς')) ->
  (σ -> m σ') ->
  TypeSchemeF λκ λσ σ ς ->
  m (TypeSchemeF λκ' λσ' σ' ς')
traverseTypeSchemeF f g h σ =
  case σ of
    MonoType σ -> pure MonoType <*> h σ
    ImplicitForall λ c π -> pure ImplicitForall <*> g λ <*> pure c <*> traverse h π
    ImplicitKindForall λ -> pure ImplicitKindForall <*> f λ

mapTypeSchemeF f g h = runIdentity . traverseTypeSchemeF (Identity . f) (Identity . g) (Identity . h)

foldTypeSchemeF f g h = getConst . traverseTypeSchemeF (Const . f) (Const . g) (Const . h)

traverseInstantiationF ::
  Applicative m =>
  (κ -> m κ') ->
  (σ -> m σ') ->
  (θ -> m θ') ->
  (InstantiationF κ σ θ) ->
  m (InstantiationF κ' σ' θ')
traverseInstantiationF f g h θ = case θ of
  InstantiateEmpty -> pure InstantiateEmpty
  InstantiateKind κ θ -> pure InstantiateKind <*> f κ <*> h θ
  InstantiateType σ θ -> pure InstantiateType <*> g σ <*> h θ

mapInstantiationF f g h = runIdentity . traverseInstantiationF (Identity . f) (Identity . g) (Identity . h)

foldInstantiationF f g h = getConst . traverseInstantiationF (Const . f) (Const . g) (Const . h)

traverseTypeF ::
  Applicative m =>
  (v -> m v') ->
  (λ σ -> m (λ' σ')) ->
  (κ -> m κ') ->
  (σ -> m σ') ->
  TypeF v λ κ σ ->
  m (TypeF v' λ' κ' σ')
traverseTypeF f i h g σ = case σ of
  TypeVariable x -> pure TypeVariable <*> pure x
  TypeLogical v -> pure TypeLogical <*> f v
  Inline σ τ -> pure Inline <*> g σ <*> g τ
  Forall λ c π -> pure Forall <*> i λ <*> pure c <*> traverse g π
  OfCourse σ -> pure OfCourse <*> g σ
  FunctionPointer σ π τ -> pure FunctionPointer <*> g σ <*> g π <*> g τ
  FunctionLiteralType σ π τ -> pure FunctionLiteralType <*> g σ <*> g π <*> g τ
  Pair σ τ -> pure Pair <*> g σ <*> g τ
  Effect π σ -> pure Effect <*> g π <*> g σ
  Reference π σ -> pure Reference <*> g π <*> g σ
  Number ρ ρ' -> pure Number <*> h ρ <*> h ρ'

mapTypeF f i h g = runIdentity . traverseTypeF (Identity . f) (Identity . i) (Identity . h) (Identity . g)

foldTypeF f i h g = getConst . traverseTypeF (Const . f) (Const . i) (Const . h) (Const . g)

data TypeSchemeSource p
  = TypeSchemeSource
      p
      ( TypeSchemeF
          (Bound (Pattern KindIdentifier Sort p))
          (Bound (Pattern TypeIdentifier (KindAuto p) p))
          (TypeSource p)
          (TypeSchemeSource p)
      )
  deriving (Show)

type TypeSchemeAuto p = Maybe (TypeSchemeSource p)

data TypeScheme vσ vκ
  = TypeSchemeCore
      ( TypeSchemeF
          (Bound KindPattern)
          (Bound (TypePattern vκ))
          (Type vσ vκ)
          (TypeScheme vσ vκ)
      )
  deriving (Show)

type TypeSchemeUnify = TypeScheme TypeLogical KindLogical

type TypeSchemeInfer = TypeScheme Void Void

data Instantiation vσ vκ = InstantiationCore (InstantiationF (Kind vκ) (Type vσ vκ) (Instantiation vσ vκ)) deriving (Show)

type InstantiationUnify = Instantiation TypeLogical KindLogical

type InstantiationInfer = Instantiation Void Void

data TypeSource p = TypeSource p (TypeF Void (Bound (Pattern TypeIdentifier (KindAuto p) p)) (KindAuto p) (TypeSource p)) deriving (Show)

type TypeAuto p = Maybe (TypeSource p)

data Type vσ vκ = TypeCore (TypeF vσ (Bound (TypePattern vκ)) (Kind vκ) (Type vσ vκ)) deriving (Show)

type TypeUnify = Type TypeLogical KindLogical

type TypeInfer = Type Void Void

data TypePattern v = TypePatternCore TypeIdentifier (Kind v) deriving (Show)

type TypePatternUnify = TypePattern KindLogical

type TypePatternInfer = TypePattern Void

typeSchemeSource = Isomorph (uncurry TypeSchemeSource) $ \(TypeSchemeSource p σ) -> (p, σ)

monoType = Prism MonoType $ \case
  (MonoType σ) -> Just σ
  _ -> Nothing

forallx = Prism (uncurry $ uncurry ImplicitForall) $ \case
  (ImplicitForall λ c π) -> Just ((λ, c), π)
  _ -> Nothing

kindForall = Prism ImplicitKindForall $ \case
  (ImplicitKindForall λ) -> Just λ
  _ -> Nothing

typeSource = Isomorph (uncurry TypeSource) $ \(TypeSource p σ) -> (p, σ)

typeVariable = Prism TypeVariable $ \case
  (TypeVariable x) -> Just x
  _ -> Nothing

typeExtra = Prism TypeLogical $ \case
  (TypeLogical v) -> Just v
  _ -> Nothing

inline = Prism (uncurry Inline) $ \case
  (Inline σ τ) -> Just (σ, τ)
  _ -> Nothing

explicitForall = Prism (uncurry $ uncurry Forall) $ \case
  (Forall λ c π) -> Just ((λ, c), π)
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

typeIdentifier = Isomorph TypeIdentifier runTypeIdentifier

class FreeVariablesType u where
  freeVariablesType :: u -> Set TypeIdentifier

class ConvertType u where
  convertType :: TypeIdentifier -> TypeIdentifier -> u -> u

class SubstituteType u where
  substituteType :: Type vσ vκ -> TypeIdentifier -> u vσ vκ -> u vσ vκ

-- traverse and monadic bind
class ZonkType u where
  zonkType :: Applicative m => (vσ -> m (Type vσ' vκ)) -> u vσ vκ -> m (u vσ' vκ)

bindingsType (TypePatternCore x _) = Set.singleton x

renameType ux x (TypePatternCore x' κ) | x == x' = TypePatternCore ux κ
renameType _ _ λ@(TypePatternCore _ _) = λ

freeVariablesHigherType = freeVariablesHigher' freeVariablesType freeVariablesType

convertHigherType = substituteHigher' convertType convertType

substituteHigherType = substituteHigher' substituteType substituteType

freeVariablesSameType = freeVariablesSame' freeVariablesType bindingsType

convertSameType = substituteSame' convertType avoidTypeConvert

substituteSameType = substituteSame' substituteType avoidType

freeVariablesLowerType = freeVariablesLower' freeVariablesType

convertLowerType = convertLower' convertType

substituteLowerType avoid = substituteLower' substituteType avoid

avoidType = Avoid bindingsType renameType freeVariablesType convertType

avoidTypeConvert = Avoid bindingsType renameType Set.singleton convertType

freeVariablesSameTypeSource = freeVariablesSame' freeVariablesType bindings'

convertSameTypeSource = substituteSame' convertType avoidTypeSource

avoidTypeSource = Avoid bindings' rename' Set.singleton convertType

toTypePattern (Pattern _ x κ) = TypePatternCore x κ

instance Fresh TypeIdentifier where
  fresh c (TypeIdentifier x) = TypeIdentifier $ Util.fresh (Set.mapMonotonic runTypeIdentifier c) x

instance Functor TypeSchemeSource where
  fmap f (TypeSchemeSource p ς) =
    TypeSchemeSource (f p) $
      mapTypeSchemeF
        (mapBound (mapPattern id id f) (fmap f))
        (mapBound (mapPattern id (fmap (fmap f)) f) (fmap f))
        (fmap f)
        ς

instance Functor TypeSource where
  fmap f (TypeSource p σ) =
    TypeSource (f p) $
      mapTypeF
        id
        (mapBound (mapPattern id (fmap (fmap f)) f) (fmap f))
        (fmap (fmap f))
        (fmap f)
        σ

instance ConvertType σ => ConvertType (Maybe σ) where
  convertType ux x σ = fmap (convertType ux x) σ

instance FreeVariablesType (TypeScheme vσ vκ) where
  freeVariablesType (TypeSchemeCore σ) = foldTypeSchemeF go'' go' go σ
    where
      go = freeVariablesType
      go' = freeVariablesSameType
      go'' = freeVariablesLowerType

instance ConvertType (TypeScheme vσ vκ) where
  convertType ux x (TypeSchemeCore σ) = TypeSchemeCore $ mapTypeSchemeF go'' go' go σ
    where
      go = convertType ux x
      go' = convertSameType ux x
      go'' = convertLowerType ux x

instance SubstituteType TypeScheme where
  substituteType ux x (TypeSchemeCore σ) = TypeSchemeCore $ mapTypeSchemeF go'' go' go σ
    where
      go = substituteType ux x
      go' = substituteSameType ux x
      go'' = substituteLowerType avoidKind ux x

instance ConvertKind (TypeScheme vσ vκ) where
  convertKind ux x (TypeSchemeCore σ) = TypeSchemeCore $ mapTypeSchemeF go'' go' go σ
    where
      go = convertKind ux x
      go' = convertHigherKind ux x
      go'' = convertSameKind ux x

instance SubstituteKind (TypeScheme vσ) where
  substituteKind ux x (TypeSchemeCore σ) = TypeSchemeCore $ mapTypeSchemeF go'' go' go σ
    where
      go = substituteKind ux x
      go' = substituteHigherKind ux x
      go'' = substituteSameKind ux x

instance FreeVariablesType (Type vσ vκ) where
  freeVariablesType (TypeCore (TypeVariable x)) = Set.singleton x
  freeVariablesType (TypeCore σ) = foldTypeF mempty go' mempty go σ
    where
      go = freeVariablesType
      go' = freeVariablesSameType

instance ConvertType (TypeSource p) where
  convertType ux x (TypeSource p (TypeVariable x')) | x == x' = TypeSource p $ TypeVariable ux
  convertType ux x (TypeSource p σ) = TypeSource p $ mapTypeF id go' id go σ
    where
      go = convertType ux x
      go' = convertSameTypeSource ux x

instance ConvertType (Type vσ vκ) where
  convertType ux x (TypeCore (TypeVariable x')) | x == x' = TypeCore $ TypeVariable ux
  convertType ux x (TypeCore σ) = TypeCore $ mapTypeF id go' id go σ
    where
      go = convertType ux x
      go' = convertSameType ux x

instance SubstituteType (Type) where
  substituteType ux x (TypeCore (TypeVariable x')) | x == x' = ux
  substituteType ux x (TypeCore σ) = TypeCore $ mapTypeF id go' id go σ
    where
      go = substituteType ux x
      go' = substituteSameType ux x

instance FreeVariablesType (Instantiation vσ vκ) where
  freeVariablesType (InstantiationCore θ) = foldInstantiationF mempty go go θ
    where
      go = freeVariablesType

instance ConvertType (Instantiation vσ vκ) where
  convertType ux x (InstantiationCore θ) = InstantiationCore $ mapInstantiationF id go go θ
    where
      go = convertType ux x

instance SubstituteType (Instantiation) where
  substituteType ux x (InstantiationCore θ) = InstantiationCore $ mapInstantiationF id go go θ
    where
      go = substituteType ux x

instance FreeVariablesKind (Instantiation vσ vκ) where
  freeVariablesKind (InstantiationCore θ) = foldInstantiationF go go go θ
    where
      go = freeVariablesKind

instance ConvertKind (Instantiation vσ vκ) where
  convertKind ux x (InstantiationCore θ) = InstantiationCore $ mapInstantiationF go go go θ
    where
      go = convertKind ux x

instance SubstituteKind (Instantiation vσ) where
  substituteKind ux x (InstantiationCore θ) = InstantiationCore $ mapInstantiationF go go go θ
    where
      go = substituteKind ux x

instance FreeVariablesKind (Type vσ vκ) where
  freeVariablesKind (TypeCore σ) = foldTypeF mempty go' go go σ
    where
      go = freeVariablesKind
      go' = freeVariablesHigherKind

instance ConvertKind (Type vσ vκ) where
  convertKind ux x (TypeCore σ) = TypeCore $ mapTypeF id go' go go σ
    where
      go = convertKind ux x
      go' = convertHigherKind ux x

instance SubstituteKind (Type vσ) where
  substituteKind ux x (TypeCore σ) = TypeCore $ mapTypeF id go' go go σ
    where
      go = substituteKind ux x
      go' = substituteHigherKind ux x

instance FreeVariablesKind (TypePattern vκ) where
  freeVariablesKind (TypePatternCore _ κ) = freeVariablesKind κ

instance ConvertKind (TypePattern vκ) where
  convertKind ux x (TypePatternCore x' κ) = TypePatternCore x' (convertKind ux x κ)

instance SubstituteKind TypePattern where
  substituteKind ux x (TypePatternCore x' κ) = TypePatternCore x' (substituteKind ux x κ)

instance ZonkType Type where
  zonkType f (TypeCore (TypeLogical v)) = f v
  zonkType f (TypeCore σ) =
    pure TypeCore
      <*> traverseTypeF
        (error "handled manually")
        (traverseBound pure (zonkType f))
        pure
        (zonkType f)
        σ

instance ZonkType TypeScheme where
  zonkType f (TypeSchemeCore ς) =
    pure TypeSchemeCore
      <*> traverseTypeSchemeF
        (traverseBound pure (zonkType f))
        (traverseBound pure (zonkType f))
        (zonkType f)
        ς

instance ZonkType Instantiation where
  zonkType f (InstantiationCore θ) =
    pure InstantiationCore
      <*> traverseInstantiationF pure (zonkType f) (zonkType f) θ

instance ZonkKind (Type vσ) where
  zonkKind f (TypeCore σ) =
    pure TypeCore
      <*> traverseTypeF
        pure
        (traverseBound (zonkKind f) (zonkKind f))
        (zonkKind f)
        (zonkKind f)
        σ

instance ZonkKind (TypeScheme vσ) where
  zonkKind f (TypeSchemeCore ς) =
    pure TypeSchemeCore
      <*> traverseTypeSchemeF
        (traverseBound pure (zonkKind f))
        (traverseBound (zonkKind f) (zonkKind f))
        (zonkKind f)
        ς

instance ZonkKind (Instantiation vσ) where
  zonkKind f (InstantiationCore θ) =
    pure InstantiationCore
      <*> traverseInstantiationF (zonkKind f) (zonkKind f) (zonkKind f) θ

instance ZonkKind (TypePattern) where
  zonkKind f (TypePatternCore x κ) = pure TypePatternCore <*> pure x <*> zonkKind f κ

instance Reduce (Instantiation vσ vκ) where
  reduce (InstantiationCore θ) = InstantiationCore $ mapInstantiationF reduce reduce reduce θ

instance Reduce (Type vσ vκ) where
  reduce = id

instance Location TypeSource where
  location (TypeSource p _) = p

instance Reduce (TypePattern vκ) where
  reduce (TypePatternCore x κ) = TypePatternCore x (reduce κ)

freeVariablesLogical :: TypeUnify -> Set TypeLogical
freeVariablesLogical = getConst . zonkType (Const . Set.singleton)

sourceType :: Monoid p => Type Void Void -> TypeSource p
sourceType (TypeCore σ) =
  TypeSource mempty $
    mapTypeF
      id
      (mapBound sourceTypePattern sourceType)
      sourceKindAuto
      sourceType
      σ

sourceTypeAuto = Just . sourceType

sourceTypePattern (TypePatternCore x κ) = Pattern mempty x (sourceKindAuto κ)

sourceTypeScheme :: Monoid p => TypeScheme Void Void -> TypeSchemeSource p
sourceTypeScheme (TypeSchemeCore ς) =
  TypeSchemeSource mempty $
    mapTypeSchemeF
      (mapBound sourceKindPattern sourceTypeScheme)
      (mapBound sourceTypePattern sourceTypeScheme)
      sourceType
      ς

flexibleType = runIdentity . zonkType absurd
