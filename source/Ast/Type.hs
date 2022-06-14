module Ast.Type where

import Ast.Common
import Ast.Kind
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
import Misc.Explode
import Misc.Isomorph
import Misc.Prism
import qualified Misc.Util as Util

newtype TypeIdentifier = TypeIdentifier {runTypeIdentifier :: String} deriving (Show, Eq, Ord)

newtype TypeLogical = TypeLogicalRaw Int deriving (Eq, Ord, Show)

data TypeSchemeF λκς λσς σ
  = MonoType σ
  | ImplicitForall λσς
  | ImplicitKindForall λκς
  deriving (Show)

data InstantiationF κ σ θ
  = InstantiateType σ θ
  | InstantiateKind κ θ
  | InstantiateEmpty
  deriving (Show)

data Constraint
  = Copy
  deriving (Eq, Ord, Show)

data TypeF v κ λσ σ
  = TypeVariable TypeIdentifier
  | TypeLogical v
  | Inline σ σ
  | Forall λσ
  | OfCourse σ
  | FunctionPointer σ σ σ
  | FunctionLiteralType σ σ σ
  | Tuple [σ]
  | Effect σ σ
  | Unique σ
  | Shared σ σ
  | Pointer σ σ
  | Number κ κ
  | Boolean
  | World
  | Wildcard
  deriving (Show, Eq, Ord)

traverseTypeSchemeF ::
  Applicative m =>
  (λκς -> m λκς') ->
  (λσς -> m λσς') ->
  (σ -> m σ') ->
  TypeSchemeF λκς λσς σ ->
  m (TypeSchemeF λκς' λσς' σ')
traverseTypeSchemeF f g h σ =
  case σ of
    MonoType σ -> pure MonoType <*> h σ
    ImplicitForall λ -> pure ImplicitForall <*> g λ
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
  (κ -> m κ') ->
  (λσ -> m λσ') ->
  (σ -> m σ') ->
  TypeF v κ λσ σ ->
  m (TypeF v' κ' λσ' σ')
traverseTypeF f h i g σ = case σ of
  TypeVariable x -> pure TypeVariable <*> pure x
  TypeLogical v -> pure TypeLogical <*> f v
  Inline σ τ -> pure Inline <*> g σ <*> g τ
  Forall λ -> pure Forall <*> i λ
  OfCourse σ -> pure OfCourse <*> g σ
  FunctionPointer σ π τ -> pure FunctionPointer <*> g σ <*> g π <*> g τ
  FunctionLiteralType σ π τ -> pure FunctionLiteralType <*> g σ <*> g π <*> g τ
  Tuple σs -> pure Tuple <*> traverse g σs
  Effect σ π -> pure Effect <*> g σ <*> g π
  Unique σ -> pure Unique <*> g σ
  Shared σ π -> pure Shared <*> g σ <*> g π
  Pointer σ τ -> pure Pointer <*> g σ <*> g τ
  Number ρ ρ' -> pure Number <*> h ρ <*> h ρ'
  Boolean -> pure Boolean
  World -> pure World
  Wildcard -> pure Wildcard

mapTypeF f i h g = runIdentity . traverseTypeF (Identity . f) (Identity . i) (Identity . h) (Identity . g)

foldTypeF f i h g = getConst . traverseTypeF (Const . f) (Const . i) (Const . h) (Const . g)

data TypeSchemeSource p
  = TypeSchemeSource
      p
      ( TypeSchemeF
          (Bound (KindPatternSource p) (TypeSchemeSource p))
          (Bound (TypePatternSource p) (TypeSchemeSource p))
          (TypeSource p)
      )
  deriving (Show)

type TypeSchemeAuto p = Maybe (TypeSchemeSource p)

data TypeScheme vσ vκ
  = TypeSchemeCore
      ( TypeSchemeF
          (Bound KindPattern (TypeScheme vσ vκ))
          (Bound (TypePattern vσ vκ) (TypeScheme vσ vκ))
          (Type vσ vκ)
      )
  deriving (Show)

type TypeSchemeUnify = TypeScheme TypeLogical KindLogical

type TypeSchemeInfer = TypeScheme Void Void

data Instantiation vσ vκ = InstantiationCore (InstantiationF (Kind vκ) (Type vσ vκ) (Instantiation vσ vκ)) deriving (Show)

type InstantiationUnify = Instantiation TypeLogical KindLogical

type InstantiationInfer = Instantiation Void Void

data TypeSource p
  = TypeSource
      p
      ( TypeF
          Void
          (KindAuto p)
          (Bound (TypePatternSource p) (TypeSource p))
          (TypeSource p)
      )
  deriving (Show)

type TypeAuto p = Maybe (TypeSource p)

data Type vσ vκ
  = TypeCore
      ( TypeF
          vσ
          (Kind vκ)
          (Bound (TypePattern vσ vκ) (Type vσ vκ))
          (Type vσ vκ)
      )
  deriving (Show)

type TypeUnify = Type TypeLogical KindLogical

type TypeInfer = Type Void Void

data TypePatternSource p = TypePatternSource p TypeIdentifier (KindAuto p) (Set Constraint) [TypeSource p]
  deriving (Show, Functor)

data TypePatternIntermediate p
  = TypePatternIntermediate p TypeIdentifier KindUnify (Set Constraint) [TypeInfer]
  deriving (Show)

data TypePattern vσ vκ = TypePattern TypeIdentifier (Kind vκ) (Set Constraint) [Type vσ vκ] deriving (Show)

type TypePatternUnify = TypePattern KindLogical

type TypePatternInfer = TypePattern Void

typeSchemeSource = Isomorph (uncurry TypeSchemeSource) $ \(TypeSchemeSource p σ) -> (p, σ)

monoType = Prism MonoType $ \case
  (MonoType σ) -> Just σ
  _ -> Nothing

forallx = Prism ImplicitForall $ \case
  (ImplicitForall λ) -> Just λ
  _ -> Nothing

kindForall = Prism ImplicitKindForall $ \case
  (ImplicitKindForall λ) -> Just λ
  _ -> Nothing

typeSource = Isomorph (uncurry TypeSource) $ \(TypeSource p σ) -> (p, σ)

typePatternSource =
  Isomorph
    (\((((p, x), κ), c), π) -> TypePatternSource p x κ c π)
    (\(TypePatternSource p x κ c π) -> ((((p, x), κ), c), π))

typeVariable = Prism TypeVariable $ \case
  (TypeVariable x) -> Just x
  _ -> Nothing

typeExtra = Prism TypeLogical $ \case
  (TypeLogical v) -> Just v
  _ -> Nothing

inline = Prism (uncurry Inline) $ \case
  (Inline σ τ) -> Just (σ, τ)
  _ -> Nothing

explicitForall = Prism Forall $ \case
  (Forall λ) -> Just λ
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

-- n-arity tuples are supported internally but only pairs are supposed in the surface language
pair = Prism (\(σ, τ) -> Tuple [σ, τ]) $ \case
  (Tuple [σ, τ]) -> Just (σ, τ)
  _ -> Nothing

unit = Prism (const $ Tuple []) $ \case
  (Tuple []) -> Just ()
  _ -> Nothing

effect = Prism (uncurry Effect) $ \case
  (Effect σ π) -> Just (σ, π)
  _ -> Nothing

unique = Prism Unique $ \case
  (Unique σ) -> Just σ
  _ -> Nothing

shared = Prism (uncurry Shared) $ \case
  (Shared σ π) -> Just (σ, π)
  _ -> Nothing

pointer = Prism (uncurry Pointer) $ \case
  (Pointer σ τ) -> Just (σ, τ)
  _ -> Nothing

number = Prism (uncurry Number) $ \case
  (Number ρ ρ') -> Just (ρ, ρ')
  _ -> Nothing

boolean = Prism (const Boolean) $ \case
  Boolean -> Just ()
  _ -> Nothing

world = Prism (const World) $ \case
  World -> Just ()
  _ -> Nothing

wildCard = Prism (const Wildcard) $ \case
  Wildcard -> Just ()
  _ -> Nothing

typeIdentifier = Isomorph TypeIdentifier runTypeIdentifier

-- use explode for rather then order because sorting with logic variables isn't dangerous
instance (Explode vσ, Explode vκ) => Eq (Type vσ vκ) where
  TypeCore (Forall (Bound (TypePattern _ _ c _) _)) == (TypeCore (Forall (Bound (TypePattern _ _ c' _) _)))
    | c /= c' = False
  TypeCore (Forall (Bound (TypePattern _ _ _ π) _)) == (TypeCore (Forall (Bound (TypePattern _ _ _ π') _)))
    | π /= π' = False
  TypeCore (Forall (Bound (TypePattern α κ _ _) σ)) == (TypeCore (Forall (Bound (TypePattern α' κ' _ _) σ')))
    | κ == κ' = σ == convertType α α' σ'
    | otherwise = False
  TypeCore a == TypeCore b = removeBounds a == removeBounds b
    where
      removeBounds = mapTypeF id id (const ()) id

instance (Explode vσ, Explode vκ) => Ord (Type vσ vκ) where
  TypeCore (Forall (Bound (TypePattern _ _ c _) _)) `compare` (TypeCore (Forall (Bound (TypePattern _ _ c' _) _)))
    | b <- c `compare` c', b /= EQ = b
  TypeCore (Forall (Bound (TypePattern _ _ _ π) _)) `compare` (TypeCore (Forall (Bound (TypePattern _ _ _ π') _)))
    | b <- π `compare` π', b /= EQ = b
  TypeCore (Forall (Bound (TypePattern α κ _ _) σ)) `compare` (TypeCore (Forall (Bound (TypePattern α' κ' _ _) σ')))
    | b <- κ `compare` κ', b == EQ = σ `compare` convertType α α' σ'
    | otherwise = κ `compare` κ'
  TypeCore a `compare` TypeCore b = removeBounds a `compare` removeBounds b
    where
      removeBounds = mapTypeF id id (const ()) id

class FreeVariablesType u where
  freeVariablesType :: u -> Set TypeIdentifier

class ConvertType u where
  convertType :: TypeIdentifier -> TypeIdentifier -> u -> u

class SubstituteType u where
  substituteType :: Type vσ vκ -> TypeIdentifier -> u vσ vκ -> u vσ vκ

-- traverse and monadic bind
class ZonkType u where
  zonkType :: Applicative m => (vσ -> m (Type vσ' vκ)) -> u vσ vκ -> m (u vσ' vκ)

class BindingsType u where
  bindingsType :: u -> Set TypeIdentifier

class RenameType u where
  renameType :: TypeIdentifier -> TypeIdentifier -> u -> u

freeVariablesHigherType = freeVariablesHigher freeVariablesType freeVariablesType

convertHigherType = substituteHigher convertType convertType

substituteHigherType = substituteHigher substituteType substituteType

freeVariablesSameType = freeVariablesSame bindingsType freeVariablesType

convertSameType = substituteDependent avoidTypeConvert convertType convertType

substituteSameType = substituteDependent avoidType substituteType substituteType

freeVariablesLowerType = freeVariablesLower freeVariablesType

convertLowerType = convertLower convertType

substituteLowerType avoid = substituteLower avoid substituteType

freeVariablesRgnForType = freeVariablesSame bindingsType freeVariablesHigherType

convertRgnForType = substituteDependent (avoidTypeConvert' convertHigherType) convertType convertHigherType

substituteRgnForType = substituteDependent (avoidType' convertHigherType) substituteType substituteHigherType

avoidType = avoidType' convertType

avoidType' = Avoid bindingsType renameType freeVariablesType

avoidTypeConvert = avoidTypeConvert' convertType

avoidTypeConvert' = Avoid bindingsType renameType Set.singleton

toTypePattern (TypePatternIntermediate _ x κ c π) = TypePattern x κ c (map flexible π)

instance Fresh TypeIdentifier where
  fresh c (TypeIdentifier x) = TypeIdentifier $ Util.fresh (Set.mapMonotonic runTypeIdentifier c) x

instance Functor TypeSchemeSource where
  fmap f (TypeSchemeSource p ς) =
    TypeSchemeSource (f p) $
      mapTypeSchemeF
        (mapBound (fmap f) (fmap f))
        (mapBound (fmap f) (fmap f))
        (fmap f)
        ς

instance Functor TypeSource where
  fmap f (TypeSource p σ) =
    TypeSource (f p) $
      mapTypeF
        id
        (fmap (fmap f))
        (mapBound (fmap f) (fmap f))
        (fmap f)
        σ

instance BindingsType (TypePatternSource p) where
  bindingsType (TypePatternSource _ x _ _ _) = Set.singleton x

instance RenameType (TypePatternSource p) where
  renameType ux x (TypePatternSource p x' κ c π) | x == x' = TypePatternSource p ux κ c π
  renameType _ _ λ = λ

instance BindingsType (TypePattern vσ vκ) where
  bindingsType (TypePattern x _ _ _) = Set.singleton x

instance RenameType (TypePattern vσ vκ) where
  renameType ux x (TypePattern x' κ c π) | x == x' = TypePattern ux κ c π
  renameType _ _ λ = λ

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
  freeVariablesType (TypeCore σ) = foldTypeF mempty mempty go' go σ
    where
      go = freeVariablesType
      go' = freeVariablesSameType

instance ConvertType (TypeSource p) where
  convertType ux x (TypeSource p (TypeVariable x')) | x == x' = TypeSource p $ TypeVariable ux
  convertType ux x (TypeSource p σ) = TypeSource p $ mapTypeF id id go' go σ
    where
      go = convertType ux x
      go' = convertSameType ux x

instance ConvertType (Type vσ vκ) where
  convertType ux x (TypeCore (TypeVariable x')) | x == x' = TypeCore $ TypeVariable ux
  convertType ux x (TypeCore σ) = TypeCore $ mapTypeF id id go' go σ
    where
      go = convertType ux x
      go' = convertSameType ux x

instance SubstituteType (Type) where
  substituteType ux x (TypeCore (TypeVariable x')) | x == x' = ux
  substituteType ux x (TypeCore σ) = TypeCore $ mapTypeF id id go' go σ
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

instance FreeVariablesType (TypePattern vσ vκ) where
  freeVariablesType (TypePattern _ _ _ π) = foldMap freeVariablesType π

instance ConvertType (TypePatternSource p) where
  convertType ux x (TypePatternSource p x' κ c π) = TypePatternSource p x' κ c (map (convertType ux x) π)

instance ConvertType (TypePattern vσ vκ) where
  convertType ux x (TypePattern x' κ c π) = TypePattern x' κ c (map (convertType ux x) π)

instance SubstituteType TypePattern where
  substituteType ux x (TypePattern x' κ c π) = TypePattern x' κ c (map (substituteType ux x) π)

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
  freeVariablesKind (TypeCore σ) = foldTypeF mempty go go' go σ
    where
      go = freeVariablesKind
      go' = freeVariablesHigherKind

instance ConvertKind (Type vσ vκ) where
  convertKind ux x (TypeCore σ) = TypeCore $ mapTypeF id go go' go σ
    where
      go = convertKind ux x
      go' = convertHigherKind ux x

instance SubstituteKind (Type vσ) where
  substituteKind ux x (TypeCore σ) = TypeCore $ mapTypeF id go go' go σ
    where
      go = substituteKind ux x
      go' = substituteHigherKind ux x

instance FreeVariablesKind (TypePattern vσ vκ) where
  freeVariablesKind (TypePattern _ κ _ π) = freeVariablesKind κ <> foldMap freeVariablesKind π

instance ConvertKind (TypePattern vσ vκ) where
  convertKind ux x (TypePattern x' κ c π) =
    TypePattern x' (convertKind ux x κ) c (map (convertKind ux x) π)

instance SubstituteKind (TypePattern vσ) where
  substituteKind ux x (TypePattern x' κ c π) =
    TypePattern x' (substituteKind ux x κ) c (map (substituteKind ux x) π)

instance ZonkType Type where
  zonkType f (TypeCore (TypeLogical v)) = f v
  zonkType f (TypeCore σ) =
    pure TypeCore
      <*> traverseTypeF
        (error "handled manually")
        pure
        (traverseBound (zonkType f) (zonkType f))
        (zonkType f)
        σ

instance ZonkType TypeScheme where
  zonkType f (TypeSchemeCore ς) =
    pure TypeSchemeCore
      <*> traverseTypeSchemeF
        (traverseBound pure (zonkType f))
        (traverseBound (zonkType f) (zonkType f))
        (zonkType f)
        ς

instance ZonkType Instantiation where
  zonkType f (InstantiationCore θ) =
    pure InstantiationCore
      <*> traverseInstantiationF pure (zonkType f) (zonkType f) θ

instance ZonkType TypePattern where
  zonkType f (TypePattern x κ c π) =
    pure TypePattern <*> pure x <*> pure κ <*> pure c <*> traverse (zonkType f) π

instance ZonkKind (Type vσ) where
  zonkKind f (TypeCore σ) =
    pure TypeCore
      <*> traverseTypeF
        pure
        (zonkKind f)
        (traverseBound (zonkKind f) (zonkKind f))
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

instance ZonkKind (TypePattern vσ) where
  zonkKind f (TypePattern x κ c π) =
    pure TypePattern <*> pure x <*> zonkKind f κ <*> pure c <*> traverse (zonkKind f) π

instance Reduce (Instantiation vσ vκ) where
  reduce (InstantiationCore θ) = InstantiationCore $ mapInstantiationF reduce reduce reduce θ

instance Reduce (Type vσ vκ) where
  reduce = id

instance Location TypeSource where
  location (TypeSource p _) = p

instance Reduce (TypePattern vσ vκ) where
  reduce (TypePattern x κ c π) = TypePattern x (reduce κ) c (map reduce π)

freeTypeLogical = getConst . zonkType (Const . Set.singleton)

sourceType :: Monoid p => Type Void Void -> TypeSource p
sourceType (TypeCore σ) =
  TypeSource mempty $
    mapTypeF
      id
      sourceKindAuto
      (mapBound sourceTypePattern sourceType)
      sourceType
      σ

sourceTypeAuto = Just . sourceType

sourceTypePattern (TypePattern x κ c π) = TypePatternSource mempty x (sourceKindAuto κ) c (map sourceType π)

sourceTypeScheme :: Monoid p => TypeScheme Void Void -> TypeSchemeSource p
sourceTypeScheme (TypeSchemeCore ς) =
  TypeSchemeSource mempty $
    mapTypeSchemeF
      (mapBound sourceKindPattern sourceTypeScheme)
      (mapBound sourceTypePattern sourceTypeScheme)
      sourceType
      ς

flexibleType = runIdentity . zonkType absurd

flexible = flexibleType . flexibleKind
