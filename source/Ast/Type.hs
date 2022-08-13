module Ast.Type where

import Ast.Common
import Control.Category ((.))
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
import Misc.Isomorph
import Misc.Prism
import qualified Misc.Util as Util
import Prelude hiding ((.))

newtype TypeIdentifier = TypeIdentifier {runTypeIdentifier :: String} deriving (Show, Eq, Ord)

newtype TypeLogical = TypeLogicalRaw Int deriving (Eq, Ord, Show)

data TypeSchemeF λσς σ
  = MonoType σ
  | TypeForall λσς
  deriving (Show)

data InstantiationF σ θ
  = InstantiateType σ θ
  | InstantiateEmpty
  deriving (Show)

data Constraint
  = Copy
  deriving (Eq, Ord, Show)

data TypeSub
  = TypeVariable TypeIdentifier
  | World
  deriving (Show, Eq, Ord)

data KindSize
  = Byte
  | Short
  | Int
  | Long
  | Native
  deriving (Show, Eq, Ord)

data KindSignedness
  = Signed
  | Unsigned
  deriving (Show, Eq, Ord)

data KindRuntime s κ
  = PointerRep
  | StructRep [κ]
  | WordRep s
  deriving (Show, Eq, Ord)

data Top σ
  = Kind σ σ
  | Invariant
  | Subtypable
  | Transparent
  | Opaque
  deriving (Show)

data TypeF v λσ σ
  = TypeSub TypeSub
  | TypeLogical v
  | Inline σ σ
  | Poly λσ
  | OfCourse σ
  | FunctionPointer σ σ σ
  | FunctionLiteralType σ σ σ
  | Tuple [σ]
  | Effect σ σ
  | Unique σ
  | Shared σ σ
  | Pointer σ
  | Array σ
  | Number σ σ
  | Boolean
  | Type
  | Region
  | Pretype σ
  | Boxed
  | KindRuntime (KindRuntime σ σ)
  | KindSize (KindSize)
  | KindSignedness (KindSignedness)
  | Representation
  | Size
  | Signedness
  | Top (Top σ)
  deriving (Show)

traverseTypeSchemeF ::
  Applicative m =>
  (λσς -> m λσς') ->
  (σ -> m σ') ->
  TypeSchemeF λσς σ ->
  m (TypeSchemeF λσς' σ')
traverseTypeSchemeF g h σ =
  case σ of
    MonoType σ -> pure MonoType <*> h σ
    TypeForall λ -> pure TypeForall <*> g λ

mapTypeSchemeF g h = runIdentity . traverseTypeSchemeF (Identity . g) (Identity . h)

foldTypeSchemeF g h = getConst . traverseTypeSchemeF (Const . g) (Const . h)

traverseInstantiationF ::
  Applicative m =>
  (σ -> m σ') ->
  (θ -> m θ') ->
  (InstantiationF σ θ) ->
  m (InstantiationF σ' θ')
traverseInstantiationF f h θ = case θ of
  InstantiateEmpty -> pure InstantiateEmpty
  InstantiateType σ θ -> pure InstantiateType <*> f σ <*> h θ

mapInstantiationF f h = runIdentity . traverseInstantiationF (Identity . f) (Identity . h)

foldInstantiationF f h = getConst . traverseInstantiationF (Const . f) (Const . h)

traverseTop ::
  Applicative m =>
  (σ -> m σ') ->
  Top σ ->
  m (Top σ')
traverseTop f σ = case σ of
  Kind σ τ -> pure Kind <*> f σ <*> f τ
  Invariant -> pure Invariant
  Subtypable -> pure Subtypable
  Opaque -> pure Opaque
  Transparent -> pure Transparent

traverseTypeF ::
  Applicative m =>
  (v -> m v') ->
  (λσ -> m λσ') ->
  (σ -> m σ') ->
  TypeF v λσ σ ->
  m (TypeF v' λσ' σ')
traverseTypeF f i g σ = case σ of
  TypeSub (TypeVariable x) -> pure (TypeSub $ TypeVariable x)
  TypeLogical v -> pure TypeLogical <*> f v
  Inline σ τ -> pure Inline <*> g σ <*> g τ
  Poly λ -> pure Poly <*> i λ
  OfCourse σ -> pure OfCourse <*> g σ
  FunctionPointer σ π τ -> pure FunctionPointer <*> g σ <*> g π <*> g τ
  FunctionLiteralType σ π τ -> pure FunctionLiteralType <*> g σ <*> g π <*> g τ
  Tuple σs -> pure Tuple <*> traverse g σs
  Effect σ π -> pure Effect <*> g σ <*> g π
  Unique σ -> pure Unique <*> g σ
  Shared σ π -> pure Shared <*> g σ <*> g π
  Pointer σ -> pure Pointer <*> g σ
  Array σ -> pure Array <*> g σ
  Number ρ ρ' -> pure Number <*> g ρ <*> g ρ'
  Boolean -> pure Boolean
  TypeSub World -> pure (TypeSub World)
  Type -> pure Type
  Region -> pure Region
  (Pretype κ) -> pure Pretype <*> g κ
  Boxed -> pure Boxed
  KindRuntime PointerRep -> pure (KindRuntime PointerRep)
  KindRuntime (StructRep κs) -> pure (KindRuntime . StructRep) <*> traverse g κs
  KindRuntime (WordRep s) -> pure (KindRuntime . WordRep) <*> g s
  KindSize s -> pure (KindSize s)
  KindSignedness s -> pure (KindSignedness s)
  Representation -> pure Representation
  Size -> pure Size
  Signedness -> pure Signedness
  Top μ -> Top <$> traverseTop g μ

mapTypeF f h g = runIdentity . traverseTypeF (Identity . f) (Identity . h) (Identity . g)

foldTypeF f h g = getConst . traverseTypeF (Const . f) (Const . h) (Const . g)

data TypeSchemeSource p
  = TypeSchemeSource
      p
      ( TypeSchemeF
          (Bound (TypePatternSource p) (TypeSchemeSource p))
          (TypeSource p)
      )
  deriving (Show)

type TypeSchemeAuto p = Maybe (TypeSchemeSource p)

data TypeScheme v
  = TypeSchemeCore
      ( TypeSchemeF
          (Bound (TypePattern v) (TypeScheme v))
          (Type v)
      )
  deriving (Show)

type TypeSchemeUnify = TypeScheme TypeLogical

type TypeSchemeInfer = TypeScheme Void

data Instantiation v = InstantiationCore (InstantiationF (Type v) (Instantiation v)) deriving (Show)

type InstantiationUnify = Instantiation TypeLogical

type InstantiationInfer = Instantiation Void

data TypeSource p
  = TypeSource
      p
      ( TypeF
          Void
          (TypeSchemeSource p)
          (TypeSource p)
      )
  deriving (Show)

type TypeAuto p = Maybe (TypeSource p)

data Type v
  = TypeCore
      ( TypeF
          v
          (TypeScheme v)
          (Type v)
      )
  deriving (Show)

type TypeUnify = Type TypeLogical

type TypeInfer = Type Void

data TypePatternSource p = TypePatternSource p TypeIdentifier (TypeSource p) (Set Constraint) [TypeSource p]
  deriving (Show, Functor)

data TypePatternIntermediate p
  = TypePatternIntermediate p TypeIdentifier TypeInfer (Set Constraint) [TypeSub]
  deriving (Show)

data TypePattern v = TypePattern TypeIdentifier (Type v) (Set Constraint) [Type v] deriving (Show)

type TypePatternUnify = TypePattern TypeLogical

type TypePatternInfer = TypePattern Void

typeSchemeSource = Isomorph (uncurry TypeSchemeSource) $ \(TypeSchemeSource p σ) -> (p, σ)

monoType = Prism MonoType $ \case
  (MonoType σ) -> Just σ
  _ -> Nothing

typeForall = Prism TypeForall $ \case
  (TypeForall λ) -> Just λ
  _ -> Nothing

kindRuntime = Prism KindRuntime $ \case
  (KindRuntime κ) -> Just κ
  _ -> Nothing

kindSize = Prism KindSize $ \case
  (KindSize κ) -> Just κ
  _ -> Nothing

kindSignedness = Prism KindSignedness $ \case
  (KindSignedness κ) -> Just κ
  _ -> Nothing

typeSource = Isomorph (uncurry TypeSource) $ \(TypeSource p σ) -> (p, σ)

typePatternSource =
  Isomorph
    (\((((p, x), κ), c), π) -> TypePatternSource p x κ c π)
    (\(TypePatternSource p x κ c π) -> ((((p, x), κ), c), π))

typeSub = Prism TypeSub $ \case
  (TypeSub σ) -> Just σ
  _ -> Nothing

typeVariable = (typeSub .) $
  Prism TypeVariable $ \case
    (TypeVariable x) -> Just x
    _ -> Nothing

typeExtra = Prism TypeLogical $ \case
  (TypeLogical v) -> Just v
  _ -> Nothing

inline = Prism (uncurry Inline) $ \case
  (Inline σ τ) -> Just (σ, τ)
  _ -> Nothing

poly = Prism Poly $ \case
  (Poly λ) -> Just λ
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

tuple = Prism Tuple $ \case
  Tuple σ -> Just σ
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

pointer = Prism Pointer $ \case
  (Pointer σ) -> Just σ
  _ -> Nothing

array = Prism Array $ \case
  (Array σ) -> Just σ
  _ -> Nothing

number = Prism (uncurry Number) $ \case
  (Number ρ ρ') -> Just (ρ, ρ')
  _ -> Nothing

boolean = Prism (const Boolean) $ \case
  Boolean -> Just ()
  _ -> Nothing

world = (typeSub .) $
  Prism (const World) $ \case
    World -> Just ()
    _ -> Nothing

typeIdentifier = Isomorph TypeIdentifier runTypeIdentifier

typex = Prism (const Type) $ \case
  Type -> Just ()
  _ -> Nothing

region = Prism (const Region) $ \case
  Region -> Just ()
  _ -> Nothing

pretype = Prism Pretype $ \case
  Pretype κ -> Just κ
  _ -> Nothing

boxed = Prism (const Boxed) $ \case
  Boxed -> pure ()
  _ -> Nothing

pointerRep = (kindRuntime .) $
  Prism (const PointerRep) $ \case
    PointerRep -> Just ()
    _ -> Nothing

structRep = (kindRuntime .) $
  Prism StructRep $ \case
    (StructRep ρs) -> Just ρs
    _ -> Nothing

wordRep = (kindRuntime .) $
  Prism WordRep $ \case
    (WordRep κ) -> Just κ
    _ -> Nothing

byte = (kindSize .) $
  Prism (const Byte) $ \case
    Byte -> Just ()
    _ -> Nothing

short = (kindSize .) $
  Prism (const Short) $ \case
    Short -> Just ()
    _ -> Nothing

int = (kindSize .) $
  Prism (const Int) $ \case
    Int -> Just ()
    _ -> Nothing

long = (kindSize .) $
  Prism (const Long) $ \case
    Long -> Just ()
    _ -> Nothing

native = (kindSize .) $
  Prism (const Native) $ \case
    Native -> Just ()
    _ -> Nothing

signed = (kindSignedness .) $
  Prism (const Signed) $ \case
    Signed -> Just ()
    _ -> Nothing

unsigned = (kindSignedness .) $
  Prism (const Unsigned) $ \case
    Unsigned -> Just ()
    _ -> Nothing

representation = Prism (const Representation) $ \case
  Representation -> Just ()
  _ -> Nothing

size = Prism (const Size) $ \case
  Size -> Just ()
  _ -> Nothing

signedness = Prism (const Signedness) $ \case
  Signedness -> Just ()
  _ -> Nothing

top = Prism Top $ \case
  Top σ -> Just σ
  _ -> Nothing

kind = (top .) $
  Prism (uncurry Kind) $ \case
    Kind κ κ' -> Just (κ, κ')
    _ -> Nothing

invariant = (top .) $
  Prism (const Invariant) $ \case
    Invariant -> Just ()
    _ -> Nothing

subtypable = (top .) $
  Prism (const Subtypable) $ \case
    Subtypable -> Just ()
    _ -> Nothing

transparent = (top .) $
  Prism (const Transparent) $ \case
    Transparent -> Just ()
    _ -> Nothing

opaque = (top .) $
  Prism (const Opaque) $ \case
    Opaque -> Just ()
    _ -> Nothing

class FreeVariablesType u where
  freeVariablesType :: u -> Set TypeIdentifier

class ConvertType u where
  convertType :: TypeIdentifier -> TypeIdentifier -> u -> u

class SubstituteType u where
  substituteType :: Type v -> TypeIdentifier -> u v -> u v

-- traverse and monadic bind
class ZonkType u where
  zonkType :: Applicative m => (v -> m (Type v')) -> u v -> m (u v')

class BindingsType u where
  bindingsType :: u -> Set TypeIdentifier

class RenameType u where
  renameType :: TypeIdentifier -> TypeIdentifier -> u -> u

freeVariablesHigherType = freeVariablesHigher freeVariablesType freeVariablesType

convertHigherType = substituteHigher convertType convertType

substituteHigherType = substituteHigher substituteType substituteType

freeVariablesSameType = freeVariablesBound bindingsType freeVariablesType freeVariablesType

convertSameType = substituteDependent avoidTypeConvert convertType convertType

substituteSameType = substituteDependent avoidType substituteType substituteType

-- todo, shouldn't this be dependent?
freeVariablesRgnForType = freeVariablesSame bindingsType freeVariablesHigherType

convertRgnForType = substituteDependent (avoidTypeConvert' convertHigherType) convertType convertHigherType

substituteRgnForType = substituteDependent (avoidType' convertHigherType) substituteType substituteHigherType

avoidType = avoidType' convertType

avoidType' = Avoid bindingsType renameType freeVariablesType

avoidTypeConvert = avoidTypeConvert' convertType

avoidTypeConvert' = Avoid bindingsType renameType Set.singleton

toTypePattern (TypePatternIntermediate _ x κ c π) = TypePattern x (flexible κ) c (map (flexible . TypeCore . TypeSub) π)

instance Fresh TypeIdentifier where
  fresh c (TypeIdentifier x) = TypeIdentifier $ Util.fresh (Set.mapMonotonic runTypeIdentifier c) x

instance Functor TypeSchemeSource where
  fmap f (TypeSchemeSource p ς) =
    TypeSchemeSource (f p) $
      mapTypeSchemeF
        (mapBound (fmap f) (fmap f))
        (fmap f)
        ς

instance Functor TypeSource where
  fmap f (TypeSource p σ) =
    TypeSource (f p) $
      mapTypeF
        id
        (fmap f)
        (fmap f)
        σ

instance BindingsType (TypePatternSource p) where
  bindingsType (TypePatternSource _ x _ _ _) = Set.singleton x

instance RenameType (TypePatternSource p) where
  renameType ux x (TypePatternSource p x' κ c π) | x == x' = TypePatternSource p ux κ c π
  renameType _ _ λ = λ

instance BindingsType (TypePattern v) where
  bindingsType (TypePattern x _ _ _) = Set.singleton x

instance RenameType (TypePattern v) where
  renameType ux x (TypePattern x' κ c π) | x == x' = TypePattern ux κ c π
  renameType _ _ λ = λ

instance ConvertType σ => ConvertType (Maybe σ) where
  convertType ux x σ = fmap (convertType ux x) σ

instance FreeVariablesType (TypeScheme v) where
  freeVariablesType (TypeSchemeCore σ) = foldTypeSchemeF go' go σ
    where
      go = freeVariablesType
      go' = freeVariablesSameType

instance ConvertType (TypeSchemeSource p) where
  convertType ux x (TypeSchemeSource p σ) = TypeSchemeSource p $ mapTypeSchemeF go' go σ
    where
      go = convertType ux x
      go' = convertSameType ux x

instance ConvertType (TypeScheme v) where
  convertType ux x (TypeSchemeCore σ) = TypeSchemeCore $ mapTypeSchemeF go' go σ
    where
      go = convertType ux x
      go' = convertSameType ux x

instance SubstituteType TypeScheme where
  substituteType ux x (TypeSchemeCore σ) = TypeSchemeCore $ mapTypeSchemeF go' go σ
    where
      go = substituteType ux x
      go' = substituteSameType ux x

instance FreeVariablesType (Type v) where
  freeVariablesType (TypeCore (TypeSub (TypeVariable x))) = Set.singleton x
  freeVariablesType (TypeCore σ) = foldTypeF mempty go go σ
    where
      go = freeVariablesType

instance ConvertType (TypeSource p) where
  convertType ux x (TypeSource p (TypeSub (TypeVariable x'))) | x == x' = TypeSource p $ TypeSub $ TypeVariable ux
  convertType ux x (TypeSource p σ) = TypeSource p $ mapTypeF id go go σ
    where
      go = convertType ux x

instance ConvertType (Type v) where
  convertType ux x (TypeCore (TypeSub (TypeVariable x'))) | x == x' = TypeCore $ TypeSub $ TypeVariable ux
  convertType ux x (TypeCore σ) = TypeCore $ mapTypeF id go go σ
    where
      go = convertType ux x

instance SubstituteType (Type) where
  substituteType ux x (TypeCore (TypeSub (TypeVariable x'))) | x == x' = ux
  substituteType ux x (TypeCore σ) = TypeCore $ mapTypeF id go go σ
    where
      go = substituteType ux x

instance FreeVariablesType (Instantiation v) where
  freeVariablesType (InstantiationCore θ) = foldInstantiationF go go θ
    where
      go = freeVariablesType

instance ConvertType (Instantiation v) where
  convertType ux x (InstantiationCore θ) = InstantiationCore $ mapInstantiationF go go θ
    where
      go = convertType ux x

instance SubstituteType (Instantiation) where
  substituteType ux x (InstantiationCore θ) = InstantiationCore $ mapInstantiationF go go θ
    where
      go = substituteType ux x

instance FreeVariablesType (TypePattern v) where
  freeVariablesType (TypePattern _ κ _ π) = freeVariablesType κ <> foldMap freeVariablesType π

instance ConvertType (TypePatternSource p) where
  convertType ux x (TypePatternSource p x' κ c π) =
    TypePatternSource p x' (convertType ux x κ) c (map (convertType ux x) π)

instance ConvertType (TypePattern v) where
  convertType ux x (TypePattern x' κ c π) = TypePattern x' (convertType ux x κ) c (map (convertType ux x) π)

instance SubstituteType TypePattern where
  substituteType ux x (TypePattern x' κ c π) = TypePattern x' (substituteType ux x κ) c (map (substituteType ux x) π)

instance ZonkType Type where
  zonkType f (TypeCore (TypeLogical v)) = f v
  zonkType f (TypeCore σ) =
    pure TypeCore
      <*> traverseTypeF
        (error "handled manually")
        (zonkType f)
        (zonkType f)
        σ

instance ZonkType TypeScheme where
  zonkType f (TypeSchemeCore ς) =
    pure TypeSchemeCore
      <*> traverseTypeSchemeF
        (traverseBound (zonkType f) (zonkType f))
        (zonkType f)
        ς

instance ZonkType Instantiation where
  zonkType f (InstantiationCore θ) =
    pure InstantiationCore
      <*> traverseInstantiationF (zonkType f) (zonkType f) θ

instance ZonkType TypePattern where
  zonkType f (TypePattern x κ c π) =
    pure TypePattern <*> pure x <*> zonkType f κ <*> pure c <*> traverse (zonkType f) π

instance Reduce (Instantiation v) where
  reduce (InstantiationCore θ) = InstantiationCore $ mapInstantiationF reduce reduce θ

instance Reduce (Type v) where
  reduce = id

instance Location TypeSource where
  location (TypeSource p _) = p

instance Reduce (TypePattern v) where
  reduce (TypePattern x κ c π) = TypePattern x (reduce κ) c (map reduce π)

freeTypeLogical = getConst . zonkType (Const . Set.singleton)

sourceType :: Monoid p => Type Void -> TypeSource p
sourceType (TypeCore σ) =
  TypeSource mempty $
    mapTypeF
      id
      sourceTypeScheme
      sourceType
      σ

sourceTypeAuto = Just . sourceType

sourceTypePattern (TypePattern x κ c π) = TypePatternSource mempty x (sourceType κ) c (map sourceType π)

sourceTypeScheme :: Monoid p => TypeScheme Void -> TypeSchemeSource p
sourceTypeScheme (TypeSchemeCore ς) =
  TypeSchemeSource mempty $
    mapTypeSchemeF
      (mapBound sourceTypePattern sourceTypeScheme)
      sourceType
      ς

flexible = runIdentity . zonkType absurd
