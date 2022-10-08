module Ast.Type where

import Ast.Common
import Control.Category ((.))
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
import Misc.Isomorph
import Misc.Path
import Misc.Prism
import qualified Misc.Util as Util
import Prelude hiding ((.))

newtype TypeIdentifier = TypeIdentifier {runTypeIdentifier :: String} deriving (Show, Eq, Ord)

newtype TypeGlobalIdentifier = TypeGlobalIdentifier {runTypeGlobalIdentifier :: Path} deriving (Show, Eq, Ord)

newtype TypeLogical = TypeLogicalRaw Int deriving (Eq, Ord, Show)

data TypeSub
  = TypeVariable TypeIdentifier
  | TypeGlobalVariable TypeGlobalIdentifier
  | World
  | Linear
  | Unrestricted
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
  | UnionRep [κ]
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
  | Inline σ σ σ
  | Poly λσ
  | FunctionPointer σ σ σ
  | FunctionLiteralType σ σ σ
  | Tuple [σ] σ
  | Effect σ σ
  | Unique σ
  | Shared σ σ
  | Pointer σ
  | Array σ
  | Number σ σ
  | Boolean
  | Step σ σ
  | Type
  | Region
  | Multiplicity
  | Pretype σ σ
  | Boxed
  | KindRuntime (KindRuntime σ σ)
  | KindSize KindSize
  | KindSignedness KindSignedness
  | Representation
  | Size
  | Signedness
  | Top (Top σ)
  deriving (Show)

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
  TypeSub σ -> pure (TypeSub σ)
  TypeLogical v -> pure TypeLogical <*> f v
  Inline σ π τ -> pure Inline <*> g σ <*> g π <*> g τ
  Poly λ -> pure Poly <*> i λ
  FunctionPointer σ π τ -> pure FunctionPointer <*> g σ <*> g π <*> g τ
  FunctionLiteralType σ π τ -> pure FunctionLiteralType <*> g σ <*> g π <*> g τ
  Tuple σs τ -> pure Tuple <*> traverse g σs <*> g τ
  Effect σ π -> pure Effect <*> g σ <*> g π
  Unique σ -> pure Unique <*> g σ
  Shared σ π -> pure Shared <*> g σ <*> g π
  Pointer σ -> pure Pointer <*> g σ
  Array σ -> pure Array <*> g σ
  Number ρ ρ' -> pure Number <*> g ρ <*> g ρ'
  Boolean -> pure Boolean
  Step σ τ -> pure Step <*> g σ <*> g τ
  Type -> pure Type
  Region -> pure Region
  (Pretype κ κ') -> pure Pretype <*> g κ <*> g κ'
  Boxed -> pure Boxed
  Multiplicity -> pure Multiplicity
  KindRuntime PointerRep -> pure (KindRuntime PointerRep)
  KindRuntime (StructRep κs) -> pure (KindRuntime . StructRep) <*> traverse g κs
  KindRuntime (UnionRep κs) -> pure (KindRuntime . UnionRep) <*> traverse g κs
  KindRuntime (WordRep s) -> pure (KindRuntime . WordRep) <*> g s
  KindSize s -> pure (KindSize s)
  KindSignedness s -> pure (KindSignedness s)
  Representation -> pure Representation
  Size -> pure Size
  Signedness -> pure Signedness
  Top μ -> Top <$> traverseTop g μ

mapTypeF f h g = runIdentity . traverseTypeF (Identity . f) (Identity . h) (Identity . g)

foldTypeF f h g = getConst . traverseTypeF (Const . f) (Const . h) (Const . g)

data Type p v
  = TypeAst
      p
      ( TypeF
          v
          (TypeScheme p v)
          (Type p v)
      )
  deriving (Show)

type TypeAuto p = Maybe (Type p Void)

type TypeSource p = Type p Void

type TypeUnify = Type () TypeLogical

type TypeInfer = Type () Void

type TypeSchemeAuto p = Maybe (TypeScheme p Void)

data TypeScheme p v
  = TypeScheme p (TypeSchemeF p v)
  deriving (Show)

data TypeSchemeF p v
  = MonoType (Type p v)
  | TypeForall (Bound (TypePattern p v) (TypeScheme p v))
  deriving (Show)

type TypeSchemeSource p = TypeScheme p Void

type TypeSchemeUnify = TypeScheme () TypeLogical

type TypeSchemeInfer = TypeScheme () Void

newtype Instantiation p v = Instantiation (InstantiationF p v) deriving (Show)

data InstantiationF p v
  = InstantiateType (Type p v) (Instantiation p v)
  | InstantiateEmpty
  deriving (Show)

type InstantiationUnify = Instantiation () TypeLogical

type InstantiationInfer = Instantiation () Void

data TypePattern p v = TypePattern p TypeIdentifier (Type p v) [Type p v] deriving (Show)

data TypePatternIntermediate p
  = TypePatternIntermediate p TypeIdentifier TypeInfer [TypeSub]
  deriving (Show)

type TypePatternSource p = TypePattern p Void

type TypePatternUnify = TypePattern () TypeLogical

type TypePatternInfer = TypePattern () Void

typeSchemeSource = Isomorph (uncurry TypeScheme) $ \(TypeScheme p σ) -> (p, σ)

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

typeSource = Isomorph (uncurry TypeAst) $ \(TypeAst p σ) -> (p, σ)

typePatternSource =
  Isomorph
    (\(((p, x), κ), π) -> TypePattern p x κ π)
    (\(TypePattern p x κ π) -> (((p, x), κ), π))

typeSub = Prism TypeSub $ \case
  (TypeSub σ) -> Just σ
  _ -> Nothing

typeVariable = (typeSub .) $
  Prism TypeVariable $ \case
    (TypeVariable x) -> Just x
    _ -> Nothing

typeGlobalVariable = (typeSub .) $
  Prism TypeGlobalVariable $ \case
    (TypeGlobalVariable x) -> Just x
    _ -> Nothing

typeExtra = Prism TypeLogical $ \case
  (TypeLogical v) -> Just v
  _ -> Nothing

inline = Prism (uncurry $ uncurry Inline) $ \case
  (Inline σ π τ) -> Just ((σ, π), τ)
  _ -> Nothing

poly = Prism Poly $ \case
  (Poly λ) -> Just λ
  _ -> Nothing

functionPointer = Prism (uncurry $ uncurry FunctionPointer) $ \case
  (FunctionPointer σ π τ) -> Just ((σ, π), τ)
  _ -> Nothing

functionLiteralType = Prism (uncurry $ uncurry FunctionLiteralType) $ \case
  (FunctionLiteralType σ π τ) -> Just ((σ, π), τ)
  _ -> Nothing

tuple = Prism (uncurry Tuple) $ \case
  Tuple σ τ -> Just (σ, τ)
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

linear = (typeSub .) $
  Prism (const Linear) $ \case
    Linear -> Just ()
    _ -> Nothing

unrestricted = (typeSub .) $
  Prism (const Unrestricted) $ \case
    Unrestricted -> Just ()
    _ -> Nothing

step = Prism (uncurry Step) $ \case
  Step σ τ -> Just (σ, τ)
  _ -> Nothing

typeIdentifier = Isomorph TypeIdentifier runTypeIdentifier

typeGlobalIdentifier = Isomorph TypeGlobalIdentifier runTypeGlobalIdentifier

typex = Prism (const Type) $ \case
  Type -> Just ()
  _ -> Nothing

region = Prism (const Region) $ \case
  Region -> Just ()
  _ -> Nothing

pretype = Prism (uncurry Pretype) $ \case
  Pretype κ κ' -> Just (κ, κ')
  _ -> Nothing

boxed = Prism (const Boxed) $ \case
  Boxed -> Just ()
  _ -> Nothing

multiplicity = Prism (const Multiplicity) $ \case
  Multiplicity -> Just ()
  _ -> Nothing

pointerRep = (kindRuntime .) $
  Prism (const PointerRep) $ \case
    PointerRep -> Just ()
    _ -> Nothing

structRep = (kindRuntime .) $
  Prism StructRep $ \case
    (StructRep ρs) -> Just ρs
    _ -> Nothing

unionRep = (kindRuntime .) $
  Prism UnionRep $ \case
    (UnionRep ρs) -> Just ρs
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

class TypeAlgebra u where
  freeVariablesType :: u p v -> Set TypeIdentifier
  freeVariablesGlobalType :: u p v -> Set TypeGlobalIdentifier
  convertType :: TypeIdentifier -> TypeIdentifier -> u p v -> u p v
  freeVariablesTypeSource :: Semigroup p => u p v -> Variables TypeIdentifier p
  freeVariablesGlobalTypeSource :: Semigroup p => u p v -> Variables TypeGlobalIdentifier p
  substituteType :: Type p v -> TypeIdentifier -> u p v -> u p v
  substituteGlobalType :: Type p v -> TypeGlobalIdentifier -> u p v -> u p v

  zonkType :: Applicative m => (v -> m (Type p v')) -> u p v -> m (u p v')

  joinType :: u p (Type p v) -> u p v

  traverseType :: Applicative m => (p -> m p') -> (v -> m v') -> u p v -> m (u p' v')

zonkTypeDefault :: (TypeAlgebra u, Applicative m) => (v -> m (Type p v')) -> u p v -> m (u p v')
zonkTypeDefault f σ = joinType <$> traverseType pure f σ

joinTypeDefault :: TypeAlgebra u => u p (Type p v) -> u p v
joinTypeDefault = runIdentity . zonkType pure

class BindingsType u where
  bindingsType :: u -> Set TypeIdentifier
  renameType :: TypeIdentifier -> TypeIdentifier -> u -> u

mapTypePosition f = runIdentity . traverseType (Identity . f) pure

freeVariablesHigherType = freeVariablesHigher freeVariablesType freeVariablesType

freeVariablesHigherTypeSource = freeVariablesHigherSource freeVariablesTypeSource freeVariablesTypeSource

convertHigherType = substituteHigher convertType convertType

substituteHigherType = substituteHigher substituteType substituteType

substituteGlobalHigherType = substituteHigher substituteGlobalType substituteGlobalType

freeVariablesSameType = freeVariablesBound bindingsType freeVariablesType freeVariablesType

freeVariablesGlobalHigherType = freeVariablesHigher freeVariablesGlobalType freeVariablesGlobalType

convertSameType = substituteDependent avoidTypeConvert convertType convertType

substituteSameType = substituteDependent avoidType substituteType substituteType

substituteGlobalSemiDependType = substituteBound skip (avoidCapture avoidType) substituteGlobalType substituteGlobalType

freeVariablesSameTypeSource = freeVariablesBoundSource bindingsType freeVariablesTypeSource freeVariablesTypeSource

freeVariablesGlobalHigherTypeSource = freeVariablesHigherSource freeVariablesGlobalTypeSource freeVariablesGlobalTypeSource

freeVariablesRgnForType = freeVariablesBound bindingsType freeVariablesType freeVariablesHigherType

freeVariablesRgnForTypeSource = freeVariablesBoundSource bindingsType freeVariablesTypeSource freeVariablesHigherTypeSource

freeVariablesGlobalRgnForType = freeVariablesHigher freeVariablesGlobalType freeVariablesGlobalHigherType

freeVariablesGlobalRgnForTypeSource = freeVariablesHigherSource freeVariablesGlobalTypeSource freeVariablesGlobalHigherTypeSource

convertRgnForType = substituteDependent (avoidTypeConvert' convertHigherType) convertType convertHigherType

substituteRgnForType = substituteDependent (avoidType' convertHigherType) substituteType substituteHigherType

substituteGlobalRgnForType = substituteBound skip (avoidCapture (avoidType' convertHigherType)) substituteGlobalType substituteGlobalHigherType

avoidType = avoidType' convertType

avoidType' = Avoid bindingsType renameType freeVariablesType

avoidTypeConvert = avoidTypeConvert' convertType

avoidTypeConvert' = Avoid bindingsType renameType Set.singleton

toTypePattern (TypePatternIntermediate _ x κ π) = TypePattern () x (flexible κ) (map (flexible . TypeAst () . TypeSub) π)

instance Fresh TypeIdentifier where
  fresh c (TypeIdentifier x) = TypeIdentifier $ Util.fresh (Set.mapMonotonic runTypeIdentifier c) x

instance BindingsType (TypePattern p v) where
  bindingsType (TypePattern _ x _ _) = Set.singleton x
  renameType ux x (TypePattern p x' κ π) | x == x' = TypePattern p ux κ π
  renameType _ _ λ = λ

instance TypeAlgebra TypeScheme where
  freeVariablesType (TypeScheme _ (MonoType σ)) = freeVariablesType σ
  freeVariablesType (TypeScheme _ (TypeForall λ)) = freeVariablesSameType λ
  freeVariablesGlobalType (TypeScheme _ (MonoType σ)) = freeVariablesGlobalType σ
  freeVariablesGlobalType (TypeScheme _ (TypeForall λ)) = freeVariablesGlobalHigherType λ
  convertType ux x (TypeScheme p (MonoType σ)) = TypeScheme p $ MonoType (convertType ux x σ)
  convertType ux x (TypeScheme p (TypeForall λ)) = TypeScheme p $ TypeForall (convertSameType ux x λ)
  freeVariablesTypeSource (TypeScheme _ (MonoType σ)) = freeVariablesTypeSource σ
  freeVariablesTypeSource (TypeScheme _ (TypeForall λ)) = freeVariablesSameTypeSource λ
  freeVariablesGlobalTypeSource (TypeScheme _ (MonoType σ)) = freeVariablesGlobalTypeSource σ
  freeVariablesGlobalTypeSource (TypeScheme _ (TypeForall λ)) = freeVariablesGlobalHigherTypeSource λ
  substituteType ux x (TypeScheme p (MonoType σ)) = TypeScheme p $ MonoType (substituteType ux x σ)
  substituteType ux x (TypeScheme p (TypeForall λ)) = TypeScheme p $ TypeForall (substituteSameType ux x λ)
  substituteGlobalType ux x (TypeScheme p (MonoType σ)) = TypeScheme p $ MonoType (substituteGlobalType ux x σ)
  substituteGlobalType ux x (TypeScheme p (TypeForall λ)) = TypeScheme p $ TypeForall (substituteGlobalSemiDependType ux x λ)
  zonkType = zonkTypeDefault
  joinType (TypeScheme p (MonoType σ)) = TypeScheme p (MonoType (joinType σ))
  joinType (TypeScheme p (TypeForall λ)) = TypeScheme p (TypeForall (mapBound joinType joinType λ))
  traverseType fp fv (TypeScheme p (MonoType σ)) = TypeScheme <$> fp p <*> (MonoType <$> traverseType fp fv σ)
  traverseType fp fv (TypeScheme p (TypeForall λ)) = TypeScheme <$> fp p <*> (TypeForall <$> traverseBound go go λ)
    where
      go = traverseType fp fv

instance TypeAlgebra Type where
  freeVariablesType (TypeAst _ (TypeSub (TypeVariable x))) = Set.singleton x
  freeVariablesType (TypeAst _ σ) = foldTypeF mempty go go σ
    where
      go = freeVariablesType
  freeVariablesGlobalType (TypeAst _ (TypeSub (TypeGlobalVariable x))) = Set.singleton x
  freeVariablesGlobalType (TypeAst _ σ) = foldTypeF mempty go go σ
    where
      go = freeVariablesGlobalType
  convertType ux x (TypeAst p (TypeSub (TypeVariable x'))) | x == x' = TypeAst p $ TypeSub $ TypeVariable ux
  convertType ux x (TypeAst p σ) = TypeAst p $ mapTypeF id go go σ
    where
      go = convertType ux x
  freeVariablesTypeSource (TypeAst p (TypeSub (TypeVariable x))) = Variables $ Map.singleton x p
  freeVariablesTypeSource (TypeAst _ σ) = foldTypeF mempty go go σ
    where
      go = freeVariablesTypeSource
  freeVariablesGlobalTypeSource (TypeAst p (TypeSub (TypeGlobalVariable x))) = Variables $ Map.singleton x p
  freeVariablesGlobalTypeSource (TypeAst _ σ) = foldTypeF mempty go go σ
    where
      go = freeVariablesGlobalTypeSource
  substituteType ux x (TypeAst _ (TypeSub (TypeVariable x'))) | x == x' = ux
  substituteType ux x (TypeAst p σ) = TypeAst p $ mapTypeF id go go σ
    where
      go = substituteType ux x
  substituteGlobalType ux x (TypeAst _ (TypeSub (TypeGlobalVariable x'))) | x == x' = ux
  substituteGlobalType ux x (TypeAst p σ) = TypeAst p $ mapTypeF id go go σ
    where
      go = substituteGlobalType ux x
  zonkType f (TypeAst _ (TypeLogical v)) = f v
  zonkType f (TypeAst p σ) =
    TypeAst p
      <$> traverseTypeF
        (error "handled manually")
        (zonkType f)
        (zonkType f)
        σ
  joinType = joinTypeDefault
  traverseType fp fv (TypeAst p σ) =
    TypeAst <$> fp p <*> traverseTypeF fv go go σ
    where
      go = traverseType fp fv

instance TypeAlgebra Instantiation where
  freeVariablesType (Instantiation θ) = case θ of
    InstantiateEmpty -> mempty
    InstantiateType σ θ -> go σ <> go θ
    where
      go = freeVariablesType
  freeVariablesGlobalType (Instantiation θ) = case θ of
    InstantiateEmpty -> mempty
    InstantiateType σ θ -> go σ <> go θ
    where
      go = freeVariablesGlobalType
  freeVariablesTypeSource (Instantiation θ) = case θ of
    InstantiateEmpty -> mempty
    InstantiateType σ θ -> go σ <> go θ
    where
      go = freeVariablesTypeSource
  freeVariablesGlobalTypeSource (Instantiation θ) = case θ of
    InstantiateEmpty -> mempty
    InstantiateType σ θ -> go σ <> go θ
    where
      go = freeVariablesGlobalTypeSource
  convertType ux x (Instantiation θ) =
    Instantiation $
      ( case θ of
          InstantiateEmpty -> InstantiateEmpty
          InstantiateType σ θ -> InstantiateType (go σ) (go θ)
      )
    where
      go = convertType ux x
  substituteType ux x (Instantiation θ) =
    Instantiation $
      ( case θ of
          InstantiateEmpty -> InstantiateEmpty
          InstantiateType σ θ -> InstantiateType (go σ) (go θ)
      )
    where
      go = substituteType ux x
  substituteGlobalType ux x (Instantiation θ) =
    Instantiation $
      ( case θ of
          InstantiateEmpty -> InstantiateEmpty
          InstantiateType σ θ -> InstantiateType (go σ) (go θ)
      )
    where
      go = substituteGlobalType ux x
  zonkType f (Instantiation θ) =
    Instantiation
      <$> ( case θ of
              InstantiateEmpty -> pure InstantiateEmpty
              InstantiateType σ θ -> pure InstantiateType <*> zonkType f σ <*> zonkType f θ
          )
  joinType = joinTypeDefault
  traverseType fp fv (Instantiation θ) =
    Instantiation
      <$> ( case θ of
              InstantiateEmpty -> pure InstantiateEmpty
              InstantiateType σ θ -> pure InstantiateType <*> go σ <*> go θ
          )
    where
      go = traverseType fp fv

instance TypeAlgebra TypePattern where
  freeVariablesType (TypePattern _ _ κ π) = freeVariablesType κ <> foldMap freeVariablesType π
  freeVariablesGlobalType (TypePattern _ _ κ π) = freeVariablesGlobalType κ <> foldMap freeVariablesGlobalType π
  convertType ux x (TypePattern p x' κ π) = TypePattern p x' (convertType ux x κ) (map (convertType ux x) π)
  freeVariablesTypeSource (TypePattern _ _ κ π) = freeVariablesTypeSource κ <> foldMap freeVariablesTypeSource π
  freeVariablesGlobalTypeSource (TypePattern _ _ κ π) = freeVariablesGlobalTypeSource κ <> foldMap freeVariablesGlobalTypeSource π
  substituteType ux x (TypePattern p x' κ π) = TypePattern p x' (substituteType ux x κ) (map (substituteType ux x) π)
  substituteGlobalType ux x (TypePattern p x' κ π) = TypePattern p x' (substituteGlobalType ux x κ) (map (substituteGlobalType ux x) π)
  zonkType f (TypePattern p x κ π) =
    TypePattern p x <$> zonkType f κ <*> traverse (zonkType f) π
  traverseType fp fv (TypePattern p x κ pm) =
    TypePattern <$> fp p <*> pure x <*> go κ <*> traverse go pm
    where
      go = traverseType fp fv
  joinType = joinTypeDefault

freeTypeLogical = getConst . zonkType (Const . Set.singleton)

flexible = runIdentity . zonkType absurd

sourceTypeScheme :: TypeSchemeInfer -> TypeSchemeSource ()
sourceTypeScheme = mapTypePosition (const ())

sourceType :: TypeInfer -> TypeSource ()
sourceType = mapTypePosition (const ())

positionType (TypeAst p _) = p

isTypeImport (TypeAst _ (TypeSub (TypeGlobalVariable _))) = True
isTypeImport _ = False
