module Ast.Type where

import Ast.Common
import Control.Category ((.))
import Control.Monad.Trans.State.Strict (get, put, runState)
import Data.Bifoldable (Bifoldable)
import Data.Bifunctor (Bifunctor)
import Data.Bitraversable (Bitraversable, bitraverse)
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
import Misc.Boolean
import Misc.Isomorph
import Misc.Path
import Misc.Prism
import qualified Misc.Util as Util
import Prelude hiding ((.))

newtype TypeIdentifier = TypeIdentifier {runTypeIdentifier :: String} deriving (Show, Eq, Ord)

newtype TypeGlobalIdentifier = TypeGlobalIdentifier {runTypeGlobalIdentifier :: Path} deriving (Show, Eq, Ord)

newtype TypeLogical = TypeLogicalRaw Int deriving (Eq, Ord, Show)

globalType heading (TypeIdentifier x) = TypeGlobalIdentifier (Path heading x)

data TypeConstant
  = TypeVariable TypeIdentifier
  | TypeGlobalVariable TypeGlobalIdentifier
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
  | UnionRep [κ]
  | WordRep s
  deriving (Show, Eq, Ord)

data TypeBoolean σ
  = TypeNot σ
  | TypeAnd σ σ
  | TypeOr σ σ
  | TypeXor σ σ
  deriving (Show, Functor, Foldable, Traversable)

data TypeF h v λσ σ
  = TypeConstant TypeConstant
  | TypeLogical v
  | Top
  | Inline σ σ σ
  | Poly σ λσ
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
  | Kind σ σ
  | Syntactic
  | Propositional
  | Unification
  | Transparent
  | Opaque
  | Transparency
  | AmbiguousLabel
  | Label
  | Hole h
  | TypeBoolean (TypeBoolean σ)
  | TypeTrue
  | TypeFalse
  deriving (Show)

traverseTypeF ::
  Applicative m =>
  (h -> m h') ->
  (v -> m v') ->
  (λσ -> m λσ') ->
  (σ -> m σ') ->
  TypeF h v λσ σ ->
  m (TypeF h' v' λσ' σ')
traverseTypeF a f i g σ = case σ of
  TypeConstant σ -> pure (TypeConstant σ)
  TypeLogical v -> pure TypeLogical <*> f v
  Inline σ π τ -> pure Inline <*> g σ <*> g π <*> g τ
  Poly σ λ -> pure Poly <*> g σ <*> i λ
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
  Kind σ τ -> pure Kind <*> g σ <*> g τ
  Syntactic -> pure Syntactic
  Propositional -> pure Propositional
  Transparent -> pure Transparent
  Opaque -> pure Opaque
  Unification -> pure Unification
  Transparency -> pure Transparency
  Top -> pure Top
  Hole h -> Hole <$> a h
  Label -> pure Label
  AmbiguousLabel -> pure AmbiguousLabel
  TypeBoolean σ -> TypeBoolean <$> (traverse g σ)
  TypeTrue -> pure TypeTrue
  TypeFalse -> pure TypeFalse

mapTypeF a f h g = runIdentity . traverseTypeF (Identity . a) (Identity . f) (Identity . h) (Identity . g)

foldTypeF a f h g = getConst . traverseTypeF (Const . a) (Const . f) (Const . h) (Const . g)

data Type phase p v
  = TypeAst
      p
      ( TypeF
          (phase () Void)
          v
          (TypeScheme phase p v)
          (Type phase p v)
      )

instance (IsCore phase, Show v, Show p) => Show (Type phase p v) where
  showsPrec d (TypeAst p σ) = showParen (d > 10) $ showString "TypeAst " . showsPrec 11 p . showString " " . showsPrec 11 (core σ)

type TypeSource p = Type Source p Void

type TypeUnify = Type Core () TypeLogical

type TypeInfer = Type Core () Void

type TypeSchemeAuto p = Maybe (TypeScheme Source p Void)

data TypeScheme phase p v
  = TypeScheme p (TypeSchemeF phase p v)
  deriving (Show)

data TypeSchemeF phase p v
  = MonoType (Type phase p v)
  | TypeForall (Bound (TypePattern phase p v) (TypeScheme phase p v))
  deriving (Show)

type TypeSchemeSource p = TypeScheme Source p Void

type TypeSchemeUnify = TypeScheme Core () TypeLogical

type TypeSchemeInfer = TypeScheme Core () Void

data LabelScheme phase p v
  = MonoLabel (TypeScheme phase p v)
  | LabelForall TypeIdentifier (LabelScheme phase p v)

type LabelSchemeUnify = LabelScheme Core () TypeLogical

type LabelSchemeInfer = LabelScheme Core () Void

newtype Instantiation phase p v = Instantiation (InstantiationF phase p v)

data InstantiationF phase p v
  = InstantiateType (Type phase p v) (Instantiation phase p v)
  | InstantiateEmpty

type InstantiationUnify = Instantiation Core () TypeLogical

type InstantiationInfer = Instantiation Core () Void

data TypePattern phase p v = TypePattern p TypeIdentifier (Type phase p v)
  deriving (Show)

data TypePatternIntermediate p
  = TypePatternIntermediate p TypeIdentifier TypeInfer

type TypePatternSource p = TypePattern Source p Void

type TypePatternUnify = TypePattern Core () TypeLogical

type TypePatternInfer = TypePattern Core () Void

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
    (\((p, x), κ) -> TypePattern p x κ)
    (\(TypePattern p x κ) -> ((p, x), κ))

typeConstant = Prism TypeConstant $ \case
  (TypeConstant σ) -> Just σ
  _ -> Nothing

typeVariable = (typeConstant .) $
  Prism TypeVariable $ \case
    (TypeVariable x) -> Just x
    _ -> Nothing

typeGlobalVariable = (typeConstant .) $
  Prism TypeGlobalVariable $ \case
    (TypeGlobalVariable x) -> Just x
    _ -> Nothing

typeExtra = Prism TypeLogical $ \case
  (TypeLogical v) -> Just v
  _ -> Nothing

inline = Prism (uncurry $ uncurry Inline) $ \case
  (Inline σ π τ) -> Just ((σ, π), τ)
  _ -> Nothing

poly = Prism (uncurry Poly) $ \case
  (Poly σ λ) -> Just (σ, λ)
  _ -> Nothing

functionPointer = Prism (uncurry $ uncurry FunctionPointer) $ \case
  (FunctionPointer σ π τ) -> Just ((σ, π), τ)
  _ -> Nothing

functionLiteralType = Prism (uncurry $ uncurry FunctionLiteralType) $ \case
  (FunctionLiteralType σ π τ) -> Just ((σ, π), τ)
  _ -> Nothing

tuple = Prism Tuple $ \case
  Tuple σ -> Just (σ)
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

world = (typeConstant .) $
  Prism (const World) $ \case
    World -> Just ()
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

top = Prism (const Top) $ \case
  Top -> Just ()
  _ -> Nothing

kind = Prism (uncurry Kind) $ \case
  Kind κ κ' -> Just (κ, κ')
  _ -> Nothing

syntactic =
  Prism (const Syntactic) $ \case
    Syntactic -> Just ()
    _ -> Nothing

propositional =
  Prism (const Propositional) $ \case
    Propositional -> Just ()
    _ -> Nothing

transparent =
  Prism (const Transparent) $ \case
    Transparent -> Just ()
    _ -> Nothing

opaque =
  Prism (const Opaque) $ \case
    Opaque -> Just ()
    _ -> Nothing

transparency =
  Prism (const Transparency) $ \case
    Transparency -> Just ()
    _ -> Nothing

unification =
  Prism (const Unification) $ \case
    Unification -> Just ()
    _ -> Nothing

label =
  Prism (const Label) $ \case
    Label -> Just ()
    _ -> Nothing

ambiguousLabel =
  Prism (const AmbiguousLabel) $ \case
    AmbiguousLabel -> Just ()
    _ -> Nothing

hole =
  Prism (const $ Hole (Source ())) $ \case
    Hole (Source ()) -> Just ()
    _ -> Nothing

typeBoolean = Prism TypeBoolean $ \case
  TypeBoolean σ -> Just σ
  _ -> Nothing

typeAnd = (typeBoolean .) $
  Prism (uncurry TypeAnd) $ \case
    TypeAnd σ τ -> Just (σ, τ)
    _ -> Nothing

typeOr = (typeBoolean .) $
  Prism (uncurry TypeOr) $ \case
    TypeOr σ τ -> Just (σ, τ)
    _ -> Nothing

typeXor = (typeBoolean .) $
  Prism (uncurry TypeXor) $ \case
    TypeXor σ τ -> Just (σ, τ)
    _ -> Nothing

typeNot = (typeBoolean .) $
  Prism TypeNot $ \case
    TypeNot σ -> Just σ
    _ -> Nothing

typeTrue = Prism (const TypeTrue) $ \case
  TypeTrue -> Just ()
  _ -> Nothing

typeFalse = Prism (const TypeFalse) $ \case
  TypeFalse -> Just ()
  _ -> Nothing

class TypeAlgebra u where
  freeVariablesType :: Bifoldable phase => u phase p v -> Set TypeIdentifier
  freeVariablesGlobalType :: Bifoldable phase => u phase p v -> Set TypeGlobalIdentifier
  convertType :: Bifunctor phase => TypeIdentifier -> TypeIdentifier -> u phase p v -> u phase p v
  freeVariablesTypeSource :: (Semigroup p, Bifoldable phase) => u phase p v -> Variables TypeIdentifier p
  freeVariablesGlobalTypeSource :: (Semigroup p, Bifoldable phase) => u phase p v -> Variables TypeGlobalIdentifier p
  substituteType :: Type Core p v -> TypeIdentifier -> u Core p v -> u Core p v
  substituteGlobalType :: Type Core p v -> TypeGlobalIdentifier -> u Core p v -> u Core p v
  zonkType :: (Applicative m, Bitraversable phase) => (v -> m (Type phase p v')) -> u phase p v -> m (u phase p v')
  joinType :: (Bitraversable phase) => u phase p (Type phase p v) -> u phase p v
  traverseTypes :: (Applicative m, Bitraversable phase) => (p -> m p') -> (Type phase p v -> m (Type phase p' v')) -> u phase p v -> m (u phase p' v')

mapTypes fp f = runIdentity . traverseTypes (Identity . fp) (Identity . f)

traverseType :: (TypeAlgebra u, Applicative m, Bitraversable phase) => (p -> m p') -> (v -> m v') -> u phase p v -> m (u phase p' v')
traverseType fp fv = traverseTypes fp $ \(TypeAst p σ) -> TypeAst <$> fp p <*> traverseTypeF (bitraverse pure absurd) fv go go σ
  where
    go = traverseType fp fv

zonkTypeDefault :: (TypeAlgebra u, Applicative m, Bitraversable phase) => (v -> m (Type phase p v')) -> u phase p v -> m (u phase p v')
zonkTypeDefault f σ = joinType <$> traverseType pure f σ

joinTypeDefault :: (TypeAlgebra u, Bitraversable phase) => u phase p (Type phase p v) -> u phase p v
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

avoidType = avoidType' convertType

avoidType' = Avoid bindingsType renameType freeVariablesType

avoidTypeConvert = avoidTypeConvert' convertType

avoidTypeConvert' = Avoid bindingsType renameType Set.singleton

toTypePattern (TypePatternIntermediate _ x κ) = TypePattern () x κ

instance Fresh TypeIdentifier where
  fresh c (TypeIdentifier x) = TypeIdentifier $ Util.fresh (Set.mapMonotonic runTypeIdentifier c) x

instance BindingsType (TypePattern phase p v) where
  bindingsType (TypePattern _ x _) = Set.singleton x
  renameType ux x (TypePattern p x' κ) | x == x' = TypePattern p ux κ
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
  traverseTypes fp f (TypeScheme p (MonoType σ)) = TypeScheme <$> fp p <*> (MonoType <$> traverseTypes fp f σ)
  traverseTypes fp f (TypeScheme p (TypeForall λ)) = TypeScheme <$> fp p <*> (TypeForall <$> traverseBound go go λ)
    where
      go = traverseTypes fp f

instance TypeAlgebra Type where
  freeVariablesType (TypeAst _ (TypeConstant (TypeVariable x))) = Set.singleton x
  freeVariablesType (TypeAst _ σ) = foldTypeF mempty mempty go go σ
    where
      go = freeVariablesType
  freeVariablesGlobalType (TypeAst _ (TypeConstant (TypeGlobalVariable x))) = Set.singleton x
  freeVariablesGlobalType (TypeAst _ σ) = foldTypeF mempty mempty go go σ
    where
      go = freeVariablesGlobalType
  convertType ux x (TypeAst p (TypeConstant (TypeVariable x'))) | x == x' = TypeAst p $ TypeConstant $ TypeVariable ux
  convertType ux x (TypeAst p σ) = TypeAst p $ mapTypeF id id go go σ
    where
      go = convertType ux x
  freeVariablesTypeSource (TypeAst p (TypeConstant (TypeVariable x))) = Variables $ Map.singleton x p
  freeVariablesTypeSource (TypeAst _ σ) = foldTypeF mempty mempty go go σ
    where
      go = freeVariablesTypeSource
  freeVariablesGlobalTypeSource (TypeAst p (TypeConstant (TypeGlobalVariable x))) = Variables $ Map.singleton x p
  freeVariablesGlobalTypeSource (TypeAst _ σ) = foldTypeF mempty mempty go go σ
    where
      go = freeVariablesGlobalTypeSource
  substituteType ux x (TypeAst _ (TypeConstant (TypeVariable x'))) | x == x' = ux
  substituteType ux x (TypeAst p σ) = TypeAst p $ mapTypeF id id go go σ
    where
      go = substituteType ux x
  substituteGlobalType ux x (TypeAst _ (TypeConstant (TypeGlobalVariable x'))) | x == x' = ux
  substituteGlobalType ux x (TypeAst p σ) = TypeAst p $ mapTypeF id id go go σ
    where
      go = substituteGlobalType ux x

  zonkType f (TypeAst _ (TypeLogical v)) = f v
  zonkType f (TypeAst p σ) =
    TypeAst p
      <$> traverseTypeF
        (bitraverse pure absurd)
        (error "handled manually")
        (zonkType f)
        (zonkType f)
        σ
  joinType = joinTypeDefault
  traverseTypes _ = id

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
  traverseTypes _ _ (Instantiation (InstantiateEmpty)) = pure $ Instantiation InstantiateEmpty
  traverseTypes fp f (Instantiation (InstantiateType σ θ)) = Instantiation <$> (InstantiateType <$> traverseTypes fp f σ <*> traverseTypes fp f θ)

instance TypeAlgebra TypePattern where
  freeVariablesType (TypePattern _ _ κ) = freeVariablesType κ
  freeVariablesGlobalType (TypePattern _ _ κ) = freeVariablesGlobalType κ
  convertType ux x (TypePattern p x' κ) = TypePattern p x' (convertType ux x κ)
  freeVariablesTypeSource (TypePattern _ _ κ) = freeVariablesTypeSource κ
  freeVariablesGlobalTypeSource (TypePattern _ _ κ) = freeVariablesGlobalTypeSource κ
  substituteType ux x (TypePattern p x' κ) = TypePattern p x' (substituteType ux x κ)
  substituteGlobalType ux x (TypePattern p x' κ) = TypePattern p x' (substituteGlobalType ux x κ)
  zonkType f (TypePattern p x κ) =
    TypePattern p x <$> zonkType f κ
  joinType = joinTypeDefault
  traverseTypes fp f (TypePattern p x κ) =
    TypePattern <$> fp p <*> pure x <*> go κ
    where
      go = traverseTypes fp f

-- may have duplicates
freeTypeLogical = getConst . zonkType (Const . (\x -> [x]))

flexible = runIdentity . zonkType absurd

sourceTypeScheme :: TypeSchemeInfer -> TypeSchemeSource ()
sourceTypeScheme (TypeScheme () (MonoType σ)) = TypeScheme () $ MonoType (sourceType σ)
sourceTypeScheme (TypeScheme () (TypeForall ς)) =
  TypeScheme () $ TypeForall (mapBound sourceTypePattern sourceTypeScheme ς)

sourceTypePattern :: TypePatternInfer -> TypePatternSource ()
sourceTypePattern (TypePattern () x σ) = TypePattern () x (sourceType σ)

sourceType :: TypeInfer -> TypeSource ()
sourceType (TypeAst () σ) = TypeAst () $ mapTypeF (\(Core v) -> absurd v) absurd sourceTypeScheme sourceType σ

positionType (TypeAst p _) = p

isTypeImport (TypeAst _ (TypeConstant (TypeGlobalVariable _))) = True
isTypeImport _ = False

data ReLabel = ReLabel (Set TypeIdentifier) [TypeIdentifier]

reLabel :: TypeScheme Core () v -> LabelScheme Core () v
reLabel ς = foldr LabelForall (MonoLabel ς') schemes
  where
    (ς', ReLabel _ schemes) = runState (goTypeScheme ς) (ReLabel (freeVariablesType ς) [])
    goType (TypeAst () (Poly _ ς)) = do
      ReLabel free schemes <- get
      let new = fresh free (TypeIdentifier "L")
      put $ ReLabel (Set.insert new free) (new : schemes)
      ς <- goTypeScheme ς
      pure $ TypeAst () $ Poly (TypeAst () $ TypeConstant $ TypeVariable new) ς
    goType (TypeAst () σ) = TypeAst () <$> traverseTypeF pure pure (error "handled manually") goType σ
    goTypeScheme (TypeScheme () (MonoType σ)) = TypeScheme () <$> MonoType <$> goType σ
    goTypeScheme (TypeScheme () (TypeForall (Bound (TypePattern () x κ) ς))) = do
      κ <- goType κ
      ς <- goTypeScheme ς
      pure $ TypeScheme () $ TypeForall $ Bound (TypePattern () x κ) ς

nameTypeLogical :: Applicative m => TypeLogical -> m TypeInfer
nameTypeLogical (TypeLogicalRaw i) = pure $ TypeAst () $ TypeConstant $ TypeVariable $ TypeIdentifier $ show i

nameType :: TypeUnify -> TypeSource ()
nameType = sourceType . runIdentity . zonkType nameTypeLogical

linear = TypeAst () TypeFalse

unrestricted = TypeAst () TypeTrue

none = TypeAst () TypeFalse

reconstructF
  indexVariable
  indexGlobalVariable
  indexLogical
  poly
  reconstructRuntime
  reconstructMultiplicities
  reconstructPropositonal
  (TypeAst () σ) = case σ of
    TypeConstant (TypeVariable x) -> do
      indexVariable x
    TypeConstant (TypeGlobalVariable x) -> do
      indexGlobalVariable x
    TypeLogical v -> do
      indexLogical v
    Inline _ _ _ -> do
      pure $ TypeAst () $ Type
    Poly _ ς -> do
      poly ς
    FunctionPointer _ _ _ -> do
      pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime PointerRep) unrestricted
    FunctionLiteralType _ _ _ -> do
      pure $ TypeAst () $ Type
    Tuple σs -> do
      ρs <- traverse reconstructRuntime σs
      τ <- reconstructMultiplicities σs
      pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime $ StructRep ρs) τ
    Step σ τ -> do
      κ <- reconstructRuntime σ
      μ <- reconstructRuntime τ
      let union = TypeAst () $ KindRuntime $ UnionRep $ [κ, μ]
      let wrap = TypeAst () $ KindRuntime $ StructRep $ [TypeAst () $ KindRuntime $ WordRep $ TypeAst () $ KindSize $ Byte, union]
      pure (TypeAst () $ Pretype wrap $ linear)
    Effect _ _ -> pure $ TypeAst () $ Type
    Unique _ ->
      pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) linear
    Shared _ _ ->
      pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) unrestricted
    Number _ ρ -> do
      pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime $ WordRep ρ) unrestricted
    Pointer _ -> pure $ TypeAst () $ Boxed
    Array _ -> pure $ TypeAst () $ Boxed
    Boolean -> pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime $ WordRep $ TypeAst () $ KindSize $ Byte) unrestricted
    TypeConstant World -> pure $ TypeAst () $ Region
    Type -> pure $ TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Transparent)
    Region -> pure $ TypeAst () $ Kind (TypeAst () Propositional) (TypeAst () Transparent)
    Pretype _ _ -> pure $ TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Transparent)
    Boxed -> pure $ TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Transparent)
    Multiplicity -> pure $ TypeAst () $ Kind (TypeAst () Propositional) (TypeAst () Transparent)
    KindRuntime _ -> pure $ TypeAst () $ Representation
    KindSize _ -> pure $ TypeAst () $ Size
    KindSignedness _ -> pure $ TypeAst () $ Signedness
    Representation -> pure $ TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Opaque)
    Size -> pure $ TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Opaque)
    Signedness -> pure $ TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Opaque)
    Syntactic -> pure (TypeAst () Unification)
    Propositional -> pure (TypeAst () Unification)
    Transparent -> pure (TypeAst () Transparency)
    Opaque -> pure (TypeAst () Transparency)
    Transparency -> pure (TypeAst () Top)
    Unification -> pure (TypeAst () Top)
    Kind _ _ -> do
      pure (TypeAst () $ Top)
    AmbiguousLabel -> pure (TypeAst () Label)
    Label -> pure $ TypeAst () $ Top
    TypeTrue -> reconstructPropositonal []
    TypeFalse -> reconstructPropositonal []
    TypeBoolean (TypeXor σ τ) -> reconstructPropositonal [σ, τ]
    TypeBoolean (TypeOr σ τ) -> reconstructPropositonal [σ, τ]
    TypeBoolean (TypeAnd σ τ) -> reconstructPropositonal [σ, τ]
    TypeBoolean (TypeNot σ) -> reconstructPropositonal [σ]
    Hole (Core v) -> absurd v
    Top -> error "reconstruct top"

convertBoolean (TypeAst () (TypeLogical v)) = variable v
convertBoolean (TypeAst () (TypeConstant c)) = constant c
convertBoolean (TypeAst () (TypeBoolean σ)) = case σ of
  TypeAnd σ τ -> convertBoolean σ * convertBoolean τ
  TypeOr σ τ -> x + y + x * y
    where
      x = convertBoolean σ
      y = convertBoolean τ
  TypeXor σ τ -> convertBoolean σ + convertBoolean τ
  TypeNot σ -> convertBoolean σ + 1
convertBoolean (TypeAst () TypeTrue) = 1
convertBoolean (TypeAst () TypeFalse) = 0
convertBoolean _ = error "convert boolean error"

unconvertBoolean (Polynomial e) | Set.null e = TypeAst () TypeFalse
unconvertBoolean (Polynomial e) = foldl1 (\σ τ -> TypeAst () $ TypeBoolean $ TypeXor σ τ) (map prod $ Set.toList e)
  where
    prod e | Set.null e = TypeAst () TypeTrue
    prod e = foldl1 (\σ τ -> TypeAst () $ TypeBoolean $ TypeAnd σ τ) (map var $ Set.toList e)
      where
        var (Flexible v) = TypeAst () $ TypeLogical v
        var (Constant c) = TypeAst () $ TypeConstant c

simplify :: (TypeAlgebra u, Ord v') => u Core () v' -> u Core () v'
simplify = mapTypes id go
  where
    go σ@(TypeAst () (TypeBoolean _)) = unconvertBoolean $ convertBoolean σ
    go (TypeAst () σ) = TypeAst () $ mapTypeF (absurd . runCore) id simplify simplify σ
