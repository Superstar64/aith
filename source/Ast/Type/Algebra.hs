module Ast.Type.Algebra where

import Ast.Common.Variable
import Ast.Type.Runtime
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))

data TypeConstant
  = TypeVariable TypeIdentifier
  | TypeGlobalVariable TypeGlobalIdentifier
  | World
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
  | Kind σ
  | Syntactic
  | Propositional
  | Unification
  | AmbiguousLabel
  | Label
  | Hole h
  | TypeBoolean (TypeBoolean σ)
  | TypeTrue
  | TypeFalse
  deriving (Show)

data Erasure
  = Transparent
  | Concrete
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
  Kind σ -> pure Kind <*> g σ
  Syntactic -> pure Syntactic
  Propositional -> pure Propositional
  Unification -> pure Unification
  Top -> pure Top
  Hole h -> Hole <$> a h
  Label -> pure Label
  AmbiguousLabel -> pure AmbiguousLabel
  TypeBoolean σ -> TypeBoolean <$> (traverse g σ)
  TypeTrue -> pure TypeTrue
  TypeFalse -> pure TypeFalse

mapTypeF a f h g = runIdentity . traverseTypeF (Identity . a) (Identity . f) (Identity . h) (Identity . g)

foldTypeF a f h g = getConst . traverseTypeF (Const . a) (Const . f) (Const . h) (Const . g)
