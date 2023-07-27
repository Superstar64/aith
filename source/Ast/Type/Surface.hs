module Ast.Type.Surface where

import Ast.Common.Surface
import Ast.Common.Variable
import Ast.Type.Algebra hiding (Type)
import qualified Ast.Type.Algebra as Algebra (TypeF (Type))
import Ast.Type.Runtime
import Control.Category (id, (.))
import Data.Void (Void)
import Misc.Isomorph
import Misc.Prism
import Prelude hiding (id, (.))

data Type p
  = Type
      p
      ( TypeF
          ()
          Void
          (TypeScheme p)
          (Type p)
      )
  deriving (Show)

data TypeScheme p
  = TypeScheme p (TypeSchemeF p)
  deriving (Show)

data TypeSchemeF p
  = MonoType (Type p)
  | TypeForall (TypePattern p) (TypeScheme p)
  deriving (Show)

data TypePattern p = TypePattern p TypeIdentifier Erasure (Type p)
  deriving (Show)

data Instantiation p
  = Instantiation [Type p]
  | InstantiationInfer
  deriving (Show)

-- todo inline this
typeConstant = Prism TypeConstant $ \case
  (TypeConstant σ) -> Just σ
  _ -> Nothing

-- todo inline this
typeSource = Isomorph (uncurry Type) $ \(Type p σ) -> (p, σ)

-- todo inline this
kindRuntime = Prism KindRuntime $ \case
  (KindRuntime κ) -> Just κ
  _ -> Nothing

-- todo inline this
kindSize = Prism KindSize $ \case
  (KindSize κ) -> Just κ
  _ -> Nothing

-- todo inline this
kindSignedness = Prism KindSignedness $ \case
  (KindSignedness κ) -> Just κ
  _ -> Nothing

typeVariable = (typeConstant .) $
  Prism TypeVariable $ \case
    (TypeVariable x) -> Just x
    _ -> Nothing

typeGlobalVariable = (typeConstant .) $
  Prism TypeGlobalVariable $ \case
    (TypeGlobalVariable x) -> Just x
    _ -> Nothing

monoType = Prism to from
  where
    to (p, σ) = TypeScheme p (MonoType σ)
    from (TypeScheme p (MonoType σ)) = pure (p, σ)
    from _ = Nothing

world = (typeConstant .) $
  Prism (const World) $ \case
    World -> Just ()
    _ -> Nothing

inline = Prism to from . toPrism tuple4'
  where
    to (σ, p, π, τ) = Type p (Inline σ π τ)
    from (Type p (Inline σ π τ)) = Just (σ, p, π, τ)
    from _ = Nothing

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

effect = Prism to from . toPrism tuple3'
  where
    to (σ, p, π) = Type p (Effect σ π)
    from (Type p (Effect σ π)) = Just (σ, p, π)
    from _ = Nothing

unique = Prism Unique $ \case
  (Unique σ) -> Just σ
  _ -> Nothing

shared = Prism to from . toPrism tuple3'
  where
    to (σ, p, τ) = Type p (Shared σ τ)
    from (Type p (Shared σ τ)) = Just (σ, p, τ)
    from _ = Nothing

pointer = Prism to from
  where
    to (σ, p) = Type p (Pointer σ)
    from (Type p (Pointer σ)) = Just (σ, p)
    from _ = Nothing

array = Prism to from
  where
    to (σ, p) = Type p (Array σ)
    from (Type p (Array σ)) = Just (σ, p)
    from _ = Nothing

number = Prism to from . toPrism tuple3'
  where
    to (σ, p, τ) = Type p (Number σ τ)
    from (Type p (Number σ τ)) = Just (σ, p, τ)
    from _ = Nothing

number' = Prism (uncurry Number) $ \case
  (Number ρ ρ') -> Just (ρ, ρ')
  _ -> Nothing

boolean = Prism (const Boolean) $ \case
  Boolean -> Just ()
  _ -> Nothing

step = Prism (uncurry Step) $ \case
  Step σ τ -> Just (σ, τ)
  _ -> Nothing

typeIdentifier = Isomorph TypeIdentifier runTypeIdentifier

typeGlobalIdentifier = Isomorph TypeGlobalIdentifier runTypeGlobalIdentifier

typex = Prism (const Algebra.Type) $ \case
  Algebra.Type -> Just ()
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

wordRep = Prism to from
  where
    to (σ, p) = Type p (KindRuntime (WordRep σ))
    from (Type p (KindRuntime (WordRep σ))) = Just (σ, p)
    from _ = Nothing

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

kind = Prism Kind $ \case
  Kind κ -> Just (κ)
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

concrete =
  Prism (const Concrete) $ \case
    Concrete -> Just ()
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
  Prism (const $ Hole ()) $ \case
    Hole () -> Just ()
    _ -> Nothing

typeBoolean = Prism TypeBoolean $ \case
  TypeBoolean σ -> Just σ
  _ -> Nothing

typeAnd = Prism to from . toPrism tuple3'
  where
    to (σ, p, τ) = Type p (TypeBoolean (TypeAnd σ τ))
    from (Type p (TypeBoolean (TypeAnd σ τ))) = Just (σ, p, τ)
    from _ = Nothing

typeOr = Prism to from . toPrism tuple3'
  where
    to (σ, p, τ) = Type p (TypeBoolean (TypeOr σ τ))
    from (Type p (TypeBoolean (TypeOr σ τ))) = Just (σ, p, τ)
    from _ = Nothing

typeXor = Prism to from . toPrism tuple3'
  where
    to (σ, p, τ) = Type p (TypeBoolean (TypeXor σ τ))
    from (Type p (TypeBoolean (TypeXor σ τ))) = Just (σ, p, τ)
    from _ = Nothing

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

typeForall = Prism to from
  where
    to ((p, pm), σ) = TypeScheme p (TypeForall pm σ)
    from (TypeScheme p (TypeForall pm σ)) = Just ((p, pm), σ)
    from _ = Nothing

typePattern =
  Isomorph
    (\(((p, x), π), κ) -> TypePattern p x π κ)
    (\(TypePattern p x π κ) -> (((p, x), π), κ))

instanciation = Prism to from
  where
    to = Instantiation
    from (Instantiation σ) = Just σ
    from _ = Nothing

instantiationInfer = Prism to from
  where
    to () = InstantiationInfer
    from InstantiationInfer = Just ()
    from _ = Nothing

instance Alpha Type where
  freeVariables (Type p (TypeConstant (TypeVariable x))) = typeLocal x p
  freeVariables (Type p (TypeConstant (TypeGlobalVariable x))) = typeGlobal x p
  freeVariables (Type _ σ) = foldTypeF mempty mempty go go σ
    where
      go = freeVariables

instance Alpha TypeScheme where
  freeVariables (TypeScheme _ (MonoType σ)) = freeVariables σ
  freeVariables (TypeScheme _ (TypeForall (TypePattern _ x _ κ) σ)) =
    freeVariables κ <> deleteTypeLocal x (freeVariables σ)

instance Alpha Instantiation where
  freeVariables (Instantiation θ) = foldMap freeVariables θ
  freeVariables InstantiationInfer = mempty

instance Functor Type where
  fmap f (Type p σ) = Type (f p) (mapTypeF id id go go σ)
    where
      go = fmap f

instance Functor TypeScheme where
  fmap f (TypeScheme p (MonoType σ)) = TypeScheme (f p) (MonoType (fmap f σ))
  fmap f (TypeScheme p (TypeForall pm σ)) = TypeScheme (f p) (TypeForall (fmap f pm) (fmap f σ))

instance Functor TypePattern where
  fmap f (TypePattern p x π κ) = TypePattern (f p) x π (fmap f κ)

instance Functor Instantiation where
  fmap f (Instantiation θ) = Instantiation ((fmap . fmap) f θ)
  fmap _ InstantiationInfer = InstantiationInfer
