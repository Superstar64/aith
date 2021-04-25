module Core.Ast.Type where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.KindPattern
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import Misc.Prism
import qualified Misc.Variables as Variables

data TypeF p
  = TypeVariable Identifier
  | Macro (Type p) (Type p)
  | Forall (Bound (TypePattern p p) (Type p))
  | KindForall (Bound (KindPattern p) (Type p))
  | OfCourse (Type p)
  | TypeConstruction (Type p) (Type p)
  | TypeOperator (Bound (TypePattern p p) (Type p))
  | FunctionPointer (Type p) [Type p]
  | FunctionLiteralType (Type p) [Type p]
  | ErasedQualified (Type p) (Type p)
  | Copy (Type p)
  | RuntimePair (Type p) (Type p)
  deriving (Show)

traverseType typex typeBound kindBound = go
  where
    go (TypeVariable x) = pure TypeVariable <*> pure x
    go (Macro σ τ) = pure Macro <*> typex σ <*> typex τ
    go (Forall λ) = pure Forall <*> typeBound λ
    go (KindForall λ) = pure KindForall <*> kindBound λ
    go (OfCourse σ) = pure OfCourse <*> typex σ
    go (TypeConstruction σ τ) = pure TypeConstruction <*> typex σ <*> typex τ
    go (TypeOperator λ) = pure TypeOperator <*> typeBound λ
    go (FunctionPointer σ τs) = pure FunctionPointer <*> typex σ <*> traverse typex τs
    go (FunctionLiteralType σ τs) = pure FunctionLiteralType <*> typex σ <*> traverse typex τs
    go (ErasedQualified π σ) = pure ErasedQualified <*> typex π <*> typex σ
    go (Copy σ) = pure Copy <*> typex σ
    go (RuntimePair σ τ) = pure RuntimePair <*> typex σ <*> typex τ

foldType typex typeBound kindBound σ = getConst $ traverseType (Const . typex) (Const . typeBound) (Const . kindBound) σ

mapType typex typeBound kindBound σ = runIdentity $ traverseType (Identity . typex) (Identity . typeBound) (Identity . kindBound) σ

typeVariable = Prism TypeVariable $ \case
  (TypeVariable x) -> Just x
  _ -> Nothing

macro = Prism (uncurry Macro) $ \case
  (Macro σ τ) -> Just (σ, τ)
  _ -> Nothing

forallx = Prism Forall $ \case
  (Forall λ) -> Just λ
  _ -> Nothing

kindForall = Prism KindForall $ \case
  (KindForall λ) -> Just λ
  _ -> Nothing

ofCourse = Prism OfCourse $ \case
  (OfCourse σ) -> Just σ
  _ -> Nothing

typeConstruction = Prism (uncurry TypeConstruction) $ \case
  (TypeConstruction σ τ) -> Just (σ, τ)
  _ -> Nothing

typeOperator = Prism TypeOperator $ \case
  (TypeOperator λ) -> Just λ
  _ -> Nothing

functionPointer = Prism (uncurry FunctionPointer) $ \case
  (FunctionPointer σ τs) -> Just (σ, τs)
  _ -> Nothing

functionLiteralType = Prism (uncurry FunctionLiteralType) $ \case
  (FunctionLiteralType σ τs) -> Just (σ, τs)
  _ -> Nothing

erasedQualified = Prism (uncurry ErasedQualified) $ \case
  (ErasedQualified π σ) -> Just (π, σ)
  _ -> Nothing

copy = Prism Copy $ \case
  (Copy σ) -> Just σ
  _ -> Nothing

runtimePair = Prism (uncurry RuntimePair) $ \case
  (RuntimePair σ τ) -> Just (σ, τ)
  _ -> Nothing

instance Functor TypeF where
  fmap f σ = runIdentity $ traverseType (Identity . fmap f) (Identity . bimap (bimap f f) (fmap f)) (Identity . bimap (fmap f) (fmap f)) σ

type TypeInternal = Type Internal

data Type p = CoreType p (TypeF p) deriving (Show, Functor)

coreType = Isomorph (uncurry CoreType) $ \(CoreType p σ) -> (p, σ)

avoidCaptureType ::
  forall p pm e u.
  (Binder p pm, Algebra (Type p) p u, Algebra (Type p) p e) =>
  u ->
  Bound pm e ->
  Bound pm e
avoidCaptureType = avoidCapture @(Type p)

avoidCaptureTypeConvert ::
  forall p pm e.
  (Binder p pm, Algebra (Type p) p e) =>
  Identifier ->
  Bound pm e ->
  Bound pm e
avoidCaptureTypeConvert = avoidCaptureGeneral internalVariable (convert @(Type p))

instance Semigroup p => Algebra (Type p) p (Type p) where
  freeVariables (CoreType p (TypeVariable x)) = Variables.singleton x p
  freeVariables (CoreType _ σ) = foldType go go go σ
    where
      go = freeVariables @(Type p)
  convert ix x (CoreType p (TypeVariable x')) | x == x' = (CoreType p (TypeVariable ix))
  convert ix x (CoreType p σ) = CoreType p $ mapType go go go σ
    where
      go = convert @(Type p) ix x
  substitute ux x (CoreType _ (TypeVariable x')) | x == x' = ux
  substitute ux x (CoreType p σ) = CoreType p $ mapType go go go σ
    where
      go = substitute ux x

instance Algebra (Type p) p u => Algebra (Type p) p (Bound (TypePattern p p) u) where
  freeVariables (Bound pm σ) = removeBinds (freeVariables @(Type p) σ) (bindings pm)
  convert = substituteSame (convert @(Type p)) avoidCaptureTypeConvert
  substitute = substituteSame substitute avoidCaptureType

instance (Algebra (Type p) p u, Algebra (Kind p) p u) => Algebra (Type p) p (Bound (KindPattern p) u) where
  freeVariables (Bound _ σ) = freeVariables @(Type p) σ
  convert = substituteLower (convert @(Type p)) (flip const)
  substitute = substituteLower substitute avoidCaptureKind

instance Semigroup p => Algebra (Kind p) p (Type p) where
  freeVariables (CoreType _ σ) = foldType go go go σ
    where
      go = freeVariables @(Kind p)
  convert ix x (CoreType p σ) = CoreType p $ mapType go go go σ
    where
      go = convert @(Kind p) ix x
  substitute ux x (CoreType p σ) = CoreType p $ mapType go go go σ
    where
      go = substitute ux x

instance Semigroup p => Algebra (Type p) p (Kind p) where
  freeVariables _ = mempty
  convert _ _ = id
  substitute _ _ = id

reduceTypeImpl (TypeConstruction σ τ) | (CoreType _ (TypeOperator λ)) <- reduce σ = let (CoreType _ σ') = apply λ (reduce τ) in σ'
reduceTypeImpl σ = runIdentity $ traverseType go go go σ
  where
    go = Identity . reduce

instance Semigroup p => Reduce (Type p) where
  reduce (CoreType p σ) = CoreType p $ reduceTypeImpl σ

instance Semigroup p => Apply (Bound (TypePattern p p) (Type p)) (Type p) (Type p) where
  apply (Bound (CoreTypePattern _ (TypePatternVariable x _)) σ) ux = reduce $ substitute ux x σ

instance Semigroup p => Apply (Bound (KindPattern p) (Type p)) (Kind p) (Type p) where
  apply (Bound (CoreKindPattern _ (KindPatternVariable x _)) σ) ux = reduce $ substitute ux x σ

instance Location Type where
  location (CoreType p _) = p
