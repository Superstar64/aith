module Core.Ast.Type where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.KindPattern
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
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
  | PolyOperator (Bound (KindPattern p) (Type p))
  | PolyConstruction (Type p) (Kind p)
  | FunctionPointer (Type p) (Type p)
  | FunctionLiteralType (Type p) (Type p)
  | Qualified (Type p) (Type p)
  | Copy (Type p)
  | RuntimePair (Type p) (Type p)
  | Recursive (Bound (TypePattern p p) (Type p))
  | RegionTransformer (Type p) (Type p)
  | RegionReference (Type p) (Type p)
  | RegionSubtype (Type p) (Type p)
  deriving (Show)

typef =
  assumeIsomorph $
    typeVariable
      `branch` macro
      `branch` forallx
      `branch` kindForall
      `branch` ofCourse
      `branch` typeConstruction
      `branch` typeOperator
      `branch` polyOperator
      `branch` polyConstruction
      `branch` functionPointer
      `branch` functionLiteralType
      `branch` qualifiedx
      `branch` copy
      `branch` runtimePair
      `branch` recursive
      `branch` regionTransformer
      `branch` regionReference
      `branch` regionSubtype

instance Functor TypeF where
  fmap f σ =
    runIdentity $
      traverseTypeF
        (Identity . fmap f)
        (Identity . fmap f)
        (Identity . bimap (bimap f f) (fmap f))
        (Identity . bimap (fmap f) (fmap f))
        σ
    where
      traverseTypeF typex kind typeBound kindBound = go
        where
          go (TypeVariable x) = pure TypeVariable <*> pure x
          go (Macro σ τ) = pure Macro <*> typex σ <*> typex τ
          go (Forall λ) = pure Forall <*> typeBound λ
          go (KindForall λ) = pure KindForall <*> kindBound λ
          go (OfCourse σ) = pure OfCourse <*> typex σ
          go (TypeConstruction σ τ) = pure TypeConstruction <*> typex σ <*> typex τ
          go (TypeOperator λ) = pure TypeOperator <*> typeBound λ
          go (PolyOperator λ) = pure PolyOperator <*> kindBound λ
          go (PolyConstruction σ κ) = pure PolyConstruction <*> typex σ <*> kind κ
          go (FunctionPointer σ τs) = pure FunctionPointer <*> typex σ <*> typex τs
          go (FunctionLiteralType σ τs) = pure FunctionLiteralType <*> typex σ <*> typex τs
          go (Qualified π σ) = pure Qualified <*> typex π <*> typex σ
          go (Copy σ) = pure Copy <*> typex σ
          go (RuntimePair σ τ) = pure RuntimePair <*> typex σ <*> typex τ
          go (Recursive λ) = pure Recursive <*> typeBound λ
          go (RegionTransformer π σ) = pure RegionTransformer <*> typex π <*> typex σ
          go (RegionReference π σ) = pure RegionReference <*> typex π <*> typex σ
          go (RegionSubtype π π') = pure RegionSubtype <*> typex π <*> typex π'

foldType f (CoreType _ σ) = f $ from σ
  where
    (Isomorph _ from) = typef

mapType f (CoreType p σ) = CoreType p (to $ f $ from σ)
  where
    (Isomorph to from) = typef

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

polyOperator = Prism PolyOperator $ \case
  (PolyOperator λ) -> Just λ
  _ -> Nothing

polyConstruction = Prism (uncurry PolyConstruction) $ \case
  (PolyConstruction σ κ) -> Just (σ, κ)
  _ -> Nothing

functionPointer = Prism (uncurry FunctionPointer) $ \case
  (FunctionPointer σ τs) -> Just (σ, τs)
  _ -> Nothing

functionLiteralType = Prism (uncurry FunctionLiteralType) $ \case
  (FunctionLiteralType σ τs) -> Just (σ, τs)
  _ -> Nothing

qualifiedx = Prism (uncurry Qualified) $ \case
  (Qualified π σ) -> Just (π, σ)
  _ -> Nothing

copy = Prism Copy $ \case
  (Copy σ) -> Just σ
  _ -> Nothing

runtimePair = Prism (uncurry RuntimePair) $ \case
  (RuntimePair σ τ) -> Just (σ, τ)
  _ -> Nothing

recursive = Prism Recursive $ \case
  (Recursive λ) -> Just λ
  _ -> Nothing

regionTransformer = Prism (uncurry RegionTransformer) $ \case
  (RegionTransformer π σ) -> Just (π, σ)
  _ -> Nothing

regionReference = Prism (uncurry RegionReference) $ \case
  (RegionReference π σ) -> Just (π, σ)
  _ -> Nothing

regionSubtype = Prism (uncurry RegionSubtype) $ \case
  (RegionSubtype π π') -> Just (π, π')
  _ -> Nothing

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
  freeVariables σ = foldType (freeVariables @(Type p)) σ
  convert ix x (CoreType p (TypeVariable x')) | x == x' = (CoreType p (TypeVariable ix))
  convert ix x σ = mapType (convert @(Type p) ix x) σ
  substitute ux x (CoreType _ (TypeVariable x')) | x == x' = ux
  substitute ux x σ = mapType (substitute ux x) σ

instance Algebra (Type p) p u => Algebra (Type p) p (Bound (TypePattern p p) u) where
  freeVariables (Bound pm σ) = removeBinds (freeVariables @(Type p) σ) (bindings pm)
  convert = substituteSame (convert @(Type p)) avoidCaptureTypeConvert
  substitute = substituteSame substitute avoidCaptureType

instance (Algebra (Type p) p u, Algebra (Kind p) p u) => Algebra (Type p) p (Bound (KindPattern p) u) where
  freeVariables (Bound _ σ) = freeVariables @(Type p) σ
  convert = substituteLower (convert @(Type p)) (flip const)
  substitute = substituteLower substitute avoidCaptureKind

instance Semigroup p => Algebra (Kind p) p (Type p) where
  freeVariables = foldType $ freeVariables @(Kind p)
  convert ix x = mapType $ convert @(Kind p) ix x
  substitute ux x = mapType $ substitute ux x

instance Semigroup p => Algebra (Type p) p (Kind p) where
  freeVariables _ = mempty
  convert _ _ = id
  substitute _ _ = id

instance Semigroup p => Reduce (Type p) where
  reduce (CoreType _ (TypeConstruction σ τ)) | (CoreType _ (TypeOperator λ)) <- reduce σ = apply λ (reduce τ)
  reduce (CoreType _ (PolyConstruction σ κ)) | (CoreType _ (PolyOperator λ)) <- reduce σ = apply λ (reduce κ)
  reduce σ = mapType reduce σ

instance Semigroup p => Apply (Bound (TypePattern p p) (Type p)) (Type p) (Type p) where
  apply (Bound (CoreTypePattern _ (TypePatternVariable x _)) σ) ux = reduce $ substitute ux x σ

instance Semigroup p => Apply (Bound (KindPattern p) (Type p)) (Kind p) (Type p) where
  apply (Bound (CoreKindPattern _ (KindPatternVariable x _)) σ) ux = reduce $ substitute ux x σ

instance Location Type where
  location (CoreType p _) = p
