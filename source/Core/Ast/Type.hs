module Core.Ast.Type where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.KindPattern
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import Misc.Prism
import Misc.Variables (Variables)
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
  deriving (Show)

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

instance Functor TypeF where
  fmap _ (TypeVariable x) = TypeVariable x
  fmap f (Macro σ τ) = Macro (fmap f σ) (fmap f τ)
  fmap f (Forall (Bound pm σ)) = Forall $ Bound (bimap f f pm) (fmap f σ)
  fmap f (KindForall (Bound pm σ)) = KindForall $ Bound (fmap f pm) (fmap f σ)
  fmap f (OfCourse σ) = OfCourse (fmap f σ)
  fmap f (TypeConstruction σ τ) = TypeConstruction (fmap f σ) (fmap f τ)
  fmap f (TypeOperator (Bound pm σ)) = TypeOperator $ Bound (bimap f f pm) (fmap f σ)
  fmap f (FunctionPointer σ τs) = FunctionPointer (fmap f σ) (map (fmap f) τs)

type TypeInternal = Type Internal

data Type p = CoreType p (TypeF p) deriving (Show, Functor)

coreType = Isomorph (uncurry CoreType) $ \(CoreType p σ) -> (p, σ)

freeVariablesTypeImpl ::
  forall u p.
  ( Semigroup p,
    FreeVariables u p (Type p),
    FreeVariables u p (Bound (TypePattern p p) (Type p)),
    FreeVariables u p (Bound (KindPattern p) (Type p))
  ) =>
  TypeF p ->
  Variables p
freeVariablesTypeImpl (TypeVariable _) = mempty
freeVariablesTypeImpl (Macro σ τ) = freeVariables @u σ <> freeVariables @u τ
freeVariablesTypeImpl (Forall λ) = freeVariables @u λ
freeVariablesTypeImpl (KindForall λ) = freeVariables @u λ
freeVariablesTypeImpl (OfCourse σ) = freeVariables @u σ
freeVariablesTypeImpl (TypeConstruction σ τ) = freeVariables @u σ <> freeVariables @u τ
freeVariablesTypeImpl (TypeOperator λ) = freeVariables @u λ
freeVariablesTypeImpl (FunctionPointer σ τs) = freeVariables @u σ <> freeVariables @u τs

instance Semigroup p => FreeVariables (Type p) p (Type p) where
  freeVariables (CoreType p (TypeVariable x)) = Variables.singleton x p
  freeVariables (CoreType _ σ) = freeVariablesTypeImpl @(Type p) σ

instance Semigroup p => FreeVariables (Type p) p (Bound (TypePattern p p) (Type p)) where
  freeVariables (Bound pm σ) = removeBinds (freeVariables @(Type p) σ) (bindings @p pm)

instance Semigroup p => FreeVariables (Type p) p (Bound (KindPattern p) (Type p)) where
  freeVariables (Bound _ σ) = freeVariables @(Type p) σ

instance Semigroup p => FreeVariables (Kind p) p (Type p) where
  freeVariables (CoreType _ σ) = freeVariablesTypeImpl @(Kind p) σ

instance Semigroup p => FreeVariables (Kind p) p (Bound (TypePattern p p) (Type p)) where
  freeVariables (Bound pm σ) = freeVariables @(Kind p) pm <> freeVariables @(Kind p) σ

instance Semigroup p => FreeVariables (Kind p) p (Bound (KindPattern p) (Type p)) where
  freeVariables (Bound pm σ) = removeBinds (freeVariables @(Kind p) σ) (bindings @p pm)

instance Semigroup p => FreeVariables (Type p) p (Kind p) where
  freeVariables _ = mempty

avoidCaptureType = avoidCapture (CoreType Internal . TypeVariable) (freeVariablesInternal @TypeInternal)

substituteTypeImpl _ _ (TypeVariable x) = TypeVariable x
substituteTypeImpl ux x (Macro σ τ) = Macro (substitute ux x σ) (substitute ux x τ)
substituteTypeImpl ux x (Forall λ) = Forall (substitute ux x λ)
substituteTypeImpl ux x (KindForall λ) = KindForall (substitute ux x λ)
substituteTypeImpl ux x (OfCourse σ) = OfCourse (substitute ux x σ)
substituteTypeImpl ux x (TypeConstruction σ τ) = TypeConstruction (substitute ux x σ) (substitute ux x τ)
substituteTypeImpl ux x (TypeOperator λ) = TypeOperator (substitute ux x λ)
substituteTypeImpl ux x (FunctionPointer σ τs) = FunctionPointer (substitute ux x σ) (substitute ux x τs)

instance Substitute TypeInternal TypeInternal where
  substitute ux x (CoreType Internal (TypeVariable x')) | x == x' = ux
  substitute ux x (CoreType Internal σ) = CoreType Internal $ substituteTypeImpl ux x σ

instance Substitute TypeInternal (Bound TypePatternInternal TypeInternal) where
  substitute _ x λ@(Bound pm _) | x `Variables.member` bindingsInternal pm = λ
  substitute ux x λ = Bound pm (substitute ux x σ)
    where
      Bound pm σ = avoidCaptureType ux λ

instance Substitute TypeInternal (Bound KindPatternInternal TypeInternal) where
  substitute ux x λ = Bound pm (substitute ux x σ)
    where
      Bound pm σ = avoidCaptureKind ux λ

instance Substitute KindInternal TypeInternal where
  substitute ux x (CoreType Internal σ) = CoreType Internal $ substituteTypeImpl ux x σ

instance Substitute KindInternal (Bound TypePatternInternal TypeInternal) where
  substitute ux x (Bound pm σ) = Bound (substitute ux x pm) (substitute ux x σ)

instance Substitute KindInternal (Bound KindPatternInternal TypeInternal) where
  substitute _ x λ@(Bound pm _) | x `Variables.member` bindingsInternal pm = λ
  substitute ux x λ = Bound pm (substitute ux x σ)
    where
      Bound pm σ = avoidCaptureKind ux λ

instance Substitute TypeInternal KindInternal where
  substitute _ _ = id

reduceTypeImpl (TypeVariable x) = TypeVariable x
reduceTypeImpl (Macro σ τ) = Macro (reduce σ) (reduce τ)
reduceTypeImpl (Forall λ) = Forall (reduce λ)
reduceTypeImpl (KindForall λ) = KindForall (reduce λ)
reduceTypeImpl (OfCourse σ) = OfCourse (reduce σ)
reduceTypeImpl (TypeConstruction σ τ) | (CoreType Internal (TypeOperator λ)) <- reduce σ = let (CoreType Internal σ') = apply λ τ in σ'
reduceTypeImpl (TypeConstruction σ τ) = TypeConstruction (reduce σ) (reduce τ)
reduceTypeImpl (TypeOperator λ) = TypeOperator (reduce λ)
reduceTypeImpl (FunctionPointer σ τs) = FunctionPointer (reduce σ) (reduce τs)

instance Reduce TypeInternal where
  reduce (CoreType Internal σ) = CoreType Internal $ reduceTypeImpl σ

instance Apply (Bound TypePatternInternal TypeInternal) TypeInternal TypeInternal where
  apply (Bound (CoreTypePattern Internal (TypePatternVariable x _)) σ) ux = reduce $ substitute ux x σ

instance Apply (Bound KindPatternInternal TypeInternal) KindInternal TypeInternal where
  apply (Bound (CoreKindPattern Internal (KindPatternVariable x _)) σ) ux = reduce $ substitute ux x σ

instance Location Type where
  location (CoreType p _) = p
