module Core.Ast.Type where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.KindPattern
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import Data.Void (Void)
import Misc.Identifier (Identifier, substituteVariable)
import qualified Misc.Identifier as Variables
import qualified TypeSystem.Abstraction as TypeSystem
import qualified TypeSystem.Application as TypeSystem
import qualified TypeSystem.Forall as TypeSystem
import qualified TypeSystem.Function as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.OfCourse as TypeSystem
import qualified TypeSystem.StageForall as TypeSystem
import qualified TypeSystem.Variable as TypeSystem

data TypeF p
  = TypeVariable Identifier
  | Macro (Type p) (Type p)
  | Forall (TypePattern (Kind p) p) (Type p)
  | KindForall (KindPattern p) (Type p)
  | OfCourse (Type p)
  | TypeConstruction (Type p) (Type p)
  | TypeOperator (TypePattern (Kind p) p) (Type p)
  deriving (Show)

instance Functor TypeF where
  fmap _ (TypeVariable x) = TypeVariable x
  fmap f (Macro σ τ) = Macro (fmap f σ) (fmap f τ)
  fmap f (Forall pm σ) = Forall (bimap (fmap f) f pm) (fmap f σ)
  fmap f (KindForall pm σ) = KindForall (fmap f pm) (fmap f σ)
  fmap f (OfCourse σ) = OfCourse (fmap f σ)
  fmap f (TypeConstruction σ τ) = TypeConstruction (fmap f σ) (fmap f τ)
  fmap f (TypeOperator pm σ) = TypeOperator (bimap (fmap f) f pm) (fmap f σ)

type TypeInternal = Type Internal

data Type p = CoreType p (TypeF p) deriving (Show, Functor)

projectType ::
  TypeF p ->
  Either
    (TypeSystem.Variable (Type p))
    ( Either
        (TypeSystem.Function KindInternal (Type p))
        ( Either
            (TypeSystem.Forall KindInternal (TypePattern KindInternal p) (TypePattern (Kind p) p) (Type p))
            ( Either
                (TypeSystem.StageForall KindInternal (KindPattern p) (KindPattern p) (Type p))
                ( Either
                    (TypeSystem.OfCourse KindInternal (Type p))
                    ( Either
                        (TypeSystem.Application (Type p))
                        (TypeSystem.Abstraction Void (TypePattern KindInternal p) (TypePattern (Kind p) p) (Type p))
                    )
                )
            )
        )
    )
projectType (TypeVariable x) = Left $ TypeSystem.Variable x
projectType (Macro σ τ) = Right $ Left $ TypeSystem.Function σ τ
projectType (Forall pm σ) = Right $ Right $ Left $ TypeSystem.Forall pm σ
projectType (KindForall pm σ) = Right $ Right $ Right $ Left $ TypeSystem.StageForall pm σ
projectType (OfCourse σ) = Right $ Right $ Right $ Right $ Left $ TypeSystem.OfCourse σ
projectType (TypeConstruction σ τ) = Right $ Right $ Right $ Right $ Right $ Left $ TypeSystem.Application σ τ
projectType (TypeOperator pm σ) = Right $ Right $ Right $ Right $ Right $ Right $ TypeSystem.Abstraction pm σ

instance TypeSystem.EmbedVariable TypeInternal where
  variable x = CoreType Internal $ TypeVariable x

instance TypeSystem.EmbedFunction TypeInternal where
  function σ τ = CoreType Internal $ Macro σ τ

instance TypeSystem.EmbedForall TypePatternInternal TypeInternal where
  forallx pm σ = CoreType Internal $ Forall pm σ

instance TypeSystem.EmbedStageForall KindPatternInternal TypeInternal where
  stageForall pm σ = CoreType Internal $ KindForall pm σ

instance TypeSystem.EmbedOfCourse TypeInternal where
  ofCourse σ = CoreType Internal $ OfCourse σ

instance TypeSystem.EmbedAbstraction TypePatternInternal TypeInternal where
  abstraction pm σ = CoreType Internal $ TypeOperator pm σ

instance TypeSystem.EmbedApplication TypeInternal where
  application σ τ = CoreType Internal $ TypeConstruction σ τ

instance Semigroup p => FreeVariables (Type p) p (Type p) where
  freeVariables (CoreType p σ) = freeVariablesImpl @(Type p) p $ projectType σ

instance Semigroup p => FreeVariablesImpl (Type p) p (TypeSystem.Variable (Type p)) where
  freeVariablesImpl p (TypeSystem.Variable x) = Variables.singleton x p

instance Semigroup p => FreeVariables (Kind p) p (Type p) where
  freeVariables (CoreType p σ) = freeVariablesImpl @(Kind p) p $ projectType σ

instance Semigroup p => FreeVariablesImpl (Kind p) p (TypeSystem.Variable (Type p)) where
  freeVariablesImpl _ _ = mempty

instance Semigroup p => FreeVariables (Type p) p (TypePattern (Kind p) p) where
  freeVariables _ = mempty

instance Semigroup p => FreeVariables (Type p) p (Kind p) where
  freeVariables _ = mempty

instance FreeVariablesInternal TypeInternal TypeInternal where
  freeVariablesInternal = freeVariables @TypeInternal

instance FreeVariablesInternal KindInternal TypeInternal where
  freeVariablesInternal = freeVariables @KindInternal

instance Semigroup p => ModifyVariables (Type p) p (TypePattern (Kind p) p) where
  modifyVariables (CoreTypePattern _ pm) free = foldr Variables.delete free $ bindings (projectTypePattern pm)

instance Semigroup p => ModifyVariables (Type p) p (KindPattern p) where
  modifyVariables _ = id

instance Substitute TypeInternal TypeInternal where
  substitute σx x (CoreType Internal σ) = substituteImpl σx x $ projectType σ

instance SubstituteImpl (TypeSystem.Variable TypeInternal) TypeInternal TypeInternal where
  substituteImpl σx x (TypeSystem.Variable x') = substituteVariable TypeSystem.variable σx x x'

instance Substitute KindInternal TypeInternal where
  substitute sx x (CoreType Internal σ) = substituteImpl sx x $ projectType σ

instance SubstituteImpl (TypeSystem.Variable TypeInternal) KindInternal TypeInternal where
  substituteImpl _ _ (TypeSystem.Variable x) = TypeSystem.variable x

instance SubstituteSame TypeInternal

instance Substitute TypeInternal TypePatternInternal where
  substitute _ _ pm = pm

instance Substitute TypeInternal KindInternal where
  substitute _ _ κ = κ

instance Substitute TypeInternal KindPatternInternal where
  substitute _ _ pm = pm

instance CaptureAvoidingSubstitution TypeInternal TypePatternInternal TypeInternal where
  avoidCapture σx (CoreTypePattern Internal pm, σ) = avoidCaptureImpl @TypeInternal projectTypePattern (CoreTypePattern Internal) σx (pm, σ)
  substituteShadow = substituteShadowImpl

instance CaptureAvoidingSubstitution KindInternal TypePatternInternal TypeInternal where
  avoidCapture _ = id
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution TypeInternal KindPatternInternal TypeInternal where
  avoidCapture σx (CoreKindPattern Internal pm, σ) = avoidCaptureImpl @KindInternal projectKindPattern (CoreKindPattern Internal) σx (pm, σ)
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution KindInternal KindPatternInternal TypeInternal where
  avoidCapture sx (CoreKindPattern Internal pm, σ) = avoidCaptureImpl @KindInternal projectKindPattern (CoreKindPattern Internal) sx (pm, σ)
  substituteShadow = substituteShadowImpl

instance Reduce TypeInternal where
  reduce (CoreType Internal σ) = reduceImpl $ projectType σ

instance ReducePattern TypePatternInternal TypeInternal TypeInternal where
  reducePattern (CoreTypePattern Internal pm) σ τ = reducePattern (projectTypePattern pm) σ τ

instance ReducePattern KindPatternInternal KindInternal TypeInternal where
  reducePattern (CoreKindPattern Internal pm) s τ = reducePattern (projectKindPattern pm) s τ

instance ReduceMatchAbstraction TypeInternal TypeInternal where
  reduceMatchAbstraction (CoreType Internal (TypeOperator pm σ)) = Just $ \τ -> reducePattern pm τ σ
  reduceMatchAbstraction _ = Nothing

instance Positioned (Type p) p where
  location (CoreType p _) = p
