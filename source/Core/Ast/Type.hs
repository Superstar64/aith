module Core.Ast.Type where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Stage
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import qualified Data.Set as Set
import Misc.Identifier
import qualified TypeSystem.Abstraction as TypeSystem
import qualified TypeSystem.Application as TypeSystem
import qualified TypeSystem.Forall as TypeSystem
import qualified TypeSystem.Function as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.OfCourse as TypeSystem
import qualified TypeSystem.Variable as TypeSystem

data TypeF p
  = TypeVariable Identifier
  | Macro (Type p) (Type p)
  | Forall (TypePattern (Kind p) p) (Type p)
  | OfCourse (Type p)
  | TypeConstruction (Type p) (Type p)
  | TypeOperator (TypePattern (Kind p) p) (Type p)
  deriving (Show)

instance Functor TypeF where
  fmap _ (TypeVariable x) = TypeVariable x
  fmap f (Macro σ τ) = Macro (fmap f σ) (fmap f τ)
  fmap f (Forall pm σ) = Forall (bimap (fmap f) f pm) (fmap f σ)
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
        (TypeSystem.Function StageInternal (Type p))
        ( Either
            (TypeSystem.Forall StageInternal (TypePattern KindInternal p) (TypePattern (Kind p) p) (Type p))
            ( Either
                (TypeSystem.OfCourse StageInternal (Type p))
                ( Either
                    (TypeSystem.Application (Type p))
                    (TypeSystem.Abstraction () (TypePattern KindInternal p) (TypePattern (Kind p) p) (Type p))
                )
            )
        )
    )
projectType (TypeVariable x) = Left $ TypeSystem.Variable x
projectType (Macro σ τ) = Right $ Left $ TypeSystem.Function σ τ
projectType (Forall pm σ) = Right $ Right $ Left $ TypeSystem.Forall pm σ
projectType (OfCourse σ) = Right $ Right $ Right $ Left $ TypeSystem.OfCourse σ
projectType (TypeConstruction σ τ) = Right $ Right $ Right $ Right $ Left $ TypeSystem.Application σ τ
projectType (TypeOperator pm σ) = Right $ Right $ Right $ Right $ Right $ TypeSystem.Abstraction pm σ

instance TypeSystem.EmbedVariable TypeInternal where
  variable x = CoreType Internal $ TypeVariable x

instance TypeSystem.EmbedFunction TypeInternal where
  function σ τ = CoreType Internal $ Macro σ τ

instance TypeSystem.EmbedForall (TypePattern KindInternal Internal) TypeInternal where
  forallx pm σ = CoreType Internal $ Forall pm σ

instance TypeSystem.EmbedOfCourse TypeInternal where
  ofCourse σ = CoreType Internal $ OfCourse σ

instance TypeSystem.EmbedAbstraction (TypePattern KindInternal Internal) TypeInternal where
  abstraction pm σ = CoreType Internal $ TypeOperator pm σ

instance TypeSystem.EmbedApplication TypeInternal where
  application σ τ = CoreType Internal $ TypeConstruction σ τ

instance FreeVariables TypeInternal TypeInternal where
  freeVariables' (CoreType Internal σ) = freeVariables @TypeInternal $ projectType σ

instance FreeVariables (TypeSystem.Variable TypeInternal) TypeInternal where
  freeVariables' (TypeSystem.Variable x) = Set.singleton x

instance FreeVariables (TypePattern KindInternal Internal) TypeInternal where
  freeVariables' (CoreTypePattern Internal pm) = freeVariables @TypeInternal $ projectTypePattern pm

instance FreeVariables KindInternal TypeInternal where
  freeVariables' _ = Set.empty

instance ModifyVariables TypeInternal (TypePattern KindInternal Internal) where
  modifyVariables (CoreTypePattern Internal pm) free = foldr Set.delete free $ bindings (projectTypePattern pm)

instance Substitute TypeInternal TypeInternal where
  substitute σx x (CoreType Internal σ) = substituteImpl σx x $ projectType σ

instance SubstituteSame TypeInternal

instance SubstituteImpl (TypeSystem.Variable TypeInternal) TypeInternal TypeInternal where
  substituteImpl σx x (TypeSystem.Variable x') = substituteVariable TypeSystem.variable σx x x'

instance Substitute TypeInternal (TypePattern KindInternal Internal) where
  substitute _ _ pm = pm

instance Substitute TypeInternal KindInternal where
  substitute _ _ κ = κ

instance AvoidCapture TypeInternal (TypePattern KindInternal Internal) TypeInternal where
  avoidCapture σx (CoreTypePattern Internal pm, σ) = avoidCaptureImpl @TypeInternal projectTypePattern (CoreTypePattern Internal) σx (pm, σ)

instance Reduce TypeInternal where
  reduce (CoreType Internal σ) = reduceImpl $ projectType σ

instance ReducePattern (TypePattern KindInternal Internal) TypeInternal where
  reducePattern (CoreTypePattern Internal pm) σ τ = reducePattern (projectTypePattern pm) σ τ

instance ReduceMatchAbstraction TypeInternal TypeInternal where
  reduceMatchAbstraction (CoreType Internal (TypeOperator (CoreTypePattern Internal (TypePatternVariable x _)) σ1)) = Just $ \σ2 -> substitute σ2 x σ1
  reduceMatchAbstraction _ = Nothing

instance Positioned (Type p) p where
  location (CoreType p _) = p
