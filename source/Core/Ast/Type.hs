module Core.Ast.Type where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.Stage
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import qualified Data.Set as Set
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same)
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
        (TypeSystem.Function Stage (Type p))
        ( Either
            (TypeSystem.Forall Stage (TypePattern KindInternal p) (TypePattern (Kind p) p) (Type p))
            ( Either
                (TypeSystem.OfCourse Stage (Type p))
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

instance i ~ Internal => TypeSystem.EmbedVariable (Type i) where
  variable x = CoreType Internal $ TypeVariable x

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedFunction (Type i) where
  function σ τ = CoreType Internal $ Macro σ τ

instance (i ~ Internal, i' ~ Internal, κ ~ KindInternal) => TypeSystem.EmbedForall (TypePattern κ i) (Type i') where
  forallx pm σ = CoreType Internal $ Forall pm σ

instance (i ~ Internal) => TypeSystem.EmbedOfCourse (Type i) where
  ofCourse σ = CoreType Internal $ OfCourse σ

instance (i ~ Internal, i' ~ Internal, κ ~ KindInternal) => TypeSystem.EmbedAbstraction (TypePattern κ i) (Type i') where
  abstraction pm σ = CoreType Internal $ TypeOperator pm σ

instance (i ~ Internal) => TypeSystem.EmbedApplication (Type i) where
  application σ τ = CoreType Internal $ TypeConstruction σ τ

instance (i ~ Internal, i' ~ Internal) => Same (Type i) (Type i) where
  same = Just Refl

instance (i ~ Internal, i' ~ Internal) => Same (Multiplicity i) (Type i') where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => Same (Type i) (Multiplicity i') where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Type i) (Type i') where
  freeVariables' (CoreType Internal σ) = freeVariables @TypeInternal $ projectType σ

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Type i) (Multiplicity i') where
  freeVariables' (CoreType Internal σ) = freeVariables @MultiplicityInternal $ projectType σ

instance (i ~ Internal, i' ~ Internal, κ ~ KindInternal) => FreeVariables (TypePattern κ i) (Type i') where
  freeVariables' (CoreTypePattern Internal pm) = freeVariables @TypeInternal $ projectTypePattern pm

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Kind i) (Type i') where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Multiplicity i') (Type i) where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => Substitute (Type i) (Type i') where
  substitute σx x (CoreType Internal σ) = substituteImpl σx x $ projectType σ

instance (i ~ Internal) => SubstituteSame (Type i)

instance (i ~ Internal, i' ~ Internal) => Substitute (Multiplicity i) (Type i') where
  substitute l x (CoreType Internal σ) = substituteImpl l x $ projectType σ

instance (i ~ Internal, i' ~ Internal, κ ~ KindInternal) => Substitute (Type i) (TypePattern κ i') where
  substitute _ _ pm = pm

instance (i ~ Internal, i' ~ Internal) => Substitute (Type i) (Multiplicity i') where
  substitute _ _ l = l

instance Substitute (Type i) (Kind i) where
  substitute _ _ κ = κ

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal, κ ~ KindInternal) => AvoidCapturePattern (Type i) (TypePattern κ i') (Type i'') where
  avoidCapturePattern u (CoreTypePattern Internal pm, σ) = avoidCapturePatternImpl u (projectTypePattern pm, σ)

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal, κ ~ KindInternal) => AvoidCapturePattern (Multiplicity i) (TypePattern κ i') (Type i'') where
  avoidCapturePattern u (CoreTypePattern Internal pm, σ) = avoidCapturePatternImpl u (projectTypePattern pm, σ)

instance (i ~ Internal) => Reduce (Type i) where
  reduce (CoreType Internal σ) = reduceImpl $ projectType σ

instance (i ~ Internal, i' ~ Internal, κ ~ KindInternal) => ReducePattern (TypePattern κ i) (Type i') where
  reducePattern (CoreTypePattern Internal pm) σ τ = reducePattern (projectTypePattern pm) σ τ

instance (i ~ Internal, i' ~ Internal) => ReduceMatchAbstraction (Type i) (Type i) where
  reduceMatchAbstraction (CoreType Internal (TypeOperator (CoreTypePattern Internal (TypePatternVariable x _)) σ1)) = Just $ \σ2 -> substitute σ2 x σ1
  reduceMatchAbstraction _ = Nothing

instance Positioned (Type p) p where
  location (CoreType p _) = p
