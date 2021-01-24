module Core.Ast.Term where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.Pattern
import Core.Ast.Stage
import Core.Ast.StagePattern
import Core.Ast.Type
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import qualified Data.Set as Set
import Misc.Identifier
import qualified TypeSystem.Abstraction as TypeSystem
import qualified TypeSystem.Application as TypeSystem
import qualified TypeSystem.Bind as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.OfCourseIntroduction as TypeSystem
import qualified TypeSystem.StageAbstraction as TypeSystem
import qualified TypeSystem.StageApplication as TypeSystem
import qualified TypeSystem.TypeAbstraction as TypeSystem
import qualified TypeSystem.TypeApplication as TypeSystem
import qualified TypeSystem.Variable as TypeSystem

data TermF p
  = Variable Identifier
  | MacroAbstraction (Pattern (Type p) p) (Term p)
  | MacroApplication (Term p) (Term p)
  | TypeAbstraction (TypePattern (Kind p) p) (Term p)
  | TypeApplication (Term p) (Type p)
  | StageAbstraction (StagePattern p) (Term p)
  | StageApplication (Term p) (Stage p)
  | OfCourseIntroduction (Term p)
  | Bind (Pattern (Type p) p) (Term p) (Term p)
  deriving (Show)

instance Functor TermF where
  fmap _ (Variable x) = Variable x
  fmap f (MacroAbstraction pm e) = MacroAbstraction (bimap (fmap f) f pm) (fmap f e)
  fmap f (MacroApplication e1 e2) = MacroApplication (fmap f e1) (fmap f e2)
  fmap f (TypeAbstraction pm e) = TypeAbstraction (bimap (fmap f) f pm) (fmap f e)
  fmap f (TypeApplication e σ) = TypeApplication (fmap f e) (fmap f σ)
  fmap f (StageAbstraction pm e) = StageAbstraction (fmap f pm) (fmap f e)
  fmap f (StageApplication e s) = StageApplication (fmap f e) (fmap f s)
  fmap f (OfCourseIntroduction e) = OfCourseIntroduction (fmap f e)
  fmap f (Bind pm e1 e2) = Bind (bimap (fmap f) f pm) (fmap f e1) (fmap f e2)

data Term p = CoreTerm p (TermF p) deriving (Show, Functor)

type TermInternal = Term Internal

projectTerm ::
  TermF p ->
  Either
    (TypeSystem.Variable (Term p))
    ( Either
        (TypeSystem.Abstraction MultiplicityInternal (Pattern TypeInternal p) (Pattern (Type p) p) (Term p))
        ( Either
            (TypeSystem.Application (Term p))
            ( Either
                (TypeSystem.TypeAbstraction (TypePattern KindInternal Internal) (TypePattern KindInternal p) (TypePattern (Kind p) p) (Term p))
                ( Either
                    (TypeSystem.TypeApplication KindInternal (Type p) (Term p))
                    ( Either
                        ( TypeSystem.StageAbstraction StagePatternInternal (StagePattern p) (StagePattern p) (Term p)
                        )
                        ( Either
                            ( TypeSystem.StageApplication StageInternal (Stage p) (Term p)
                            )
                            ( Either
                                (TypeSystem.OfCourseIntroduction MultiplicityInternal (Term p))
                                (TypeSystem.Bind MultiplicityInternal (Pattern TypeInternal p) (Pattern (Type p) p) (Term p))
                            )
                        )
                    )
                )
            )
        )
    )
projectTerm (Variable x) = Left $ TypeSystem.Variable x
projectTerm (MacroAbstraction pm e) = Right $ Left $ TypeSystem.Abstraction pm e
projectTerm (MacroApplication e1 e2) = Right $ Right $ Left $ TypeSystem.Application e1 e2
projectTerm (TypeAbstraction pm e) = Right $ Right $ Right $ Left $ TypeSystem.TypeAbstraction pm e
projectTerm (TypeApplication e σ) = Right $ Right $ Right $ Right $ Left $ TypeSystem.TypeApplication e σ
projectTerm (StageAbstraction pm e) = Right $ Right $ Right $ Right $ Right $ Left $ TypeSystem.StageAbstraction pm e
projectTerm (StageApplication e s) = Right $ Right $ Right $ Right $ Right $ Right $ Left $ TypeSystem.StageApplication e s
projectTerm (OfCourseIntroduction e) = Right $ Right $ Right $ Right $ Right $ Right $ Right $ Left $ TypeSystem.OfCourseIntroduction e
projectTerm (Bind pm e1 e2) = Right $ Right $ Right $ Right $ Right $ Right $ Right $ Right $ TypeSystem.Bind pm e1 e2

instance TypeSystem.EmbedVariable TermInternal where
  variable x = CoreTerm Internal $ Variable x

instance TypeSystem.EmbedAbstraction (Pattern TypeInternal Internal) TermInternal where
  abstraction pm e = CoreTerm Internal $ MacroAbstraction pm e

instance TypeSystem.EmbedApplication TermInternal where
  application e1 e2 = CoreTerm Internal $ MacroApplication e1 e2

instance TypeSystem.EmbedTypeAbstraction (TypePattern KindInternal Internal) TermInternal where
  typeAbstraction pm e = CoreTerm Internal $ TypeAbstraction pm e

instance TypeSystem.EmbedTypeApplication TypeInternal TermInternal where
  typeApplication e σ = CoreTerm Internal $ TypeApplication e σ

instance TypeSystem.EmbedStageAbstraction StagePatternInternal TermInternal where
  stageAbstraction pm e = CoreTerm Internal $ StageAbstraction pm e

instance TypeSystem.EmbedStageApplication StageInternal TermInternal where
  stageApplication e s = CoreTerm Internal $ StageApplication e s

instance TypeSystem.EmbedOfCourseIntroduction TermInternal where
  ofCourseIntroduction e = CoreTerm Internal $ OfCourseIntroduction e

instance TypeSystem.EmbedBind (Pattern TypeInternal Internal) TermInternal where
  bind pm e1 e2 = CoreTerm Internal $ Bind pm e1 e2

instance FreeVariables TermInternal TermInternal where
  freeVariables (CoreTerm Internal e) = freeVariables @TermInternal $ projectTerm e

instance FreeVariables TermInternal (TypeSystem.Variable TermInternal) where
  freeVariables (TypeSystem.Variable x) = Set.singleton x

instance FreeVariables TypeInternal TermInternal where
  freeVariables (CoreTerm Internal e) = freeVariables @TypeInternal $ projectTerm e

instance FreeVariables TypeInternal (TypeSystem.Variable TermInternal) where
  freeVariables _ = Set.empty

instance FreeVariables StageInternal TermInternal where
  freeVariables (CoreTerm Internal e) = freeVariables @StageInternal $ projectTerm e

instance FreeVariables StageInternal (TypeSystem.Variable TermInternal) where
  freeVariables _ = Set.empty

instance FreeVariables TermInternal (Pattern TypeInternal Internal) where
  freeVariables _ = Set.empty

instance FreeVariables TermInternal (TypePattern KindInternal Internal) where
  freeVariables _ = Set.empty

instance FreeVariables TermInternal TypeInternal where
  freeVariables _ = Set.empty

instance FreeVariables TermInternal KindInternal where
  freeVariables _ = Set.empty

instance FreeVariables TermInternal StageInternal where
  freeVariables _ = Set.empty

instance ModifyVariables TermInternal (Pattern TypeInternal Internal) where
  modifyVariables (CorePattern Internal pm) free = foldr Set.delete free $ bindings (projectPattern pm)

instance ModifyVariables TermInternal (TypePattern KindInternal Internal) where
  modifyVariables _ free = free

instance ModifyVariables TermInternal StagePatternInternal where
  modifyVariables _ free = free

instance Substitute TermInternal TermInternal where
  substitute ex x (CoreTerm Internal e) = substituteImpl ex x $ projectTerm e

instance SubstituteImpl (TypeSystem.Variable TermInternal) TermInternal TermInternal where
  substituteImpl ex x (TypeSystem.Variable x') = substituteVariable TypeSystem.variable ex x x'

instance Substitute TypeInternal TermInternal where
  substitute σx x (CoreTerm Internal e) = substituteImpl σx x $ projectTerm e

instance SubstituteImpl (TypeSystem.Variable TermInternal) TypeInternal TermInternal where
  substituteImpl _ _ (TypeSystem.Variable x) = TypeSystem.variable x

instance Substitute StageInternal TermInternal where
  substitute sx x (CoreTerm Internal e) = substituteImpl sx x $ projectTerm e

instance SubstituteImpl (TypeSystem.Variable TermInternal) StageInternal TermInternal where
  substituteImpl _ _ (TypeSystem.Variable x) = TypeSystem.variable x

instance SubstituteSame TermInternal

instance Substitute TermInternal (Pattern TypeInternal Internal) where
  substitute _ _ pm = pm

instance Substitute TermInternal (TypePattern KindInternal Internal) where
  substitute _ _ pm = pm

instance Substitute TermInternal StagePatternInternal where
  substitute _ _ pm = pm

instance Substitute TermInternal TypeInternal where
  substitute _ _ σ = σ

instance Substitute TermInternal KindInternal where
  substitute _ _ κ = κ

instance Substitute TermInternal StageInternal where
  substitute _ _ s = s

instance CaptureAvoidingSubstitution TermInternal (Pattern TypeInternal Internal) TermInternal where
  avoidCapture ex (CorePattern Internal pm, e) = avoidCaptureImpl @TermInternal projectPattern (CorePattern Internal) ex (pm, e)
  substituteShadow = substituteShadowImpl

instance CaptureAvoidingSubstitution TypeInternal (Pattern TypeInternal Internal) TermInternal where
  avoidCapture _ = id
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution StageInternal (Pattern TypeInternal Internal) TermInternal where
  avoidCapture _ = id
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution TermInternal (TypePattern KindInternal Internal) TermInternal where
  avoidCapture ex (CoreTypePattern Internal pm, e) = avoidCaptureImpl @TypeInternal projectTypePattern (CoreTypePattern Internal) ex (pm, e)
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution TypeInternal (TypePattern KindInternal Internal) TermInternal where
  avoidCapture σx (CoreTypePattern Internal pm, e) = avoidCaptureImpl @TypeInternal projectTypePattern (CoreTypePattern Internal) σx (pm, e)
  substituteShadow = substituteShadowImpl

instance CaptureAvoidingSubstitution StageInternal (TypePattern KindInternal Internal) TermInternal where
  avoidCapture _ = id
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution TermInternal StagePatternInternal TermInternal where
  avoidCapture ex (CoreStagePattern Internal pm, e) = avoidCaptureImpl @StageInternal projectStagePattern (CoreStagePattern Internal) ex (pm, e)
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution TypeInternal StagePatternInternal TermInternal where
  avoidCapture σx (CoreStagePattern Internal pm, e) = avoidCaptureImpl @StageInternal projectStagePattern (CoreStagePattern Internal) σx (pm, e)
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution StageInternal StagePatternInternal TermInternal where
  avoidCapture sx (CoreStagePattern Internal pm, e) = avoidCaptureImpl @StageInternal projectStagePattern (CoreStagePattern Internal) sx (pm, e)
  substituteShadow = substituteShadowImpl

instance Reduce TermInternal where
  reduce (CoreTerm Internal e) = reduceImpl $ projectTerm e

instance ReducePattern (Pattern TypeInternal Internal) TermInternal TermInternal where
  reducePattern (CorePattern Internal pm) e1 e2 = reducePattern (projectPattern pm) e1 e2

instance ReducePattern (TypePattern KindInternal Internal) TypeInternal TermInternal where
  reducePattern (CoreTypePattern Internal pm) σ e = reducePattern (projectTypePattern pm) σ e

instance ReducePattern StagePatternInternal StageInternal TermInternal where
  reducePattern (CoreStagePattern Internal pm) s e = reducePattern (projectStagePattern pm) s e

instance ReduceMatchAbstraction TermInternal TermInternal where
  reduceMatchAbstraction (CoreTerm Internal (MacroAbstraction pm e1)) = Just $ \e2 -> reducePattern pm e2 e1
  reduceMatchAbstraction _ = Nothing

instance ReduceMatchAbstraction TypeInternal TermInternal where
  reduceMatchAbstraction (CoreTerm Internal (TypeAbstraction pm e)) = Just $ \σ -> reducePattern pm σ e
  reduceMatchAbstraction _ = Nothing

instance ReduceMatchAbstraction StageInternal TermInternal where
  reduceMatchAbstraction (CoreTerm Internal (StageAbstraction pm e)) = Just $ \s -> reducePattern pm s e
  reduceMatchAbstraction _ = Nothing

instance TypeSystem.MatchOfCourseIntroduction TermInternal where
  matchOfCourseIntroduction (CoreTerm Internal (OfCourseIntroduction e)) = Just (TypeSystem.OfCourseIntroduction e)
  matchOfCourseIntroduction _ = Nothing

instance Positioned (Term p) p where
  location (CoreTerm p _) = p
