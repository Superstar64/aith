module Core.Ast.Term where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.KindPattern
import Core.Ast.Multiplicity
import Core.Ast.Pattern
import Core.Ast.Sort
import Core.Ast.Type
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import Misc.Identifier (Identifier, substituteVariable)
import qualified Misc.Identifier as Variables
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
  | KindAbstraction (KindPattern p) (Term p)
  | KindApplication (Term p) (Kind p)
  | OfCourseIntroduction (Term p)
  | Bind (Pattern (Type p) p) (Term p) (Term p)
  deriving (Show)

instance Functor TermF where
  fmap _ (Variable x) = Variable x
  fmap f (MacroAbstraction pm e) = MacroAbstraction (bimap (fmap f) f pm) (fmap f e)
  fmap f (MacroApplication e1 e2) = MacroApplication (fmap f e1) (fmap f e2)
  fmap f (TypeAbstraction pm e) = TypeAbstraction (bimap (fmap f) f pm) (fmap f e)
  fmap f (TypeApplication e σ) = TypeApplication (fmap f e) (fmap f σ)
  fmap f (KindAbstraction pm e) = KindAbstraction (fmap f pm) (fmap f e)
  fmap f (KindApplication e s) = KindApplication (fmap f e) (fmap f s)
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
                (TypeSystem.TypeAbstraction TypePatternInternal (TypePattern KindInternal p) (TypePattern (Kind p) p) (Term p))
                ( Either
                    (TypeSystem.TypeApplication KindInternal (Type p) (Term p))
                    ( Either
                        ( TypeSystem.StageAbstraction KindPatternInternal (KindPattern p) (KindPattern p) (Term p)
                        )
                        ( Either
                            ( TypeSystem.StageApplication Sort KindInternal (Kind p) (Term p)
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
projectTerm (KindAbstraction pm e) = Right $ Right $ Right $ Right $ Right $ Left $ TypeSystem.StageAbstraction pm e
projectTerm (KindApplication e s) = Right $ Right $ Right $ Right $ Right $ Right $ Left $ TypeSystem.StageApplication e s
projectTerm (OfCourseIntroduction e) = Right $ Right $ Right $ Right $ Right $ Right $ Right $ Left $ TypeSystem.OfCourseIntroduction e
projectTerm (Bind pm e1 e2) = Right $ Right $ Right $ Right $ Right $ Right $ Right $ Right $ TypeSystem.Bind pm e1 e2

instance TypeSystem.EmbedVariable TermInternal where
  variable x = CoreTerm Internal $ Variable x

instance TypeSystem.EmbedAbstraction PatternInternal TermInternal where
  abstraction pm e = CoreTerm Internal $ MacroAbstraction pm e

instance TypeSystem.EmbedApplication TermInternal where
  application e1 e2 = CoreTerm Internal $ MacroApplication e1 e2

instance TypeSystem.EmbedTypeAbstraction TypePatternInternal TermInternal where
  typeAbstraction pm e = CoreTerm Internal $ TypeAbstraction pm e

instance TypeSystem.EmbedTypeApplication TypeInternal TermInternal where
  typeApplication e σ = CoreTerm Internal $ TypeApplication e σ

instance TypeSystem.EmbedStageAbstraction KindPatternInternal TermInternal where
  stageAbstraction pm e = CoreTerm Internal $ KindAbstraction pm e

instance TypeSystem.EmbedStageApplication KindInternal TermInternal where
  stageApplication e s = CoreTerm Internal $ KindApplication e s

instance TypeSystem.EmbedOfCourseIntroduction TermInternal where
  ofCourseIntroduction e = CoreTerm Internal $ OfCourseIntroduction e

instance TypeSystem.EmbedBind PatternInternal TermInternal where
  bind pm e1 e2 = CoreTerm Internal $ Bind pm e1 e2

instance Semigroup p => FreeVariables (Term p) p (Term p) where
  freeVariables (CoreTerm p e) = freeVariablesImpl @(Term p) p $ projectTerm e

instance Semigroup p => FreeVariablesImpl (Term p) p (TypeSystem.Variable (Term p)) where
  freeVariablesImpl p (TypeSystem.Variable x) = Variables.singleton x p

instance Semigroup p => FreeVariables (Type p) p (Term p) where
  freeVariables (CoreTerm p e) = freeVariablesImpl @(Type p) p $ projectTerm e

instance Semigroup p => FreeVariablesImpl (Type p) p (TypeSystem.Variable (Term p)) where
  freeVariablesImpl _ _ = mempty

instance Semigroup p => FreeVariables (Kind p) p (Term p) where
  freeVariables (CoreTerm p e) = freeVariablesImpl @(Kind p) p $ projectTerm e

instance Semigroup p => FreeVariablesImpl (Kind p) p (TypeSystem.Variable (Term p)) where
  freeVariablesImpl _ _ = mempty

instance Semigroup p => FreeVariables (Term p) p (Pattern (Type p) p) where
  freeVariables _ = mempty

instance Semigroup p => FreeVariables (Term p) p (TypePattern (Kind p) p) where
  freeVariables _ = mempty

instance Semigroup p => FreeVariables (Term p) p (Type p) where
  freeVariables _ = mempty

instance Semigroup p => FreeVariables (Term p) p (Kind p) where
  freeVariables _ = mempty

instance FreeVariablesInternal TermInternal TermInternal where
  freeVariablesInternal = freeVariables @TermInternal

instance FreeVariablesInternal TypeInternal TermInternal where
  freeVariablesInternal = freeVariables @TypeInternal

instance FreeVariablesInternal KindInternal TermInternal where
  freeVariablesInternal = freeVariables @KindInternal

instance Semigroup p => ModifyVariables (Term p) p (Pattern (Type p) p) where
  modifyVariables (CorePattern _ pm) free = foldr Variables.delete free $ bindings (projectPattern pm)

instance Semigroup p => ModifyVariables (Term p) p (TypePattern (Kind p) p) where
  modifyVariables _ free = free

instance Semigroup p => ModifyVariables (Term p) p (KindPattern p) where
  modifyVariables _ free = free

instance Substitute TermInternal TermInternal where
  substitute ex x (CoreTerm Internal e) = substituteImpl ex x $ projectTerm e

instance SubstituteImpl (TypeSystem.Variable TermInternal) TermInternal TermInternal where
  substituteImpl ex x (TypeSystem.Variable x') = substituteVariable TypeSystem.variable ex x x'

instance Substitute TypeInternal TermInternal where
  substitute σx x (CoreTerm Internal e) = substituteImpl σx x $ projectTerm e

instance SubstituteImpl (TypeSystem.Variable TermInternal) TypeInternal TermInternal where
  substituteImpl _ _ (TypeSystem.Variable x) = TypeSystem.variable x

instance Substitute KindInternal TermInternal where
  substitute sx x (CoreTerm Internal e) = substituteImpl sx x $ projectTerm e

instance SubstituteImpl (TypeSystem.Variable TermInternal) KindInternal TermInternal where
  substituteImpl _ _ (TypeSystem.Variable x) = TypeSystem.variable x

instance SubstituteSame TermInternal

instance Substitute TermInternal PatternInternal where
  substitute _ _ pm = pm

instance Substitute TermInternal TypePatternInternal where
  substitute _ _ pm = pm

instance Substitute TermInternal KindPatternInternal where
  substitute _ _ pm = pm

instance Substitute TermInternal TypeInternal where
  substitute _ _ σ = σ

instance Substitute TermInternal KindInternal where
  substitute _ _ κ = κ

instance CaptureAvoidingSubstitution TermInternal PatternInternal TermInternal where
  avoidCapture ex (CorePattern Internal pm, e) = avoidCaptureImpl @TermInternal projectPattern (CorePattern Internal) ex (pm, e)
  substituteShadow = substituteShadowImpl

instance CaptureAvoidingSubstitution TypeInternal PatternInternal TermInternal where
  avoidCapture _ = id
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution KindInternal PatternInternal TermInternal where
  avoidCapture _ = id
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution TermInternal TypePatternInternal TermInternal where
  avoidCapture ex (CoreTypePattern Internal pm, e) = avoidCaptureImpl @TypeInternal projectTypePattern (CoreTypePattern Internal) ex (pm, e)
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution TypeInternal TypePatternInternal TermInternal where
  avoidCapture σx (CoreTypePattern Internal pm, e) = avoidCaptureImpl @TypeInternal projectTypePattern (CoreTypePattern Internal) σx (pm, e)
  substituteShadow = substituteShadowImpl

instance CaptureAvoidingSubstitution KindInternal TypePatternInternal TermInternal where
  avoidCapture _ = id
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution TermInternal KindPatternInternal TermInternal where
  avoidCapture ex (CoreKindPattern Internal pm, e) = avoidCaptureImpl @KindInternal projectKindPattern (CoreKindPattern Internal) ex (pm, e)
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution TypeInternal KindPatternInternal TermInternal where
  avoidCapture σx (CoreKindPattern Internal pm, e) = avoidCaptureImpl @KindInternal projectKindPattern (CoreKindPattern Internal) σx (pm, e)
  substituteShadow _ = substitute

instance CaptureAvoidingSubstitution KindInternal KindPatternInternal TermInternal where
  avoidCapture sx (CoreKindPattern Internal pm, e) = avoidCaptureImpl @KindInternal projectKindPattern (CoreKindPattern Internal) sx (pm, e)
  substituteShadow = substituteShadowImpl

instance Reduce TermInternal where
  reduce (CoreTerm Internal e) = reduceImpl $ projectTerm e

instance ReducePattern PatternInternal TermInternal TermInternal where
  reducePattern (CorePattern Internal pm) e1 e2 = reducePattern (projectPattern pm) e1 e2

instance ReducePattern TypePatternInternal TypeInternal TermInternal where
  reducePattern (CoreTypePattern Internal pm) σ e = reducePattern (projectTypePattern pm) σ e

instance ReducePattern KindPatternInternal KindInternal TermInternal where
  reducePattern (CoreKindPattern Internal pm) s e = reducePattern (projectKindPattern pm) s e

instance ReduceMatchAbstraction TermInternal TermInternal where
  reduceMatchAbstraction (CoreTerm Internal (MacroAbstraction pm e1)) = Just $ \e2 -> reducePattern pm e2 e1
  reduceMatchAbstraction _ = Nothing

instance ReduceMatchAbstraction TypeInternal TermInternal where
  reduceMatchAbstraction (CoreTerm Internal (TypeAbstraction pm e)) = Just $ \σ -> reducePattern pm σ e
  reduceMatchAbstraction _ = Nothing

instance ReduceMatchAbstraction KindInternal TermInternal where
  reduceMatchAbstraction (CoreTerm Internal (KindAbstraction pm e)) = Just $ \s -> reducePattern pm s e
  reduceMatchAbstraction _ = Nothing

instance TypeSystem.MatchOfCourseIntroduction TermInternal where
  matchOfCourseIntroduction (CoreTerm Internal (OfCourseIntroduction e)) = Just (TypeSystem.OfCourseIntroduction e)
  matchOfCourseIntroduction _ = Nothing

instance Positioned (Term p) p where
  location (CoreTerm p _) = p
