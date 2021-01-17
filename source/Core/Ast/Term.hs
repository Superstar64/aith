module Core.Ast.Term where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.Pattern
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
import qualified TypeSystem.TypeAbstraction as TypeSystem
import qualified TypeSystem.TypeApplication as TypeSystem
import qualified TypeSystem.Variable as TypeSystem

data TermF p
  = Variable Identifier
  | MacroAbstraction (Pattern (Type p) p) (Term p)
  | MacroApplication (Term p) (Term p)
  | TypeAbstraction (TypePattern (Kind p) p) (Term p)
  | TypeApplication (Term p) (Type p)
  | OfCourseIntroduction (Term p)
  | Bind (Pattern (Type p) p) (Term p) (Term p)
  deriving (Show)

instance Functor TermF where
  fmap _ (Variable x) = Variable x
  fmap f (MacroAbstraction pm e) = MacroAbstraction (bimap (fmap f) f pm) (fmap f e)
  fmap f (MacroApplication e1 e2) = MacroApplication (fmap f e1) (fmap f e2)
  fmap f (TypeAbstraction pm e) = TypeAbstraction (bimap (fmap f) f pm) (fmap f e)
  fmap f (TypeApplication e σ) = TypeApplication (fmap f e) (fmap f σ)
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
                (TypeSystem.TypeAbstraction TypeInternal (TypePattern KindInternal Internal) (TypePattern KindInternal p) (TypePattern (Kind p) p) (Term p))
                ( Either
                    (TypeSystem.TypeApplication KindInternal (Type p) (Term p))
                    ( Either
                        (TypeSystem.OfCourseIntroduction MultiplicityInternal (Term p))
                        (TypeSystem.Bind MultiplicityInternal (Pattern TypeInternal p) (Pattern (Type p) p) (Term p))
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
projectTerm (OfCourseIntroduction e) = Right $ Right $ Right $ Right $ Right $ Left $ TypeSystem.OfCourseIntroduction e
projectTerm (Bind pm e1 e2) = Right $ Right $ Right $ Right $ Right $ Right $ TypeSystem.Bind pm e1 e2

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

instance TypeSystem.EmbedOfCourseIntroduction TermInternal where
  ofCourseIntroduction e = CoreTerm Internal $ OfCourseIntroduction e

instance TypeSystem.EmbedBind (Pattern TypeInternal Internal) TermInternal where
  bind pm e1 e2 = CoreTerm Internal $ Bind pm e1 e2

instance FreeVariables TermInternal TermInternal where
  freeVariables' (CoreTerm Internal e) = freeVariables @TermInternal $ projectTerm e

instance FreeVariables (TypeSystem.Variable TermInternal) TermInternal where
  freeVariables' (TypeSystem.Variable x) = Set.singleton x

instance FreeVariables TermInternal TypeInternal where
  freeVariables' (CoreTerm Internal e) = freeVariables @TypeInternal $ projectTerm e

instance FreeVariables (TypeSystem.Variable TermInternal) TypeInternal where
  freeVariables' _ = Set.empty

instance FreeVariables (Pattern TypeInternal Internal) TermInternal where
  freeVariables' _ = Set.empty

instance FreeVariables (TypePattern KindInternal Internal) TermInternal where
  freeVariables' _ = Set.empty

instance FreeVariables TypeInternal TermInternal where
  freeVariables' _ = Set.empty

instance FreeVariables KindInternal TermInternal where
  freeVariables' _ = Set.empty

instance ModifyVariables TermInternal (Pattern TypeInternal Internal) where
  modifyVariables (CorePattern Internal pm) free = foldr Set.delete free $ bindings (projectPattern pm)

instance ModifyVariables TermInternal (TypePattern KindInternal Internal) where
  modifyVariables _ free = free

instance Substitute TermInternal TermInternal where
  substitute ex x (CoreTerm Internal e) = substituteImpl ex x $ projectTerm e

instance SubstituteImpl (TypeSystem.Variable TermInternal) TermInternal TermInternal where
  substituteImpl ex x (TypeSystem.Variable x') = substituteVariable TypeSystem.variable ex x x'

instance Substitute TypeInternal TermInternal where
  substitute σx x (CoreTerm Internal e) = substituteImpl σx x $ projectTerm e

instance SubstituteImpl (TypeSystem.Variable TermInternal) TypeInternal TermInternal where
  substituteImpl _ _ (TypeSystem.Variable x) = TypeSystem.variable x

instance SubstituteSame TermInternal

instance Substitute TermInternal (Pattern TypeInternal Internal) where
  substitute _ _ pm = pm

instance Substitute TermInternal (TypePattern KindInternal Internal) where
  substitute _ _ pm = pm

instance Substitute TermInternal TypeInternal where
  substitute _ _ σ = σ

instance Substitute TermInternal KindInternal where
  substitute _ _ κ = κ

instance AvoidCapture TermInternal (Pattern TypeInternal Internal) TermInternal where
  avoidCapture ex (CorePattern Internal pm, e) = avoidCaptureImpl @TermInternal projectPattern (CorePattern Internal) ex (pm, e)

instance AvoidCapture TypeInternal (Pattern TypeInternal Internal) TermInternal where
  avoidCapture _ = id

instance AvoidCapture TermInternal (TypePattern KindInternal Internal) TermInternal where
  avoidCapture ex (CoreTypePattern Internal pm, e) = avoidCaptureImpl @TypeInternal projectTypePattern (CoreTypePattern Internal) ex (pm, e)

instance AvoidCapture TypeInternal (TypePattern KindInternal Internal) TermInternal where
  avoidCapture σx (CoreTypePattern Internal pm, e) = avoidCaptureImpl @TypeInternal projectTypePattern (CoreTypePattern Internal) σx (pm, e)

instance Reduce TermInternal where
  reduce (CoreTerm Internal e) = reduceImpl $ projectTerm e

instance ReducePattern (Pattern TypeInternal Internal) TermInternal where
  reducePattern (CorePattern Internal pm) e1 e2 = reducePattern (projectPattern pm) e1 e2

instance ReduceMatchAbstraction TermInternal TermInternal where
  reduceMatchAbstraction (CoreTerm Internal (MacroAbstraction pm e1)) = Just $ \e2 -> reducePattern pm e2 e1
  reduceMatchAbstraction _ = Nothing

instance ReduceMatchAbstraction TypeInternal TermInternal where
  reduceMatchAbstraction (CoreTerm Internal (TypeAbstraction (CoreTypePattern Internal (TypePatternVariable x _)) e)) = Just $ \σ -> reduce $ substitute σ x e
  reduceMatchAbstraction _ = Nothing

instance TypeSystem.MatchOfCourseIntroduction TermInternal where
  matchOfCourseIntroduction (CoreTerm Internal (OfCourseIntroduction e)) = Just (TypeSystem.OfCourseIntroduction e)
  matchOfCourseIntroduction _ = Nothing

instance Positioned (Term p) p where
  location (CoreTerm p _) = p
