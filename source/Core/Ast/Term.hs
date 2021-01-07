module Core.Ast.Term where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.Pattern
import Core.Ast.Type
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import qualified Data.Set as Set
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same)
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

instance i ~ Internal => TypeSystem.EmbedVariable (Term i) where
  variable x = CoreTerm Internal $ Variable x

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal) => TypeSystem.EmbedAbstraction (Pattern (Type i') i'') (Term i') where
  abstraction pm e = CoreTerm Internal $ MacroAbstraction pm e

instance (i ~ Internal) => TypeSystem.EmbedApplication (Term i) where
  application e1 e2 = CoreTerm Internal $ MacroApplication e1 e2

instance (i ~ Internal, i' ~ Internal, κ ~ KindInternal) => TypeSystem.EmbedTypeAbstraction (TypePattern κ i) (Term i') where
  typeAbstraction pm e = CoreTerm Internal $ TypeAbstraction pm e

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedTypeApplication (Type i) (Term i') where
  typeApplication e σ = CoreTerm Internal $ TypeApplication e σ

instance (i ~ Internal) => TypeSystem.EmbedOfCourseIntroduction (Term i) where
  ofCourseIntroduction e = CoreTerm Internal $ OfCourseIntroduction e

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => TypeSystem.EmbedBind (Pattern σ i) (Term i') where
  bind pm e1 e2 = CoreTerm Internal $ Bind pm e1 e2

instance (i ~ Internal, i' ~ Internal) => Same (Type i) (Term i) where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => Same (Term i) (Term i) where
  same = Just Refl

instance (i ~ Internal, i' ~ Internal) => Same (Term i) (Type i) where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => Same (Multiplicity i) (Term i') where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => Same (Term i) (Multiplicity i') where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Term i) (Term i') where
  freeVariables' (CoreTerm Internal e) = freeVariables @(Term Internal) $ projectTerm e

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Term i) (Type i') where
  freeVariables' (CoreTerm Internal e) = freeVariables @TypeInternal $ projectTerm e

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Term i) (Multiplicity i') where
  freeVariables' (CoreTerm Internal e) = freeVariables @MultiplicityInternal $ projectTerm e

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => FreeVariables (Pattern σ i) (Term i') where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal, κ ~ KindInternal) => FreeVariables (TypePattern κ i) (Term i) where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Type i) (Term i') where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Kind i) (Term i') where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Multiplicity i) (Term i) where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => Substitute (Term i) (Term i') where
  substitute ex x (CoreTerm Internal e) = substituteImpl ex x $ projectTerm e

instance (i ~ Internal, i' ~ Internal) => Substitute (Type i) (Term i') where
  substitute σx x (CoreTerm Internal e) = substituteImpl σx x $ projectTerm e

instance (i ~ Internal, i' ~ Internal) => Substitute (Multiplicity i) (Term i') where
  substitute lx x (CoreTerm Internal e) = substituteImpl lx x $ projectTerm e

instance (i ~ Internal) => SubstituteSame (Term i)

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => Substitute (Term i) (Pattern σ i') where
  substitute _ _ pm = pm

instance (i ~ Internal, i' ~ Internal, κ ~ KindInternal) => Substitute (Term i) (TypePattern κ i') where
  substitute _ _ pm = pm

instance (i ~ Internal, i' ~ Internal) => Substitute (Term i) (Type i) where
  substitute _ _ σ = σ

instance Substitute (Term i) (Kind i) where
  substitute _ _ κ = κ

instance (i ~ Internal, i' ~ Internal) => Substitute (Term i) (Multiplicity i') where
  substitute _ _ l = l

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal, σ ~ TypeInternal) => AvoidCapturePattern (Term i'') (Pattern σ i) (Term i') where
  avoidCapturePattern u (CorePattern Internal pm, e) = avoidCapturePatternImpl u (projectPattern pm, e)

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal, σ ~ TypeInternal) => AvoidCapturePattern (Type i'') (Pattern σ i) (Term i') where
  avoidCapturePattern u (CorePattern Internal pm, e) = avoidCapturePatternImpl u (projectPattern pm, e)

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal, σ ~ TypeInternal) => AvoidCapturePattern (Multiplicity i'') (Pattern σ i) (Term i') where
  avoidCapturePattern u (CorePattern Internal pm, e) = avoidCapturePatternImpl u (projectPattern pm, e)

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal, κ ~ KindInternal) => AvoidCapturePattern (Term i) (TypePattern κ i') (Term i'') where
  avoidCapturePattern u (CoreTypePattern Internal pm, e) = avoidCapturePatternImpl u (projectTypePattern pm, e)

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal, κ ~ KindInternal) => AvoidCapturePattern (Type i) (TypePattern κ i') (Term i'') where
  avoidCapturePattern u (CoreTypePattern Internal pm, e) = avoidCapturePatternImpl u (projectTypePattern pm, e)

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal, κ ~ KindInternal) => AvoidCapturePattern (Multiplicity i) (TypePattern κ i') (Term i'') where
  avoidCapturePattern u (CoreTypePattern Internal pm, e) = avoidCapturePatternImpl u (projectTypePattern pm, e)

instance (i ~ Internal) => Reduce (Term i) where
  reduce (CoreTerm Internal e) = reduceImpl $ projectTerm e

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => ReducePattern (Pattern σ i) (Term i') where
  reducePattern (CorePattern Internal pm) e1 e2 = reducePattern (projectPattern pm) e1 e2

instance (i ~ Internal, i' ~ Internal) => ReduceMatchAbstraction (Term i') (Term i) where
  reduceMatchAbstraction (CoreTerm Internal (MacroAbstraction pm e1)) = Just $ \e2 -> reducePattern pm e2 e1
  reduceMatchAbstraction _ = Nothing

instance (i ~ Internal, i' ~ Internal) => ReduceMatchAbstraction (Type i') (Term i) where
  reduceMatchAbstraction (CoreTerm Internal (TypeAbstraction (CoreTypePattern Internal (TypePatternVariable x _)) e)) = Just $ \σ -> reduce $ substitute σ x e
  reduceMatchAbstraction _ = Nothing

instance (i ~ Internal) => TypeSystem.MatchOfCourseIntroduction (Term i) where
  matchOfCourseIntroduction (CoreTerm Internal (OfCourseIntroduction e)) = Just (TypeSystem.OfCourseIntroduction e)
  matchOfCourseIntroduction _ = Nothing

instance Positioned (Term p) p where
  location (CoreTerm p _) = p
