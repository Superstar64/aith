module Core.Ast.Term where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.KindPattern
import Core.Ast.Pattern
import Core.Ast.Type
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import Misc.Prism
import Misc.Symbol
import Misc.Variables (Variables)
import qualified Misc.Variables as Variables

data TermF p
  = Variable Identifier
  | MacroAbstraction (Bound (Pattern p p) (Term p))
  | MacroApplication (Term p) (Term p)
  | TypeAbstraction (Bound (TypePattern p p) (Term p))
  | TypeApplication (Term p) (Type p)
  | KindAbstraction (Bound (KindPattern p) (Term p))
  | KindApplication (Term p) (Kind p)
  | OfCourseIntroduction (Term p)
  | Bind (Term p) (Bound (Pattern p p) (Term p))
  | Extern Symbol (Type p)
  | FunctionApplication (Term p) [Term p]
  deriving (Show)

variable = Prism Variable $ \case
  (Variable x) -> Just x
  _ -> Nothing

macroAbstraction = Prism MacroAbstraction $ \case
  (MacroAbstraction λ) -> Just λ
  _ -> Nothing

macroApplication = Prism (uncurry MacroApplication) $ \case
  (MacroApplication e e') -> Just (e, e')
  _ -> Nothing

typeAbstraction = Prism TypeAbstraction $ \case
  (TypeAbstraction λ) -> Just λ
  _ -> Nothing

typeApplication = Prism (uncurry TypeApplication) $ \case
  (TypeApplication e σ) -> Just (e, σ)
  _ -> Nothing

kindAbstraction = Prism KindAbstraction $ \case
  (KindAbstraction λ) -> Just λ
  _ -> Nothing

kindApplication = Prism (uncurry KindApplication) $ \case
  (KindApplication e κ) -> Just (e, κ)
  _ -> Nothing

ofCourseIntroduction = Prism OfCourseIntroduction $ \case
  (OfCourseIntroduction e) -> Just e
  _ -> Nothing

bind = Prism (uncurry $ Bind) $ \case
  (Bind e λ) -> Just (e, λ)
  _ -> Nothing

extern = Prism (uncurry Extern) $ \case
  (Extern path σ) -> Just (path, σ)
  _ -> Nothing

functionApplication = Prism (uncurry FunctionApplication) $ \case
  (FunctionApplication e e's) -> Just (e, e's)
  _ -> Nothing

instance Functor TermF where
  fmap _ (Variable x) = Variable x
  fmap f (MacroAbstraction (Bound pm e)) = MacroAbstraction $ Bound (bimap f f pm) (fmap f e)
  fmap f (MacroApplication e1 e2) = MacroApplication (fmap f e1) (fmap f e2)
  fmap f (TypeAbstraction (Bound pm e)) = TypeAbstraction $ Bound (bimap f f pm) (fmap f e)
  fmap f (TypeApplication e σ) = TypeApplication (fmap f e) (fmap f σ)
  fmap f (KindAbstraction (Bound pm e)) = KindAbstraction $ Bound (fmap f pm) (fmap f e)
  fmap f (KindApplication e s) = KindApplication (fmap f e) (fmap f s)
  fmap f (OfCourseIntroduction e) = OfCourseIntroduction (fmap f e)
  fmap f (Bind e1 (Bound pm e2)) = Bind (fmap f e1) $ Bound (bimap f f pm) (fmap f e2)
  fmap f (Extern sm σ) = Extern sm (fmap f σ)
  fmap f (FunctionApplication e e's) = FunctionApplication (fmap f e) (fmap f <$> e's)

data Term p = CoreTerm p (TermF p) deriving (Show, Functor)

coreTerm = Isomorph (uncurry CoreTerm) $ \(CoreTerm p e) -> (p, e)

type TermInternal = Term Internal

freeVariablesTermImpl ::
  forall u p.
  ( Semigroup p,
    FreeVariables u p (Term p),
    FreeVariables u p (Type p),
    FreeVariables u p (Kind p),
    FreeVariables u p (Bound (Pattern p p) (Term p)),
    FreeVariables u p (Bound (TypePattern p p) (Term p)),
    FreeVariables u p (Bound (KindPattern p) (Term p))
  ) =>
  TermF p ->
  Variables p
freeVariablesTermImpl (Variable _) = mempty
freeVariablesTermImpl (MacroAbstraction λ) = freeVariables @u λ
freeVariablesTermImpl (MacroApplication e1 e2) = freeVariables @u e1 <> freeVariables @u e2
freeVariablesTermImpl (TypeAbstraction λ) = freeVariables @u λ
freeVariablesTermImpl (TypeApplication e σ) = freeVariables @u e <> freeVariables @u σ
freeVariablesTermImpl (KindAbstraction λ) = freeVariables @u λ
freeVariablesTermImpl (KindApplication e κ) = freeVariables @u e <> freeVariables @u κ
freeVariablesTermImpl (OfCourseIntroduction e) = freeVariables @u e
freeVariablesTermImpl (Bind e λ) = freeVariables @u e <> freeVariables @u λ
freeVariablesTermImpl (Extern _ σ) = freeVariables @u σ
freeVariablesTermImpl (FunctionApplication e1 e2s) = freeVariables @u e1 <> freeVariables @u e2s

instance Semigroup p => FreeVariables (Term p) p (Term p) where
  freeVariables (CoreTerm p (Variable x)) = Variables.singleton x p
  freeVariables (CoreTerm _ e) = freeVariablesTermImpl @(Term p) e

instance Semigroup p => FreeVariables (Term p) p (Bound (Pattern p p) (Term p)) where
  freeVariables (Bound pm e) = removeBinds (freeVariables @(Term p) e) (bindings @p pm)

instance Semigroup p => FreeVariables (Term p) p (Bound (TypePattern p p) (Term p)) where
  freeVariables (Bound _ e) = freeVariables @(Term p) e

instance Semigroup p => FreeVariables (Term p) p (Bound (KindPattern p) (Term p)) where
  freeVariables (Bound _ e) = freeVariables @(Term p) e

instance Semigroup p => FreeVariables (Term p) p (Type p) where
  freeVariables _ = mempty

instance Semigroup p => FreeVariables (Term p) p (Kind p) where
  freeVariables _ = mempty

instance Semigroup p => FreeVariables (Type p) p (Term p) where
  freeVariables (CoreTerm _ e) = freeVariablesTermImpl @(Type p) e

instance Semigroup p => FreeVariables (Type p) p (Bound (Pattern p p) (Term p)) where
  freeVariables (Bound pm e) = freeVariables @(Type p) pm <> freeVariables @(Type p) e

instance Semigroup p => FreeVariables (Type p) p (Bound (TypePattern p p) (Term p)) where
  freeVariables (Bound pm e) = removeBinds (freeVariables @(Type p) e) (bindings @p pm)

instance Semigroup p => FreeVariables (Type p) p (Bound (KindPattern p) (Term p)) where
  freeVariables (Bound _ e) = freeVariables @(Type p) e

instance Semigroup p => FreeVariables (Kind p) p (Term p) where
  freeVariables (CoreTerm _ e) = freeVariablesTermImpl @(Kind p) e

instance Semigroup p => FreeVariables (Kind p) p (Bound (Pattern p p) (Term p)) where
  freeVariables (Bound pm e) = freeVariables @(Kind p) pm <> freeVariables @(Kind p) e

instance Semigroup p => FreeVariables (Kind p) p (Bound (TypePattern p p) (Term p)) where
  freeVariables (Bound pm e) = freeVariables @(Kind p) pm <> freeVariables @(Kind p) e

instance Semigroup p => FreeVariables (Kind p) p (Bound (KindPattern p) (Term p)) where
  freeVariables (Bound pm e) = removeBinds (freeVariables @(Kind p) e) (bindings @p pm)

avoidCaptureTerm = avoidCapture (CoreTerm Internal . Variable) (freeVariablesInternal @TermInternal)

substituteTermImpl _ _ (Variable x) = Variable x
substituteTermImpl ux x (MacroAbstraction λ) = MacroAbstraction (substitute ux x λ)
substituteTermImpl ux x (MacroApplication e1 e2) = MacroApplication (substitute ux x e1) (substitute ux x e2)
substituteTermImpl ux x (TypeAbstraction λ) = TypeAbstraction (substitute ux x λ)
substituteTermImpl ux x (TypeApplication e σ) = TypeApplication (substitute ux x e) (substitute ux x σ)
substituteTermImpl ux x (KindAbstraction λ) = KindAbstraction (substitute ux x λ)
substituteTermImpl ux x (KindApplication e κ) = KindApplication (substitute ux x e) (substitute ux x κ)
substituteTermImpl ux x (OfCourseIntroduction e) = OfCourseIntroduction (substitute ux x e)
substituteTermImpl ux x (Bind e λ) = Bind (substitute ux x e) (substitute ux x λ)
substituteTermImpl ux x (Extern sm σ) = Extern sm (substitute ux x σ)
substituteTermImpl ux x (FunctionApplication e1 e2s) = FunctionApplication (substitute ux x e1) (substitute ux x e2s)

instance Substitute TermInternal TermInternal where
  substitute ux x (CoreTerm Internal (Variable x')) | x == x' = ux
  substitute ux x (CoreTerm Internal e) = CoreTerm Internal $ substituteTermImpl ux x e

instance Substitute TermInternal (Bound PatternInternal TermInternal) where
  substitute _ x λ@(Bound pm _) | x `Variables.member` bindingsInternal pm = λ
  substitute ux x λ = Bound pm (substitute ux x e)
    where
      Bound pm e = avoidCaptureTerm ux λ

instance Substitute TermInternal (Bound TypePatternInternal TermInternal) where
  substitute ux x λ = Bound pm (substitute ux x e)
    where
      Bound pm e = avoidCaptureType ux λ

instance Substitute TermInternal (Bound KindPatternInternal TermInternal) where
  substitute ux x λ = Bound pm (substitute ux x e)
    where
      Bound pm e = avoidCaptureKind ux λ

instance Substitute TypeInternal TermInternal where
  substitute ux x (CoreTerm Internal e) = CoreTerm Internal (substituteTermImpl ux x e)

instance Substitute TypeInternal (Bound PatternInternal TermInternal) where
  substitute ux x (Bound pm σ) = Bound (substitute ux x pm) (substitute ux x σ)

instance Substitute TypeInternal (Bound TypePatternInternal TermInternal) where
  substitute _ x λ@(Bound pm _) | x `Variables.member` bindingsInternal pm = λ
  substitute ux x λ = Bound pm (substitute ux x e)
    where
      Bound pm e = avoidCaptureType ux λ

instance Substitute TypeInternal (Bound KindPatternInternal TermInternal) where
  substitute ux x λ = Bound pm (substitute ux x e)
    where
      Bound pm e = avoidCaptureKind ux λ

instance Substitute KindInternal TermInternal where
  substitute ux x (CoreTerm Internal e) = CoreTerm Internal (substituteTermImpl ux x e)

instance Substitute KindInternal (Bound PatternInternal TermInternal) where
  substitute ux x (Bound pm e) = Bound (substitute ux x pm) (substitute ux x e)

instance Substitute KindInternal (Bound TypePatternInternal TermInternal) where
  substitute ux x (Bound pm e) = Bound (substitute ux x pm) (substitute ux x e)

instance Substitute KindInternal (Bound KindPatternInternal TermInternal) where
  substitute _ x λ@(Bound pm _) | x `Variables.member` bindingsInternal pm = λ
  substitute ux x λ = Bound pm (substitute ux x e)
    where
      Bound pm e = avoidCaptureKind ux λ

instance Substitute TermInternal TypeInternal where
  substitute _ _ = id

instance Substitute TermInternal KindInternal where
  substitute _ _ = id

reduceTermImpl (Variable x) = Variable x
reduceTermImpl (MacroAbstraction λ) = MacroAbstraction (reduce λ)
reduceTermImpl (MacroApplication e1 e2) | (CoreTerm Internal (MacroAbstraction λ)) <- reduce e1 = let CoreTerm Internal e' = apply λ (reduce e2) in e'
reduceTermImpl (MacroApplication e1 e2) = MacroApplication (reduce e1) (reduce e2)
reduceTermImpl (TypeAbstraction λ) = TypeAbstraction (reduce λ)
reduceTermImpl (TypeApplication e σ) | (CoreTerm Internal (TypeAbstraction λ)) <- reduce e = let CoreTerm Internal e' = apply λ (reduce σ) in e'
reduceTermImpl (TypeApplication e σ) = TypeApplication (reduce e) (reduce σ)
reduceTermImpl (KindAbstraction λ) = KindAbstraction (reduce λ)
reduceTermImpl (KindApplication e κ) | (CoreTerm Internal (KindAbstraction λ)) <- reduce e = let CoreTerm Internal e' = apply λ (reduce κ) in e'
reduceTermImpl (KindApplication e κ) = KindApplication (reduce e) (reduce κ)
reduceTermImpl (OfCourseIntroduction e) = OfCourseIntroduction (reduce e)
reduceTermImpl (Bind e λ) = let CoreTerm Internal e' = apply λ (reduce e) in e'
reduceTermImpl (Extern sm σ) = Extern sm (reduce σ)
reduceTermImpl (FunctionApplication e1 e2s) = FunctionApplication (reduce e1) (reduce e2s)

instance Reduce TermInternal where
  reduce (CoreTerm Internal e) = CoreTerm Internal (reduceTermImpl e)

instance Apply (Bound PatternInternal TermInternal) TermInternal TermInternal where
  apply (Bound (CorePattern Internal (PatternVariable x _)) e) ux = reduce $ substitute ux x e
  apply (Bound (CorePattern Internal (PatternOfCourse pm)) e) (CoreTerm Internal (OfCourseIntroduction ux)) = apply (Bound pm e) ux
  apply λ ux = CoreTerm Internal $ Bind ux λ

instance Apply (Bound TypePatternInternal TermInternal) TypeInternal TermInternal where
  apply (Bound (CoreTypePattern Internal (TypePatternVariable x _)) e) ux = reduce $ substitute ux x e

instance Apply (Bound KindPatternInternal TermInternal) KindInternal TermInternal where
  apply (Bound (CoreKindPattern Internal (KindPatternVariable x _)) e) ux = reduce $ substitute ux x e

instance Location Term where
  location (CoreTerm p _) = p
