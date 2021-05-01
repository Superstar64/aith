module Core.Ast.Term where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.KindPattern
import Core.Ast.Pattern
import Core.Ast.RuntimePattern
import Core.Ast.Type
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import Misc.Prism
import Misc.Silent
import Misc.Symbol
import qualified Misc.Variables as Variables

data TermF d p
  = Variable (d Identity) Identifier
  | MacroAbstraction (d Erased) (Bound (Pattern p p) (Term d p))
  | MacroApplication (d Erased) (Term d p) (Term d p)
  | TypeAbstraction (d Erased) (Bound (TypePattern p p) (Term d p))
  | TypeApplication (d Erased) (Term d p) (Type p)
  | KindAbstraction (d Erased) (Bound (KindPattern p) (Term d p))
  | KindApplication (d Erased) (Term d p) (Kind p)
  | OfCourseIntroduction (d Erased) (Term d p)
  | Bind (d Erased) (Term d p) (Bound (Pattern p p) (Term d p))
  | Alias (Term d p) (Bound (RuntimePattern d p p) (Term d p))
  | Extern (d Identity) (d []) Symbol (Type p) [Type p]
  | FunctionApplication (d Identity) (d []) (Term d p) [Term d p]
  | FunctionLiteral (d Identity) (Bound [RuntimePattern d p p] (Term d p))
  | ErasedQualifiedAssume (d Erased) (Type p) (Term d p)
  | ErasedQualifiedCheck (d Erased) (Term d p)
  | RuntimePairIntroduction (d Identity) (Term d p) (Term d p)
  | Pack (d Erased) (Bound (TypePattern p p) (Type p)) (Term d p)
  | Unpack (d Erased) (Term d p)

deriving instance (Show p, Show (d Identity), Show (d []), Show (d Erased)) => Show (TermF d p)

traverseTerm term typex kind bound runtimeBound runtimeBoundMany typeBound kindBound typeBoundType = go
  where
    go (Variable dx x) = pure Variable <*> pure dx <*> pure x
    go (MacroAbstraction i λ) = pure MacroAbstraction <*> pure i <*> bound λ
    go (MacroApplication i e1 e2) = pure MacroApplication <*> pure i <*> term e1 <*> term e2
    go (TypeAbstraction i λ) = pure TypeAbstraction <*> pure i <*> typeBound λ
    go (TypeApplication i e σ) = pure TypeApplication <*> pure i <*> term e <*> typex σ
    go (KindAbstraction i λ) = pure KindAbstraction <*> pure i <*> kindBound λ
    go (KindApplication i e κ) = pure KindApplication <*> pure i <*> term e <*> kind κ
    go (OfCourseIntroduction i e) = pure OfCourseIntroduction <*> pure i <*> term e
    go (Bind i e λ) = pure Bind <*> pure i <*> term e <*> bound λ
    go (Alias e λ) = pure Alias <*> term e <*> runtimeBound λ
    go (Extern dσ dτs sm σ τs) = pure Extern <*> pure dσ <*> pure dτs <*> pure sm <*> typex σ <*> traverse typex τs
    go (FunctionApplication de1 de2s e1 e2s) = pure FunctionApplication <*> pure de1 <*> pure de2s <*> term e1 <*> traverse term e2s
    go (FunctionLiteral dσ λ) = pure FunctionLiteral <*> pure dσ <*> runtimeBoundMany λ
    go (ErasedQualifiedAssume i π e) = pure ErasedQualifiedAssume <*> pure i <*> typex π <*> term e
    go (ErasedQualifiedCheck i e) = pure ErasedQualifiedCheck <*> pure i <*> term e
    go (RuntimePairIntroduction dσ e e') = pure RuntimePairIntroduction <*> pure dσ <*> term e <*> term e'
    go (Pack i λ e) = pure Pack <*> pure i <*> typeBoundType λ <*> term e
    go (Unpack i e) = pure Unpack <*> pure i <*> term e

foldTerm term typex kind bound runtimeBound runtimeBoundMany typeBound kindBound typeBoundType e = getConst $ traverseTerm (Const . term) (Const . typex) (Const . kind) (Const . bound) (Const . runtimeBound) (Const . runtimeBoundMany) (Const . typeBound) (Const . kindBound) (Const . typeBoundType) e

mapTerm term typex kind bound runtimeBound runtimeBoundMany typeBound kindBound typeBoundType e = runIdentity $ traverseTerm (Identity . term) (Identity . typex) (Identity . kind) (Identity . bound) (Identity . runtimeBound) (Identity . runtimeBoundMany) (Identity . typeBound) (Identity . kindBound) (Identity . typeBoundType) e

variable = Prism (Variable Silent) $ \case
  (Variable _ x) -> Just x
  _ -> Nothing

macroAbstraction = Prism (MacroAbstraction Silent) $ \case
  (MacroAbstraction _ λ) -> Just λ
  _ -> Nothing

macroApplication = Prism (uncurry $ MacroApplication Silent) $ \case
  (MacroApplication _ e e') -> Just (e, e')
  _ -> Nothing

typeAbstraction = Prism (TypeAbstraction Silent) $ \case
  (TypeAbstraction _ λ) -> Just λ
  _ -> Nothing

typeApplication = Prism (uncurry $ TypeApplication Silent) $ \case
  (TypeApplication _ e σ) -> Just (e, σ)
  _ -> Nothing

kindAbstraction = Prism (KindAbstraction Silent) $ \case
  (KindAbstraction _ λ) -> Just λ
  _ -> Nothing

kindApplication = Prism (uncurry $ KindApplication Silent) $ \case
  (KindApplication _ e κ) -> Just (e, κ)
  _ -> Nothing

ofCourseIntroduction = Prism (OfCourseIntroduction Silent) $ \case
  (OfCourseIntroduction _ e) -> Just e
  _ -> Nothing

bind = Prism (uncurry $ Bind Silent) $ \case
  (Bind _ e λ) -> Just (e, λ)
  _ -> Nothing

alias = Prism (uncurry $ Alias) $ \case
  (Alias e λ) -> Just (e, λ)
  _ -> Nothing

extern = Prism (uncurry $ uncurry $ Extern Silent Silent) $ \case
  (Extern _ _ path σ τs) -> Just ((path, σ), τs)
  _ -> Nothing

functionApplication = Prism (uncurry $ FunctionApplication Silent Silent) $ \case
  (FunctionApplication _ _ e e's) -> Just (e, e's)
  _ -> Nothing

functionLiteral = Prism (FunctionLiteral Silent) $ \case
  (FunctionLiteral _ λ) -> Just λ
  _ -> Nothing

erasedQualifiedAssume = Prism (uncurry $ ErasedQualifiedAssume Silent) $ \case
  (ErasedQualifiedAssume _ π e) -> Just (π, e)
  _ -> Nothing

erasedQualifiedCheck = Prism (ErasedQualifiedCheck Silent) $ \case
  (ErasedQualifiedCheck _ e) -> Just e
  _ -> Nothing

runtimePairIntrouction = Prism (uncurry $ RuntimePairIntroduction Silent) $ \case
  (RuntimePairIntroduction _ e1 e2) -> Just (e1, e2)
  _ -> Nothing

pack = Prism (uncurry $ Pack Silent) $ \case
  (Pack _ λ e) -> Just (λ, e)
  _ -> Nothing

unpack = Prism (Unpack Silent) $ \case
  (Unpack _ e) -> Just e
  _ -> Nothing

instance Functor (TermF d) where
  fmap f e = mapTerm term typex kind bound runtimeBound runtimeBoundMany typeBound kindBound typeBound e
    where
      term = fmap f
      typex = fmap f
      kind = fmap f
      bound = bimap (bimap f f) (fmap f)
      runtimeBound = bimap (bimap f f) (fmap f)
      runtimeBoundMany = bimap (fmap (bimap f f)) (fmap f)
      typeBound = bimap (bimap f f) (fmap f)
      kindBound = bimap (fmap f) (fmap f)

data Term d p = CoreTerm p (TermF d p) deriving (Functor)

deriving instance (Show p, Show (d Identity), Show (d []), Show (d Erased)) => Show (Term d p)

coreTerm = Isomorph (uncurry CoreTerm) $ \(CoreTerm p e) -> (p, e)

avoidCaptureTerm ::
  forall d p pm e u.
  (Algebra (Term d p) p u, Algebra (Term d p) p e, Binder p pm) =>
  u ->
  Bound pm e ->
  Bound pm e
avoidCaptureTerm = avoidCapture @(Term d p)

avoidCaptureTermConvert ::
  forall d p pm e.
  (Binder p pm, Algebra (Term d p) p e) =>
  Identifier ->
  Bound pm e ->
  Bound pm e
avoidCaptureTermConvert = avoidCaptureGeneral internalVariable (convert @(Term d p))

instance Semigroup p => Algebra (Term d p) p (Term d p) where
  freeVariables (CoreTerm p (Variable _ x)) = Variables.singleton x p
  freeVariables (CoreTerm _ e) = foldTerm go go go go go go go go go e
    where
      go = freeVariables @(Term d p)
  convert ix x (CoreTerm p (Variable d x')) | x == x' = CoreTerm p $ Variable d ix
  convert ix x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go go e
    where
      go = convert @(Term d p) ix x
  substitute ux x (CoreTerm _ (Variable _ x')) | x == x' = ux
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go go e
    where
      go = substitute ux x

instance Semigroup p => Algebra (Type p) p (Term d p) where
  freeVariables (CoreTerm _ e) = foldTerm go go go go go go go go go e
    where
      go = freeVariables @(Type p)
  convert ix x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go go e
    where
      go = convert @(Type p) ix x
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go go e
    where
      go = substitute ux x

instance Semigroup p => Algebra (Kind p) p (Term d p) where
  freeVariables (CoreTerm _ e) = foldTerm go go go go go go go go go e
    where
      go = freeVariables @(Kind p)
  convert ix x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go go e
    where
      go = convert @(Kind p) ix x
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go go e
    where
      go = substitute ux x

instance Semigroup p => Algebra (Term d p) p (Type p) where
  freeVariables _ = mempty
  convert _ _ = id
  substitute _ _ = id

instance Semigroup p => Algebra (Term d p) p (Kind p) where
  freeVariables _ = mempty
  convert _ _ = id
  substitute _ _ = id

instance Algebra (Term d p) p u => Algebra (Term d p) p (Bound (Pattern p p) u) where
  freeVariables (Bound pm e) = removeBinds (freeVariables @(Term d p) e) (bindings pm)
  convert = substituteSame (convert @(Term d p)) (avoidCaptureTermConvert @d @p)
  substitute = substituteSame substitute (avoidCaptureTerm @d)

instance Algebra (Term d p) p (e p) => AlgebraBound (Term d p) p e (Pattern p p)

instance Algebra (Term d p) p u => Algebra (Term d p) p (Bound (RuntimePattern d p p) u) where
  freeVariables (Bound pm e) = removeBinds (freeVariables @(Term d p) e) (bindings pm)
  convert = substituteSame (convert @(Term d p)) (avoidCaptureTermConvert @d @p)
  substitute = substituteSame substitute (avoidCaptureTerm @d)

instance Algebra (Term d p) p (e p) => AlgebraBound (Term d p) p e (RuntimePattern d p p)

instance (Algebra (Type p) p u, Algebra (Term d p) p u) => Algebra (Term d p) p (Bound (TypePattern p p) u) where
  freeVariables (Bound _ e) = freeVariables @(Term d p) e
  convert = substituteLower (convert @(Term d p)) (flip const)
  substitute = substituteLower substitute avoidCaptureType

instance (Algebra (Term d p) p u, Algebra (Kind p) p u) => Algebra (Term d p) p (Bound (KindPattern p) u) where
  freeVariables (Bound _ e) = freeVariables @(Term d p) e
  convert = substituteLower (convert @(Term d p)) (flip const)
  substitute = substituteLower substitute avoidCaptureKind

reduceTermImpl (Bind _ e λ) = let CoreTerm _ e' = apply λ (reduce e) in e'
reduceTermImpl (MacroApplication _ e1 e2) | (CoreTerm _ (MacroAbstraction _ λ)) <- reduce e1 = let CoreTerm _ e' = apply λ (reduce e2) in e'
reduceTermImpl (TypeApplication _ e σ) | (CoreTerm _ (TypeAbstraction _ λ)) <- reduce e = let CoreTerm _ e' = apply λ (reduce σ) in e'
reduceTermImpl (KindApplication _ e κ) | (CoreTerm _ (KindAbstraction _ λ)) <- reduce e = let CoreTerm _ e' = apply λ (reduce κ) in e'
reduceTermImpl (ErasedQualifiedCheck _ e) | (CoreTerm _ (ErasedQualifiedAssume _ _ e')) <- reduce e = let CoreTerm _ e'' = e' in e''
reduceTermImpl e = mapTerm go go go go go go go go go e
  where
    go = reduce

instance Semigroup p => Reduce (Term Silent p) where
  reduce (CoreTerm p e) = CoreTerm p (reduceTermImpl e)

instance Semigroup p => Apply (Bound (Pattern p p) (Term Silent p)) (Term Silent p) (Term Silent p) where
  apply (Bound (CorePattern _ (PatternVariable x _)) e) ux = reduce $ substitute ux x e
  apply (Bound (CorePattern _ (PatternOfCourse pm)) e) (CoreTerm _ (OfCourseIntroduction _ ux)) = apply (Bound pm e) ux
  -- todo find better position here
  apply λ ux@(CoreTerm p _) = CoreTerm p $ Bind Silent ux λ

instance Semigroup p => Apply (Bound (TypePattern p p) (Term Silent p)) (Type p) (Term Silent p) where
  apply (Bound (CoreTypePattern _ (TypePatternVariable x _)) e) ux = reduce $ substitute ux x e

instance Semigroup p => Apply (Bound (KindPattern p) (Term Silent p)) (Kind p) (Term Silent p) where
  apply (Bound (CoreKindPattern _ (KindPatternVariable x _)) e) ux = reduce $ substitute ux x e

instance Location (Term d) where
  location (CoreTerm p _) = p
