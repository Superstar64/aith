module Core.Ast.Term where

import Control.Category (id, (.))
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
import Misc.Symbol
import qualified Misc.Variables as Variables
import Prelude hiding (id, (.))

data TermCommon d σ pm e
  = Variable Identifier
  | Alias e (Bound pm e)
  | Extern d d Symbol σ σ
  | FunctionApplication d d e e
  | RuntimePairIntroduction d e e
  | FunctionLiteral d (Bound pm e)
  deriving (Show)

data TermF p
  = TermCommon (TermCommon () (Type p) (RuntimePattern p p) (Term p))
  | MacroAbstraction (Bound (Pattern p p) (Term p))
  | MacroApplication (Term p) (Term p)
  | TypeAbstraction (Bound (TypePattern p p) (Term p))
  | TypeApplication (Term p) (Type p)
  | KindAbstraction (Bound (KindPattern p) (Term p))
  | KindApplication (Term p) (Kind p)
  | OfCourseIntroduction (Term p)
  | Bind (Term p) (Bound (Pattern p p) (Term p))
  | ErasedQualifiedAssume (Type p) (Term p)
  | ErasedQualifiedCheck (Term p)
  | Pack (Bound (TypePattern p p) (Type p)) (Term p)
  | Unpack (Term p)
  deriving (Show)

traverseTerm term typex kind bound runtimeBound typeBound kindBound typeBoundType = go
  where
    go (TermCommon (Variable x)) = TermCommon <$> (pure Variable <*> pure x)
    go (MacroAbstraction λ) = pure MacroAbstraction <*> bound λ
    go (MacroApplication e1 e2) = pure MacroApplication <*> term e1 <*> term e2
    go (TypeAbstraction λ) = pure TypeAbstraction <*> typeBound λ
    go (TypeApplication e σ) = pure TypeApplication <*> term e <*> typex σ
    go (KindAbstraction λ) = pure KindAbstraction <*> kindBound λ
    go (KindApplication e κ) = pure KindApplication <*> term e <*> kind κ
    go (OfCourseIntroduction e) = pure OfCourseIntroduction <*> term e
    go (Bind e λ) = pure Bind <*> term e <*> bound λ
    go (TermCommon (Alias e λ)) = TermCommon <$> (pure Alias <*> term e <*> runtimeBound λ)
    go (TermCommon (Extern dσ dτs sm σ τs)) = TermCommon <$> (pure Extern <*> pure dσ <*> pure dτs <*> pure sm <*> typex σ <*> typex τs)
    go (TermCommon (FunctionApplication de1 de2s e1 e2s)) = TermCommon <$> (pure FunctionApplication <*> pure de1 <*> pure de2s <*> term e1 <*> term e2s)
    go (TermCommon (FunctionLiteral dσ λ)) = TermCommon <$> (pure FunctionLiteral <*> pure dσ <*> runtimeBound λ)
    go (ErasedQualifiedAssume π e) = pure ErasedQualifiedAssume <*> typex π <*> term e
    go (ErasedQualifiedCheck e) = pure ErasedQualifiedCheck <*> term e
    go (TermCommon (RuntimePairIntroduction dσ e e')) = TermCommon <$> (pure RuntimePairIntroduction <*> pure dσ <*> term e <*> term e')
    go (Pack λ e) = pure Pack <*> typeBoundType λ <*> term e
    go (Unpack e) = pure Unpack <*> term e

foldTerm term typex kind bound runtimeBound typeBound kindBound typeBoundType e = getConst $ traverseTerm (Const . term) (Const . typex) (Const . kind) (Const . bound) (Const . runtimeBound) (Const . typeBound) (Const . kindBound) (Const . typeBoundType) e

mapTerm term typex kind bound runtimeBound typeBound kindBound typeBoundType e = runIdentity $ traverseTerm (Identity . term) (Identity . typex) (Identity . kind) (Identity . bound) (Identity . runtimeBound) (Identity . typeBound) (Identity . kindBound) (Identity . typeBoundType) e

termCommon = Prism TermCommon $ \case
  (TermCommon e) -> Just e
  _ -> Nothing

variable = (termCommon .) $
  Prism (Variable) $ \case
    (Variable x) -> Just x
    _ -> Nothing

macroAbstraction = Prism (MacroAbstraction) $ \case
  (MacroAbstraction λ) -> Just λ
  _ -> Nothing

macroApplication = Prism (uncurry $ MacroApplication) $ \case
  (MacroApplication e e') -> Just (e, e')
  _ -> Nothing

typeAbstraction = Prism (TypeAbstraction) $ \case
  (TypeAbstraction λ) -> Just λ
  _ -> Nothing

typeApplication = Prism (uncurry $ TypeApplication) $ \case
  (TypeApplication e σ) -> Just (e, σ)
  _ -> Nothing

kindAbstraction = Prism (KindAbstraction) $ \case
  (KindAbstraction λ) -> Just λ
  _ -> Nothing

kindApplication = Prism (uncurry $ KindApplication) $ \case
  (KindApplication e κ) -> Just (e, κ)
  _ -> Nothing

ofCourseIntroduction = Prism (OfCourseIntroduction) $ \case
  (OfCourseIntroduction e) -> Just e
  _ -> Nothing

bind = Prism (uncurry $ Bind) $ \case
  (Bind e λ) -> Just (e, λ)
  _ -> Nothing

alias = (termCommon .) $
  Prism (uncurry $ Alias) $ \case
    (Alias e λ) -> Just (e, λ)
    _ -> Nothing

extern = (termCommon .) $
  Prism (uncurry $ uncurry $ Extern () ()) $ \case
    (Extern () () path σ τs) -> Just ((path, σ), τs)
    _ -> Nothing

functionApplication = (termCommon .) $
  Prism (uncurry $ FunctionApplication () ()) $ \case
    (FunctionApplication () () e e's) -> Just (e, e's)
    _ -> Nothing

functionLiteral = (termCommon .) $
  Prism (FunctionLiteral ()) $ \case
    (FunctionLiteral () λ) -> Just λ
    _ -> Nothing

erasedQualifiedAssume = Prism (uncurry $ ErasedQualifiedAssume) $ \case
  (ErasedQualifiedAssume π e) -> Just (π, e)
  _ -> Nothing

erasedQualifiedCheck = Prism (ErasedQualifiedCheck) $ \case
  (ErasedQualifiedCheck e) -> Just e
  _ -> Nothing

runtimePairIntrouction = (termCommon .) $
  Prism (uncurry $ RuntimePairIntroduction ()) $ \case
    (RuntimePairIntroduction () e1 e2) -> Just (e1, e2)
    _ -> Nothing

pack = Prism (uncurry $ Pack) $ \case
  (Pack λ e) -> Just (λ, e)
  _ -> Nothing

unpack = Prism (Unpack) $ \case
  (Unpack e) -> Just e
  _ -> Nothing

instance Functor TermF where
  fmap f e = mapTerm term typex kind bound runtimeBound typeBound kindBound typeBound e
    where
      term = fmap f
      typex = fmap f
      kind = fmap f
      bound = bimap (bimap f f) (fmap f)
      runtimeBound = bimap (bimap f f) (fmap f)
      typeBound = bimap (bimap f f) (fmap f)
      kindBound = bimap (fmap f) (fmap f)

data Term p = CoreTerm p (TermF p) deriving (Functor, Show)

coreTerm = Isomorph (uncurry CoreTerm) $ \(CoreTerm p e) -> (p, e)

avoidCaptureTerm ::
  forall p pm e u.
  (Algebra (Term p) p u, Algebra (Term p) p e, Binder p pm) =>
  u ->
  Bound pm e ->
  Bound pm e
avoidCaptureTerm = avoidCapture @(Term p)

avoidCaptureTermConvert ::
  forall p pm e.
  (Binder p pm, Algebra (Term p) p e) =>
  Identifier ->
  Bound pm e ->
  Bound pm e
avoidCaptureTermConvert = avoidCaptureGeneral internalVariable (convert @(Term p))

instance Semigroup p => Algebra (Term p) p (Term p) where
  freeVariables (CoreTerm p (TermCommon (Variable x))) = Variables.singleton x p
  freeVariables (CoreTerm _ e) = foldTerm go go go go go go go go e
    where
      go = freeVariables @(Term p)
  convert ix x (CoreTerm p (TermCommon (Variable x'))) | x == x' = CoreTerm p $ TermCommon $ Variable ix
  convert ix x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go e
    where
      go = convert @(Term p) ix x
  substitute ux x (CoreTerm _ (TermCommon (Variable x'))) | x == x' = ux
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go e
    where
      go = substitute ux x

instance Semigroup p => Algebra (Type p) p (Term p) where
  freeVariables (CoreTerm _ e) = foldTerm go go go go go go go go e
    where
      go = freeVariables @(Type p)
  convert ix x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go e
    where
      go = convert @(Type p) ix x
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go e
    where
      go = substitute ux x

instance Semigroup p => Algebra (Kind p) p (Term p) where
  freeVariables (CoreTerm _ e) = foldTerm go go go go go go go go e
    where
      go = freeVariables @(Kind p)
  convert ix x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go e
    where
      go = convert @(Kind p) ix x
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTerm go go go go go go go go e
    where
      go = substitute ux x

instance Semigroup p => Algebra (Term p) p (Type p) where
  freeVariables _ = mempty
  convert _ _ = id
  substitute _ _ = id

instance Semigroup p => Algebra (Term p) p (Kind p) where
  freeVariables _ = mempty
  convert _ _ = id
  substitute _ _ = id

instance Algebra (Term p) p u => Algebra (Term p) p (Bound (Pattern p p) u) where
  freeVariables (Bound pm e) = removeBinds (freeVariables @(Term p) e) (bindings pm)
  convert = substituteSame (convert @(Term p)) (avoidCaptureTermConvert @p)
  substitute = substituteSame substitute avoidCaptureTerm

instance Algebra (Term p) p u => Algebra (Term p) p (Bound (RuntimePattern p p) u) where
  freeVariables (Bound pm e) = removeBinds (freeVariables @(Term p) e) (bindings pm)
  convert = substituteSame (convert @(Term p)) (avoidCaptureTermConvert @p)
  substitute = substituteSame substitute avoidCaptureTerm

instance (Algebra (Type p) p u, Algebra (Term p) p u) => Algebra (Term p) p (Bound (TypePattern p p) u) where
  freeVariables (Bound _ e) = freeVariables @(Term p) e
  convert = substituteLower (convert @(Term p)) (flip const)
  substitute = substituteLower substitute avoidCaptureType

instance (Algebra (Term p) p u, Algebra (Kind p) p u) => Algebra (Term p) p (Bound (KindPattern p) u) where
  freeVariables (Bound _ e) = freeVariables @(Term p) e
  convert = substituteLower (convert @(Term p)) (flip const)
  substitute = substituteLower substitute avoidCaptureKind

reduceTermImpl (Bind e λ) = let CoreTerm _ e' = apply λ (reduce e) in e'
reduceTermImpl (MacroApplication e1 e2) | (CoreTerm _ (MacroAbstraction λ)) <- reduce e1 = let CoreTerm _ e' = apply λ (reduce e2) in e'
reduceTermImpl (TypeApplication e σ) | (CoreTerm _ (TypeAbstraction λ)) <- reduce e = let CoreTerm _ e' = apply λ (reduce σ) in e'
reduceTermImpl (KindApplication e κ) | (CoreTerm _ (KindAbstraction λ)) <- reduce e = let CoreTerm _ e' = apply λ (reduce κ) in e'
reduceTermImpl (ErasedQualifiedCheck e) | (CoreTerm _ (ErasedQualifiedAssume _ e')) <- reduce e = let CoreTerm _ e'' = e' in e''
reduceTermImpl e = mapTerm go go go go go go go go e
  where
    go = reduce

instance Semigroup p => Reduce (Term p) where
  reduce (CoreTerm p e) = CoreTerm p (reduceTermImpl e)

instance Semigroup p => Apply (Bound (Pattern p p) (Term p)) (Term p) (Term p) where
  apply (Bound (CorePattern _ (PatternVariable x _)) e) ux = reduce $ substitute ux x e
  apply (Bound (CorePattern _ (PatternOfCourse pm)) e) (CoreTerm _ (OfCourseIntroduction ux)) = apply (Bound pm e) ux
  -- todo find better position here
  apply λ ux@(CoreTerm p _) = CoreTerm p $ Bind ux λ

instance Semigroup p => Apply (Bound (TypePattern p p) (Term p)) (Type p) (Term p) where
  apply (Bound (CoreTypePattern _ (TypePatternVariable x _)) e) ux = reduce $ substitute ux x e

instance Semigroup p => Apply (Bound (KindPattern p) (Term p)) (Kind p) (Term p) where
  apply (Bound (CoreKindPattern _ (KindPatternVariable x _)) e) ux = reduce $ substitute ux x e

instance Location Term where
  location (CoreTerm p _) = p
