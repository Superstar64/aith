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
import Data.Functor.Identity (Identity (..), runIdentity)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import Misc.Prism
import Misc.Symbol
import qualified Misc.Variables as Variables
import Prelude hiding (id, (.))

data TermCommon d pmσ σ pm e
  = Variable Identifier
  | Alias e (Bound pm e)
  | Extern d d Symbol σ σ
  | FunctionApplication d d e e
  | RuntimePairIntroduction d e e
  | FunctionLiteral d (Bound pm e)
  | ReadReference d e
  | LocalRegion d (Bound pmσ (σ, (e, Bound pm e)))
  deriving (Show)

data TermF p
  = TermCommon (TermCommon () (TypePattern p p) (Type p) (RuntimePattern p p) (Term p))
  | MacroAbstraction (Bound (Pattern p p) (Term p))
  | MacroApplication (Term p) (Term p)
  | TypeAbstraction (Bound (TypePattern p p) (Term p))
  | TypeApplication (Term p) (Type p)
  | KindAbstraction (Bound (KindPattern p) (Term p))
  | KindApplication (Term p) (Kind p)
  | OfCourseIntroduction (Term p)
  | Bind (Term p) (Bound (Pattern p p) (Term p))
  | QualifiedAssume (Type p) (Term p)
  | QualifiedCheck (Term p)
  | Pack (Bound (TypePattern p p) (Type p)) (Term p)
  | Unpack (Term p)
  | PureRegionTransformer (Type p) (Term p)
  | DoRegionTransformer (Term p) (Bound (RuntimePattern p p) (Term p))
  | CastRegionTransformer (Type p) (Term p)
  deriving (Show)

termf =
  assumeIsomorph $
    variable
      `branch` alias
      `branch` extern
      `branch` functionApplication
      `branch` runtimePairIntrouction
      `branch` functionLiteral
      `branch` readReference
      `branch` localRegion
      `branch` macroAbstraction
      `branch` macroApplication
      `branch` typeAbstraction
      `branch` typeApplication
      `branch` kindAbstraction
      `branch` kindApplication
      `branch` ofCourseIntroduction
      `branch` bind
      `branch` qualifiedAssume
      `branch` qualifiedCheck
      `branch` pack
      `branch` unpack
      `branch` pureRegionTransformer
      `branch` doRegionTransformer
      `branch` castRegionTransformer

instance Functor TermF where
  fmap f e = runIdentity $ traverseTermF term typex kind bound runtimeBound typeBound kindBound typeBound localRegion e
    where
      term = Identity . fmap f
      typex = Identity . fmap f
      kind = Identity . fmap f
      bound = Identity . bimap (bimap f f) (fmap f)
      runtimeBound = Identity . bimap (bimap f f) (fmap f)
      typeBound = Identity . bimap (bimap f f) (fmap f)
      kindBound = Identity . bimap (fmap f) (fmap f)
      localRegion = Identity . bimap (bimap f f) (bimap (fmap f) (bimap (fmap f) (bimap (bimap f f) (fmap f))))
      traverseTermF term typex kind bound runtimeBound typeBound kindBound typeBoundType localRegion = go
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
          go (QualifiedAssume π e) = pure QualifiedAssume <*> typex π <*> term e
          go (QualifiedCheck e) = pure QualifiedCheck <*> term e
          go (TermCommon (RuntimePairIntroduction dσ e e')) = TermCommon <$> (pure RuntimePairIntroduction <*> pure dσ <*> term e <*> term e')
          go (Pack λ e) = pure Pack <*> typeBoundType λ <*> term e
          go (Unpack e) = pure Unpack <*> term e
          go (PureRegionTransformer π e) = pure PureRegionTransformer <*> typex π <*> term e
          go (DoRegionTransformer e λ) = pure DoRegionTransformer <*> term e <*> runtimeBound λ
          go (TermCommon (ReadReference dσ e)) = TermCommon <$> (pure ReadReference <*> pure dσ <*> term e)
          go (CastRegionTransformer π e) = pure CastRegionTransformer <*> typex π <*> term e
          go (TermCommon (LocalRegion dσ λ)) = TermCommon <$> (pure LocalRegion <*> pure dσ <*> localRegion λ)

foldTerm f (CoreTerm _ e) = f $ from e
  where
    (Isomorph _ from) = termf

mapTerm f (CoreTerm p e) = CoreTerm p $ to $ f $ from e
  where
    (Isomorph to from) = termf

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

localRegion = (termCommon .) $
  Prism (LocalRegion ()) $ \case
    (LocalRegion () λ) -> Just λ
    _ -> Nothing

qualifiedAssume = Prism (uncurry $ QualifiedAssume) $ \case
  (QualifiedAssume π e) -> Just (π, e)
  _ -> Nothing

qualifiedCheck = Prism (QualifiedCheck) $ \case
  (QualifiedCheck e) -> Just e
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

pureRegionTransformer = Prism (uncurry PureRegionTransformer) $ \case
  (PureRegionTransformer π e) -> Just (π, e)
  _ -> Nothing

doRegionTransformer = Prism (uncurry DoRegionTransformer) $ \case
  (DoRegionTransformer e λ) -> Just (e, λ)
  _ -> Nothing

readReference = (termCommon .) $
  Prism (ReadReference ()) $ \case
    (ReadReference () e) -> Just e
    _ -> Nothing

castRegionTransformer = Prism (uncurry CastRegionTransformer) $ \case
  (CastRegionTransformer π e) -> Just (π, e)
  _ -> Nothing

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
  freeVariables e = foldTerm (freeVariables @(Term p)) e
  convert ix x (CoreTerm p (TermCommon (Variable x'))) | x == x' = CoreTerm p $ TermCommon $ Variable ix
  convert ix x e = mapTerm (convert @(Term p) ix x) e
  substitute ux x (CoreTerm _ (TermCommon (Variable x'))) | x == x' = ux
  substitute ux x e = mapTerm (substitute ux x) e

instance Semigroup p => Algebra (Type p) p (Term p) where
  freeVariables = foldTerm (freeVariables @(Type p))
  convert ix x = mapTerm (convert @(Type p) ix x)
  substitute ux x = mapTerm (substitute ux x)

instance Semigroup p => Algebra (Kind p) p (Term p) where
  freeVariables = foldTerm (freeVariables @(Kind p))
  convert ix x = mapTerm (convert @(Kind p) ix x)
  substitute ux x = mapTerm (substitute ux x)

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

instance Semigroup p => Reduce (Term p) where
  reduce (CoreTerm _ (Bind e λ)) = apply (reduce λ) (reduce e) -- todo is (reduce λ) necessary here?
  reduce (CoreTerm _ (MacroApplication e1 e2)) | (CoreTerm _ (MacroAbstraction λ)) <- reduce e1 = apply λ (reduce e2)
  reduce (CoreTerm _ (TypeApplication e σ)) | (CoreTerm _ (TypeAbstraction λ)) <- reduce e = apply λ (reduce σ)
  reduce (CoreTerm _ (KindApplication e κ)) | (CoreTerm _ (KindAbstraction λ)) <- reduce e = apply λ (reduce κ)
  reduce (CoreTerm _ (QualifiedCheck e)) | (CoreTerm _ (QualifiedAssume _ e')) <- reduce e = e'
  reduce e = mapTerm reduce e

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
