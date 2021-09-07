module Language.Ast.Term where

import Control.Category (id, (.))
import Data.Bitraversable (bitraverse)
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Language.Ast.Common
import Language.Ast.Kind
import Language.Ast.Type
import Misc.Isomorph
import Misc.MonoidMap as Map
import Misc.Prism
import Misc.Symbol
import Prelude hiding (id, (.))

data PatternCommon σ pm
  = PatternVariable TermIdentifier σ
  | RuntimePatternPair pm pm
  deriving (Show)

data TermPatternF σ e pm
  = PatternCommon (PatternCommon σ pm)
  | PatternCopy e pm
  | PatternOfCourse pm
  deriving (Show)

data TermPattern θ κ σ p = CoreTermPattern p (TermPatternF σ (Term θ κ σ p) (TermPattern θ κ σ p)) deriving (Show)

data Arithmatic
  = Addition
  | Subtraction
  | Multiplication
  | Division
  deriving (Show, Eq)

data TermRuntime θ s σ λ ev e
  = Variable TermIdentifier θ
  | Alias e λ
  | Extern Symbol σ σ
  | FunctionApplication e e σ
  | RuntimePairIntroduction e e
  | FunctionLiteral λ
  | ReadReference ev e σ
  | NumberLiteral Integer σ
  | Arithmatic Arithmatic e e s
  deriving (Show)

data TermF θ κ σ λ e
  = TermRuntime (TermRuntime θ κ σ λ e e)
  | MacroAbstraction λ
  | MacroApplication e e
  | ImplicationAbstraction λ
  | ImplicationApplication e e
  | OfCourseIntroduction e
  | Bind e λ
  | PureRegionTransformer e
  | DoRegionTransformer e λ
  | ProofCopyNumber
  | ProofCopyFunction
  | ProofCopyPair e e
  | ProofCopyReference
  deriving (Show)

data Term θ κ σ p
  = CoreTerm
      p
      ( TermF
          θ
          κ
          σ
          (Bound (TermPattern θ κ σ p) (Term θ κ σ p))
          (Term θ κ σ p)
      )
  deriving (Show)

coreTermPattern = Isomorph (uncurry $ CoreTermPattern) $ \(CoreTermPattern p pm) -> (p, pm)

patternOfCourse = Prism PatternOfCourse $ \case
  (PatternOfCourse pm) -> Just pm
  _ -> Nothing

patternCommon = Prism PatternCommon $ \case
  PatternCommon pm -> Just pm
  _ -> Nothing

patternVariable = (patternCommon .) $
  Prism (uncurry PatternVariable) $ \case
    (PatternVariable x σ) -> Just (x, σ)
    _ -> Nothing

patternRuntimePair = (patternCommon .) $
  Prism (uncurry RuntimePatternPair) $ \case
    (RuntimePatternPair pm pm') -> Just (pm, pm')
    _ -> Nothing

patternCopy =
  Prism (uncurry PatternCopy) $ \case
    (PatternCopy e pm) -> Just (e, pm)
    _ -> Nothing

coreTerm = Isomorph (uncurry CoreTerm) $ \(CoreTerm p e) -> (p, e)

termRuntime = Prism TermRuntime $ \case
  (TermRuntime e) -> Just e
  _ -> Nothing

variable = (termRuntime .) $
  Prism (uncurry Variable) $ \case
    (Variable x θ) -> Just (x, θ)
    _ -> Nothing

macroAbstraction = Prism (MacroAbstraction) $ \case
  (MacroAbstraction λ) -> Just λ
  _ -> Nothing

macroApplication = Prism (uncurry $ MacroApplication) $ \case
  (MacroApplication e e') -> Just (e, e')
  _ -> Nothing

implicationAbstraction = Prism (ImplicationAbstraction) $ \case
  (ImplicationAbstraction λ) -> Just λ
  _ -> Nothing

implicationApplication = Prism (uncurry $ ImplicationApplication) $ \case
  (ImplicationApplication e e') -> Just (e, e')
  _ -> Nothing

ofCourseIntroduction = Prism (OfCourseIntroduction) $ \case
  (OfCourseIntroduction e) -> Just e
  _ -> Nothing

bind = Prism (uncurry $ Bind) $ \case
  (Bind e λ) -> Just (e, λ)
  _ -> Nothing

alias = (termRuntime .) $
  Prism (uncurry $ Alias) $ \case
    (Alias e λ) -> Just (e, λ)
    _ -> Nothing

extern = (termRuntime .) $
  Prism (uncurry $ uncurry $ Extern) $ \case
    (Extern path σ τs) -> Just ((path, σ), τs)
    _ -> Nothing

functionApplication = (termRuntime .) $
  Prism (uncurry $ uncurry $ FunctionApplication) $ \case
    (FunctionApplication e e' σ) -> Just ((e, e'), σ)
    _ -> Nothing

functionLiteral = (termRuntime .) $
  Prism (FunctionLiteral) $ \case
    (FunctionLiteral λ) -> Just λ
    _ -> Nothing

runtimePairIntrouction = (termRuntime .) $
  Prism (uncurry $ RuntimePairIntroduction) $ \case
    (RuntimePairIntroduction e1 e2) -> Just (e1, e2)
    _ -> Nothing

pureRegionTransformer = Prism PureRegionTransformer $ \case
  (PureRegionTransformer e) -> Just e
  _ -> Nothing

doRegionTransformer = Prism (uncurry DoRegionTransformer) $ \case
  (DoRegionTransformer e λ) -> Just (e, λ)
  _ -> Nothing

readReference = (termRuntime .) $
  Prism (uncurry $ uncurry $ ReadReference) $ \case
    (ReadReference ev e σ) -> Just ((ev, e), σ)
    _ -> Nothing

numberLiteral = (termRuntime .) $
  Prism (uncurry $ NumberLiteral) $ \case
    (NumberLiteral n σ) -> Just (n, σ)
    _ -> Nothing

proofCopyNumber = Prism (const ProofCopyNumber) $ \case
  ProofCopyNumber -> Just ()
  _ -> Nothing

proofCopyFunction = Prism (const ProofCopyFunction) $ \case
  ProofCopyFunction -> Just ()
  _ -> Nothing

proofCopyPair = Prism (uncurry $ ProofCopyPair) $ \case
  ProofCopyPair e e' -> Just (e, e')
  _ -> Nothing

proofCopyReference = Prism (const ProofCopyReference) $ \case
  ProofCopyReference -> Just ()
  _ -> Nothing

arithmatic o = (termRuntime .) $
  Prism (uncurry $ uncurry $ Arithmatic o) $ \case
    Arithmatic o' e e' κ | o == o' -> Just ((e, e'), κ)
    _ -> Nothing

traversePatternCommon ::
  Applicative m =>
  (σ -> m σ') ->
  (pm -> m pm') ->
  PatternCommon σ pm ->
  m (PatternCommon σ' pm')
traversePatternCommon f g pm = case pm of
  PatternVariable x σ -> pure PatternVariable <*> pure x <*> f σ
  RuntimePatternPair pm pm' -> pure RuntimePatternPair <*> g pm <*> g pm'

traverseTermPatternF ::
  Applicative m =>
  (σ -> m σ') ->
  (e -> m e') ->
  (pm -> m pm') ->
  TermPatternF σ e pm ->
  m (TermPatternF σ' e' pm')
traverseTermPatternF f h g pm = case pm of
  PatternCommon pm -> pure PatternCommon <*> traversePatternCommon f g pm
  PatternCopy e pm -> pure PatternCopy <*> h e <*> g pm
  PatternOfCourse pm -> pure PatternOfCourse <*> g pm

foldTermPatternF f h g = getConst . traverseTermPatternF (Const . f) (Const . h) (Const . g)

mapTermPatternF f h g = runIdentity . traverseTermPatternF (Identity . f) (Identity . h) (Identity . g)

traverseTermPattern ::
  Applicative m =>
  (θ -> m θ') ->
  (κ -> m κ') ->
  (σ -> m σ') ->
  (p -> m p') ->
  TermPattern θ κ σ p ->
  m (TermPattern θ' κ' σ' p')
traverseTermPattern h i f g (CoreTermPattern p pm) =
  pure CoreTermPattern <*> g p <*> traverseTermPatternF f (traverseTerm h i f g) (traverseTermPattern h i f g) pm

foldTermPattern h i f g = getConst . traverseTermPattern (Const . h) (Const . i) (Const . f) (Const . g)

mapTermPattern h i f g = runIdentity . traverseTermPattern (Identity . h) (Identity . i) (Identity . f) (Identity . g)

traverseTermRuntime ::
  Applicative m =>
  (θ -> m θ') ->
  (s -> m s') ->
  (σ -> m σ') ->
  (λ -> m λ') ->
  (ev -> m ev') ->
  (e -> m e') ->
  TermRuntime θ s σ λ ev e ->
  m (TermRuntime θ' s' σ' λ' ev' e')
traverseTermRuntime d h f g j i e =
  case e of
    Variable x θ -> pure Variable <*> pure x <*> d θ
    Alias e λ -> pure Alias <*> i e <*> g λ
    Extern sm σ σ' -> pure Extern <*> pure sm <*> f σ <*> f σ'
    FunctionApplication e1 e2 σ -> pure FunctionApplication <*> i e1 <*> i e2 <*> f σ
    RuntimePairIntroduction e1 e2 -> pure RuntimePairIntroduction <*> i e1 <*> i e2
    FunctionLiteral λ -> pure FunctionLiteral <*> g λ
    ReadReference ev e σ -> pure ReadReference <*> j ev <*> i e <*> f σ
    NumberLiteral n σ -> pure NumberLiteral <*> pure n <*> f σ
    Arithmatic o e e' κ -> pure Arithmatic <*> pure o <*> i e <*> i e' <*> h κ

traverseTermF ::
  Applicative m =>
  (θ -> m θ') ->
  (κ -> m κ') ->
  (σ -> m σ') ->
  (λ -> m λ') ->
  (e -> m e') ->
  TermF θ κ σ λ e ->
  m (TermF θ' κ' σ' λ' e')
traverseTermF d j f h i e =
  case e of
    TermRuntime e -> pure TermRuntime <*> traverseTermRuntime d j f h i i e
    MacroAbstraction λ -> pure MacroAbstraction <*> h λ
    MacroApplication e1 e2 -> pure MacroApplication <*> i e1 <*> i e2
    ImplicationAbstraction λ -> pure ImplicationAbstraction <*> h λ
    ImplicationApplication e1 e2 -> pure ImplicationApplication <*> i e1 <*> i e2
    OfCourseIntroduction e -> pure OfCourseIntroduction <*> i e
    Bind e λ -> pure Bind <*> i e <*> h λ
    PureRegionTransformer e -> pure PureRegionTransformer <*> i e
    DoRegionTransformer e λx -> pure DoRegionTransformer <*> i e <*> h λx
    ProofCopyNumber -> pure ProofCopyNumber
    ProofCopyFunction -> pure ProofCopyFunction
    ProofCopyPair e e' -> pure ProofCopyPair <*> i e <*> i e'
    ProofCopyReference -> pure ProofCopyReference

foldTermF d j f h i = getConst . traverseTermF (Const . d) (Const . j) (Const . f) (Const . h) (Const . i)

mapTermF d j f h i = runIdentity . traverseTermF (Identity . d) (Identity . j) (Identity . f) (Identity . h) (Identity . i)

traverseTerm ::
  Applicative m =>
  (θ -> m θ') ->
  (κ -> m κ') ->
  (σ -> m σ') ->
  (p -> m p') ->
  Term θ κ σ p ->
  m (Term θ' κ' σ' p')
traverseTerm d h f g (CoreTerm p e) =
  let recurse = traverseTerm d h f g
   in pure CoreTerm <*> g p
        <*> traverseTermF
          d
          h
          f
          (bitraverse (traverseTermPattern d h f g) recurse)
          recurse
          e

mapTerm d h f g = runIdentity . traverseTerm (Identity . d) (Identity . h) (Identity . f) (Identity . g)

instance Substitute (Term θ κ σ p) TermIdentifier σ where
  substitute _ _ = id

instance Substitute (Term θ κ σ p) TermIdentifier θ where
  substitute _ _ = id

instance Functor (TermPattern θ κ σ) where
  fmap f = mapTermPattern id id id f

instance Functor (Term θ κ σ) where
  fmap f = mapTerm id id id f

instance
  ( Semigroup p
  ) =>
  FreeVariables TermIdentifier p (TermPattern θ κ σ p)
  where
  freeVariables (CoreTermPattern _ pm) = foldTermPatternF mempty go go pm
    where
      go = freeVariables

instance Convert TermIdentifier (TermPattern θ κ σ p) where
  convert ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF id go go pm
    where
      go = convert ux x

instance
  ( Correct θ (Term θ κ σ p)
  ) =>
  Substitute (Term θ κ σ p) TermIdentifier (TermPattern θ κ σ p)
  where
  substitute ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go go pm
    where
      go = substitute ux x

instance
  ( FreeVariables TypeIdentifier p θ,
    FreeVariables TypeIdentifier p σ,
    Semigroup p
  ) =>
  FreeVariables TypeIdentifier p (TermPattern θ κ σ p)
  where
  freeVariables (CoreTermPattern _ pm) = foldTermPatternF go go go pm
    where
      go = freeVariables

instance
  ( Substitute σ TypeIdentifier θ,
    Substitute σ TypeIdentifier σ'
  ) =>
  Substitute σ TypeIdentifier (TermPattern θ κ σ' p)
  where
  substitute ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go go pm
    where
      go = substitute ux x

instance
  ( Substitute κ KindIdentifier θ,
    Substitute κ KindIdentifier σ,
    Substitute κ KindIdentifier κ'
  ) =>
  Substitute κ KindIdentifier (TermPattern θ κ' σ p)
  where
  substitute ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go go pm
    where
      go = substitute ux x

instance
  () =>
  Rename TermIdentifier (TermPattern θ κ σ p)
  where
  rename ux x (CoreTermPattern p (PatternCommon (PatternVariable x' σ))) | x == x' = CoreTermPattern p $ PatternCommon $ PatternVariable ux σ
  rename ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF id id go pm
    where
      go = rename ux x

instance
  () =>
  Bindings TermIdentifier Internal (TermPattern θ κ σ Internal)
  where
  bindings (CoreTermPattern p (PatternCommon (PatternVariable x _))) = Map.singleton x p
  bindings (CoreTermPattern _ pm) = foldTermPatternF mempty mempty go pm
    where
      go = bindings

instance Reduce (TermPattern InstantiationInfer KindInfer TypeInfer p) where
  reduce (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go go pm
    where
      go = reduce

instance
  ( Semigroup p
  ) =>
  FreeVariables TermIdentifier p (Term θ κ σ p)
  where
  freeVariables (CoreTerm p (TermRuntime (Variable x _))) = Map.singleton x p
  freeVariables (CoreTerm _ e) = foldTermF mempty mempty mempty go go e
    where
      go = freeVariables

instance
  () =>
  Convert TermIdentifier (Term θ κ σ p)
  where
  convert ux x (CoreTerm p (TermRuntime (Variable x' θ))) | x == x' = CoreTerm p $ TermRuntime $ Variable ux θ
  convert ux x (CoreTerm p e) = CoreTerm p $ mapTermF id id id go go e
    where
      go = convert ux x

instance
  ( Correct θ (Term θ κ σ p)
  ) =>
  Substitute (Term θ κ σ p) TermIdentifier (Term θ κ σ p)
  where
  substitute ux x (CoreTerm _ (TermRuntime (Variable x' θ))) | x == x' = correct θ ux
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTermF id id id go go e
    where
      go = substitute ux x

instance
  ( Semigroup p,
    FreeVariables TypeIdentifier p σ,
    FreeVariables TypeIdentifier p θ
  ) =>
  FreeVariables TypeIdentifier p (Term θ κ σ p)
  where
  freeVariables (CoreTerm _ e) = foldTermF go mempty go go go e
    where
      go = freeVariables

instance
  ( Substitute σ TypeIdentifier θ,
    Substitute σ TypeIdentifier σ'
  ) =>
  Substitute σ TypeIdentifier (Term θ κ σ' p)
  where
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTermF go id go go go e
    where
      go = substitute ux x

instance
  ( Substitute κ KindIdentifier σ,
    Substitute κ KindIdentifier θ,
    Substitute κ KindIdentifier κ'
  ) =>
  Substitute κ KindIdentifier (Term θ κ' σ p)
  where
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTermF go go go go go e
    where
      go = substitute ux x

instance Correct InstantiationInfer (Term InstantiationInfer KindInfer TypeInfer p) where
  correct (InstantiateEmpty) e = e
  correct (InstantiateType x σ θ) e = substitute σ x $ correct θ e
  correct (InstantiateKind x κ θ) e = substitute κ x $ correct θ e

instance Reduce (Term InstantiationInfer KindInfer TypeInfer p) where
  reduce (CoreTerm _ (Bind e λ)) = apply (reduce λ) (reduce e)
  reduce (CoreTerm _ (MacroApplication e1 e2)) | (CoreTerm _ (MacroAbstraction λ)) <- reduce e1 = apply λ (reduce e2)
  reduce (CoreTerm p e) = CoreTerm p (mapTermF go go go go go e)
    where
      go = reduce

instance
  Apply
    (Bound (TermPattern InstantiationInfer KindInfer TypeInfer p) (Term InstantiationInfer KindInfer TypeInfer p))
    (Term InstantiationInfer KindInfer TypeInfer p)
    (Term InstantiationInfer KindInfer TypeInfer p)
  where
  apply (Bound (CoreTermPattern _ (PatternCommon (PatternVariable x _))) e) ux = reduce $ substitute ux x e
  apply (Bound (CoreTermPattern _ (PatternOfCourse pm)) e) (CoreTerm _ (OfCourseIntroduction ux)) = apply (Bound pm e) ux
  -- todo find better position here
  apply λ ux@(CoreTerm p _) = CoreTerm p $ Bind ux λ

instance
  ( FreeVariables TermIdentifier p u,
    Semigroup p
  ) =>
  FreeVariables TermIdentifier p (Bound (TermPattern θ κ σ p) u)
  where
  freeVariables = freeVariablesBoundDependent

instance
  ( Convert TermIdentifier u
  ) =>
  Convert TermIdentifier (Bound (TermPattern θ κ σ p) u)
  where
  convert = substituteDependent convert convert (avoidCaptureConvert @TermIdentifier)

instance
  ( Substitute (Term θ κ σ p) TermIdentifier u,
    Correct θ (Term θ κ σ p),
    Convert TermIdentifier u
  ) =>
  Substitute (Term θ κ σ p) TermIdentifier (Bound (TermPattern θ κ σ p) u)
  where
  substitute = substituteDependent substitute substitute (avoidCapture @TermIdentifier)

instance
  ( FreeVariables TypeIdentifier p u,
    FreeVariables TypeIdentifier p σ,
    FreeVariables TypeIdentifier p θ,
    Semigroup p
  ) =>
  FreeVariables TypeIdentifier p (Bound (TermPattern θ κ σ p) u)
  where
  freeVariables (Bound pm e) = freeVariables pm <> freeVariables e

instance
  ( Substitute σ TypeIdentifier σ',
    Substitute σ TypeIdentifier u,
    Substitute σ TypeIdentifier θ
  ) =>
  Substitute σ TypeIdentifier (Bound (TermPattern θ κ' σ' p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  ( Substitute κ KindIdentifier u,
    Substitute κ KindIdentifier σ,
    Substitute κ KindIdentifier θ,
    Substitute κ KindIdentifier κ'
  ) =>
  Substitute κ KindIdentifier (Bound (TermPattern θ κ' σ p) u)
  where
  substitute = substituteHigher substitute substitute

instance FreeVariablesInternal TermIdentifier (Term θ κ σ p) where
  freeVariablesInternal = freeVariables . (Internal <$)

instance BindingsInternal TermIdentifier (TermPattern θ κ σ p) where
  bindingsInternal = bindings . (Internal <$)

instance Location (Term θ κ σ) where
  location (CoreTerm p _) = p

instance Location (TermPattern θ κ σ) where
  location (CoreTermPattern p _) = p
