module Ast.Term where

import Ast.Common
import Ast.Kind
import Ast.Type
import Control.Category (id, (.))
import Data.Bitraversable (bitraverse)
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Misc.Isomorph
import Misc.Prism
import Misc.Symbol
import Prelude hiding (id, (.))

data TermPatternF σ pm
  = PatternVariable TermIdentifier σ
  | PatternOfCourse pm
  deriving (Show)

data TermPattern θ κ σ p = CoreTermPattern p (TermPatternF σ (TermPattern θ κ σ p)) deriving (Show)

type TermPatternAuto p = TermPattern () (KindAuto p) (TypeAuto p) p

type TermPatternUnify = TermPattern InstantiationUnify KindUnify TypeUnify

type TermPatternInfer = TermPattern InstantiationInfer KindInfer TypeInfer

data TermRuntimePatternF σ pm
  = RuntimePatternVariable TermIdentifier σ
  | RuntimePatternPair pm pm
  deriving (Show)

data TermRuntimePattern θ κ σ p = CoreTermRuntimePattern p (TermRuntimePatternF σ (TermRuntimePattern θ κ σ p)) deriving (Show)

type TermRuntimePatternAuto p = TermRuntimePattern () (KindAuto p) (TypeAuto p) p

type TermRuntimePatternUnify = TermRuntimePattern InstantiationUnify KindUnify TypeUnify

type TermRuntimePatternInfer = TermRuntimePattern InstantiationInfer KindInfer TypeInfer

data Arithmatic
  = Addition
  | Subtraction
  | Multiplication
  | Division
  deriving (Show, Eq)

data TermRuntime θ s σ' σ λ ev e
  = Variable TermIdentifier θ
  | Alias e λ
  | Extern Symbol σ σ' σ
  | FunctionApplication e e σ
  | PairIntroduction e e
  | ReadReference e
  | NumberLiteral Integer
  | Arithmatic Arithmatic e e s
  deriving (Show)

data TermF λtl λt θ κ σ λ λr e
  = TermRuntime (TermRuntime θ κ σ σ λr e e)
  | FunctionLiteral λr
  | MacroAbstraction λ
  | MacroApplication e e σ
  | OfCourseIntroduction e
  | Bind e λ
  | TypeAbstraction λtl (Set Constraint)
  | TypeApplication e σ λt (Set Constraint)
  deriving (Show)

data Term θ κ σ p
  = CoreTerm
      p
      ( TermF
          (Bound (Pattern TypeIdentifier κ p) (Term θ κ σ p))
          (Bound (Pattern TypeIdentifier κ p) σ)
          θ
          κ
          σ
          (Bound (TermPattern θ κ σ p) (Term θ κ σ p))
          (Bound (TermRuntimePattern θ κ σ p) (Term θ κ σ p))
          (Term θ κ σ p)
      )
  deriving (Show)

type TermAuto p = Term () (KindAuto p) (TypeAuto p) p

type TermUnify = Term InstantiationUnify KindUnify TypeUnify

type TermInfer = Term InstantiationInfer KindInfer TypeInfer

coreTermPattern = Isomorph (uncurry $ CoreTermPattern) $ \(CoreTermPattern p pm) -> (p, pm)

coreTermRuntimePattern = Isomorph (uncurry $ CoreTermRuntimePattern) $ \(CoreTermRuntimePattern p pm) -> (p, pm)

patternOfCourse = Prism PatternOfCourse $ \case
  (PatternOfCourse pm) -> Just pm
  _ -> Nothing

patternVariable =
  Prism (uncurry PatternVariable) $ \case
    (PatternVariable x σ) -> Just (x, σ)
    _ -> Nothing

runtimePatternVariable =
  Prism (uncurry RuntimePatternVariable) $ \case
    (RuntimePatternVariable x σ) -> Just (x, σ)
    _ -> Nothing

runtimePatternPair =
  Prism (uncurry RuntimePatternPair) $ \case
    (RuntimePatternPair pm pm') -> Just (pm, pm')
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

macroApplication = Prism (uncurry $ uncurry $ MacroApplication) $ \case
  (MacroApplication e e' σ) -> Just ((e, e'), σ)
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
  Prism (uncurry $ uncurry $ uncurry $ Extern) $ \case
    (Extern path σ π τ) -> Just (((path, σ), π), τ)
    _ -> Nothing

functionApplication = (termRuntime .) $
  Prism (uncurry $ uncurry $ FunctionApplication) $ \case
    (FunctionApplication e e' σ) -> Just ((e, e'), σ)
    _ -> Nothing

functionLiteral =
  Prism (FunctionLiteral) $ \case
    (FunctionLiteral λ) -> Just λ
    _ -> Nothing

runtimePairIntrouction = (termRuntime .) $
  Prism (uncurry $ PairIntroduction) $ \case
    (PairIntroduction e1 e2) -> Just (e1, e2)
    _ -> Nothing

readReference = (termRuntime .) $
  Prism (ReadReference) $ \case
    (ReadReference e) -> Just (e)
    _ -> Nothing

numberLiteral = (termRuntime .) $
  Prism (NumberLiteral) $ \case
    (NumberLiteral n) -> Just n
    _ -> Nothing

arithmatic o = (termRuntime .) $
  Prism (uncurry $ uncurry $ Arithmatic o) $ \case
    Arithmatic o' e e' κ | o == o' -> Just ((e, e'), κ)
    _ -> Nothing

typeLambda = Prism (uncurry TypeAbstraction) $ \case
  TypeAbstraction pm c -> Just (pm, c)
  _ -> Nothing

typeApplication = Prism (uncurry $ uncurry $ uncurry TypeApplication) $ \case
  TypeApplication e σ λ c -> Just (((e, σ), λ), c)
  _ -> Nothing

traverseTermPatternF ::
  Applicative m =>
  (σ -> m σ') ->
  (pm -> m pm') ->
  TermPatternF σ pm ->
  m (TermPatternF σ' pm')
traverseTermPatternF f g pm = case pm of
  PatternVariable x σ -> pure PatternVariable <*> pure x <*> f σ
  PatternOfCourse pm -> pure PatternOfCourse <*> g pm

foldTermPatternF f h = getConst . traverseTermPatternF (Const . f) (Const . h)

mapTermPatternF f h = runIdentity . traverseTermPatternF (Identity . f) (Identity . h)

traverseTermPattern ::
  Applicative m =>
  (θ -> m θ') ->
  (κ -> m κ') ->
  (σ -> m σ') ->
  (p -> m p') ->
  TermPattern θ κ σ p ->
  m (TermPattern θ' κ' σ' p')
traverseTermPattern h i f g (CoreTermPattern p pm) =
  pure CoreTermPattern <*> g p <*> traverseTermPatternF f (traverseTermPattern h i f g) pm

foldTermPattern h i f g = getConst . traverseTermPattern (Const . h) (Const . i) (Const . f) (Const . g)

mapTermPattern h i f g = runIdentity . traverseTermPattern (Identity . h) (Identity . i) (Identity . f) (Identity . g)

traverseTermRuntimePatternF ::
  Applicative m =>
  (σ -> m σ') ->
  (pm -> m pm') ->
  TermRuntimePatternF σ pm ->
  m (TermRuntimePatternF σ' pm')
traverseTermRuntimePatternF f h pm = case pm of
  RuntimePatternVariable x σ -> pure RuntimePatternVariable <*> pure x <*> f σ
  RuntimePatternPair pm pm' -> pure RuntimePatternPair <*> h pm <*> h pm'

foldTermRuntimePatternF f h = getConst . traverseTermRuntimePatternF (Const . f) (Const . h)

mapTermRuntimePatternF f h = runIdentity . traverseTermRuntimePatternF (Identity . f) (Identity . h)

traverseTermRuntimePattern ::
  Applicative m =>
  (θ -> m θ') ->
  (κ -> m κ') ->
  (σ -> m σ') ->
  (p -> m p') ->
  TermRuntimePattern θ κ σ p ->
  m (TermRuntimePattern θ' κ' σ' p')
traverseTermRuntimePattern h i f g (CoreTermRuntimePattern p pm) =
  pure CoreTermRuntimePattern <*> g p <*> traverseTermRuntimePatternF f (traverseTermRuntimePattern h i f g) pm

foldTermRuntimePattern h i f g = getConst . traverseTermRuntimePattern (Const . h) (Const . i) (Const . f) (Const . g)

mapTermRuntimePattern h i f g = runIdentity . traverseTermRuntimePattern (Identity . h) (Identity . i) (Identity . f) (Identity . g)

traverseTermRuntime ::
  Applicative m =>
  (θ -> m θ') ->
  (s -> m s') ->
  (σ2 -> m σ2') ->
  (σ -> m σ') ->
  (λ -> m λ') ->
  (e -> m e') ->
  TermRuntime θ s σ2 σ λ ev e ->
  m (TermRuntime θ' s' σ2' σ' λ' ev' e')
traverseTermRuntime d h y f g i e =
  case e of
    Variable x θ -> pure Variable <*> pure x <*> d θ
    Alias e λ -> pure Alias <*> i e <*> g λ
    Extern sm σ σ'' σ' -> pure Extern <*> pure sm <*> f σ <*> y σ'' <*> f σ'
    FunctionApplication e1 e2 σ -> pure FunctionApplication <*> i e1 <*> i e2 <*> f σ
    PairIntroduction e1 e2 -> pure PairIntroduction <*> i e1 <*> i e2
    ReadReference e -> pure ReadReference <*> i e
    NumberLiteral n -> pure NumberLiteral <*> pure n
    Arithmatic o e e' κ -> pure Arithmatic <*> pure o <*> i e <*> i e' <*> h κ

traverseTermF ::
  Applicative m =>
  (λtl -> m λtl') ->
  (λσ -> m λσ') ->
  (θ -> m θ') ->
  (κ -> m κ') ->
  (σ -> m σ') ->
  (λ -> m λ') ->
  (λr -> m λr') ->
  (e -> m e') ->
  TermF λtl λσ θ κ σ λ λr e ->
  m (TermF λtl' λσ' θ' κ' σ' λ' λr' e')
traverseTermF k l d j f h m i e =
  case e of
    TermRuntime e -> pure TermRuntime <*> traverseTermRuntime d j f f m i e
    FunctionLiteral λ -> pure FunctionLiteral <*> m λ
    MacroAbstraction λ -> pure MacroAbstraction <*> h λ
    MacroApplication e1 e2 σ -> pure MacroApplication <*> i e1 <*> i e2 <*> f σ
    OfCourseIntroduction e -> pure OfCourseIntroduction <*> i e
    Bind e λ -> pure Bind <*> i e <*> h λ
    TypeAbstraction λ c -> pure TypeAbstraction <*> k λ <*> pure c
    TypeApplication e σ λ c -> pure TypeApplication <*> i e <*> f σ <*> l λ <*> pure c

foldTermF l k d j f h m i = getConst . traverseTermF (Const . l) (Const . k) (Const . d) (Const . j) (Const . f) (Const . h) (Const . m) (Const . i)

mapTermF l k d j f h m i = runIdentity . traverseTermF (Identity . l) (Identity . k) (Identity . d) (Identity . j) (Identity . f) (Identity . h) (Identity . m) (Identity . i)

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
          (bitraverse (traversePattern pure h g) recurse)
          (bitraverse (traversePattern pure h g) f)
          d
          h
          f
          (bitraverse (traverseTermPattern d h f g) recurse)
          (bitraverse (traverseTermRuntimePattern d h f g) recurse)
          recurse
          e

mapTerm d h f g = runIdentity . traverseTerm (Identity . d) (Identity . h) (Identity . f) (Identity . g)

instance Substitute (Term θ κ σ p) TermIdentifier σ where
  substitute _ _ = id

instance Functor (Term θ κ σ) where
  fmap f = mapTerm id id id f

instance Functor (TermRuntimePattern θ κ σ) where
  fmap f = mapTermRuntimePattern id id id f

instance Functor (TermPattern θ κ σ) where
  fmap f = mapTermPattern id id id f

instance
  ( FreeVariables TermIdentifier σ
  ) =>
  FreeVariables TermIdentifier (TermPattern θ κ σ p)
  where
  freeVariables (CoreTermPattern _ pm) = foldTermPatternF mempty go pm
    where
      go = freeVariables

instance
  ( Semigroup p,
    FreeVariablesPositioned TermIdentifier p σ
  ) =>
  FreeVariablesPositioned TermIdentifier p (TermPattern θ κ σ p)
  where
  freeVariablesPositioned (CoreTermPattern _ pm) = foldTermPatternF mempty go pm
    where
      go = freeVariablesPositioned

instance
  ( Convert TypeIdentifier θ,
    Convert TermIdentifier σ
  ) =>
  Convert TermIdentifier (TermPattern θ κ σ p)
  where
  convert ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF id go pm
    where
      go = convert ux x

instance
  ( Correct θ (Term θ κ σ p),
    Convert TermIdentifier σ,
    Convert TypeIdentifier σ,
    Convert TypeIdentifier θ
  ) =>
  Substitute (Term θ κ σ p) TermIdentifier (TermPattern θ κ σ p)
  where
  substitute ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go pm
    where
      go = substitute ux x

instance
  ( FreeVariables TypeIdentifier θ,
    FreeVariables TypeIdentifier σ
  ) =>
  FreeVariables TypeIdentifier (TermPattern θ κ σ p)
  where
  freeVariables (CoreTermPattern _ pm) = foldTermPatternF go go pm
    where
      go = freeVariables

instance
  ( Convert TypeIdentifier θ,
    Convert TypeIdentifier σ
  ) =>
  Convert TypeIdentifier (TermPattern θ κ σ p)
  where
  convert ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go pm
    where
      go = convert ux x

instance
  ( Substitute σ TypeIdentifier θ,
    Substitute σ TypeIdentifier σ',
    FreeVariables TypeIdentifier σ,
    Convert TypeIdentifier σ',
    Convert TypeIdentifier θ
  ) =>
  Substitute σ TypeIdentifier (TermPattern θ κ σ' p)
  where
  substitute ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go pm
    where
      go = substitute ux x

instance Substitute TypeUnify TypeLogicalRaw (TermPattern InstantiationUnify KindUnify TypeUnify p) where
  substitute ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go pm
    where
      go = substitute ux x

instance
  ( Convert KindIdentifier θ,
    Convert KindIdentifier σ,
    Convert KindIdentifier κ
  ) =>
  Convert KindIdentifier (TermPattern θ κ σ p)
  where
  convert ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go pm
    where
      go = convert ux x

instance
  ( Substitute κ KindIdentifier θ,
    Substitute κ KindIdentifier σ,
    Substitute κ KindIdentifier κ'
  ) =>
  Substitute κ KindIdentifier (TermPattern θ κ' σ p)
  where
  substitute ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go pm
    where
      go = substitute ux x

instance Substitute KindUnify KindLogicalRaw (TermPattern InstantiationUnify KindUnify TypeUnify p) where
  substitute ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go pm
    where
      go = substitute ux x

instance
  () =>
  Rename TermIdentifier (TermPattern θ κ σ p)
  where
  rename ux x (CoreTermPattern p (PatternVariable x' σ)) | x == x' = CoreTermPattern p $ PatternVariable ux σ
  rename ux x (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF id go pm
    where
      go = rename ux x

instance
  () =>
  Bindings TermIdentifier (TermPattern θ κ σ p)
  where
  bindings (CoreTermPattern _ (PatternVariable x _)) = Set.singleton x
  bindings (CoreTermPattern _ pm) = foldTermPatternF mempty go pm
    where
      go = bindings

instance Reduce (TermPattern InstantiationInfer KindInfer TypeInfer p) where
  reduce (CoreTermPattern p pm) = CoreTermPattern p $ mapTermPatternF go go pm
    where
      go = reduce

instance
  ( FreeVariables TermIdentifier σ
  ) =>
  FreeVariables TermIdentifier (TermRuntimePattern θ κ σ p)
  where
  freeVariables (CoreTermRuntimePattern _ pm) = foldTermRuntimePatternF mempty go pm
    where
      go = freeVariables

instance
  ( Semigroup p,
    FreeVariablesPositioned TermIdentifier p σ
  ) =>
  FreeVariablesPositioned TermIdentifier p (TermRuntimePattern θ κ σ p)
  where
  freeVariablesPositioned (CoreTermRuntimePattern _ pm) = foldTermRuntimePatternF mempty go pm
    where
      go = freeVariablesPositioned

instance
  ( Convert TypeIdentifier θ,
    Convert TermIdentifier σ
  ) =>
  Convert TermIdentifier (TermRuntimePattern θ κ σ p)
  where
  convert ux x (CoreTermRuntimePattern p pm) = CoreTermRuntimePattern p $ mapTermRuntimePatternF id go pm
    where
      go = convert ux x

instance
  ( Correct θ (Term θ κ σ p),
    Convert TermIdentifier σ,
    Convert TypeIdentifier σ,
    Convert TypeIdentifier θ
  ) =>
  Substitute (Term θ κ σ p) TermIdentifier (TermRuntimePattern θ κ σ p)
  where
  substitute ux x (CoreTermRuntimePattern p pm) = CoreTermRuntimePattern p $ mapTermRuntimePatternF go go pm
    where
      go = substitute ux x

instance
  ( FreeVariables TypeIdentifier θ,
    FreeVariables TypeIdentifier σ
  ) =>
  FreeVariables TypeIdentifier (TermRuntimePattern θ κ σ p)
  where
  freeVariables (CoreTermRuntimePattern _ pm) = foldTermRuntimePatternF go go pm
    where
      go = freeVariables

instance
  ( Convert TypeIdentifier θ,
    Convert TypeIdentifier σ
  ) =>
  Convert TypeIdentifier (TermRuntimePattern θ κ σ p)
  where
  convert ux x (CoreTermRuntimePattern p pm) = CoreTermRuntimePattern p $ mapTermRuntimePatternF go go pm
    where
      go = convert ux x

instance
  ( Substitute σ TypeIdentifier θ,
    Substitute σ TypeIdentifier σ',
    FreeVariables TypeIdentifier σ,
    Convert TypeIdentifier σ',
    Convert TypeIdentifier θ
  ) =>
  Substitute σ TypeIdentifier (TermRuntimePattern θ κ σ' p)
  where
  substitute ux x (CoreTermRuntimePattern p pm) = CoreTermRuntimePattern p $ mapTermRuntimePatternF go go pm
    where
      go = substitute ux x

instance Substitute TypeUnify TypeLogicalRaw (TermRuntimePattern InstantiationUnify KindUnify TypeUnify p) where
  substitute ux x (CoreTermRuntimePattern p pm) = CoreTermRuntimePattern p $ mapTermRuntimePatternF go go pm
    where
      go = substitute ux x

instance
  ( Convert KindIdentifier θ,
    Convert KindIdentifier σ,
    Convert KindIdentifier κ
  ) =>
  Convert KindIdentifier (TermRuntimePattern θ κ σ p)
  where
  convert ux x (CoreTermRuntimePattern p pm) = CoreTermRuntimePattern p $ mapTermRuntimePatternF go go pm
    where
      go = convert ux x

instance
  ( Substitute κ KindIdentifier θ,
    Substitute κ KindIdentifier σ,
    Substitute κ KindIdentifier κ'
  ) =>
  Substitute κ KindIdentifier (TermRuntimePattern θ κ' σ p)
  where
  substitute ux x (CoreTermRuntimePattern p pm) = CoreTermRuntimePattern p $ mapTermRuntimePatternF go go pm
    where
      go = substitute ux x

instance Substitute KindUnify KindLogicalRaw (TermRuntimePattern InstantiationUnify KindUnify TypeUnify p) where
  substitute ux x (CoreTermRuntimePattern p pm) = CoreTermRuntimePattern p $ mapTermRuntimePatternF go go pm
    where
      go = substitute ux x

instance
  () =>
  Rename TermIdentifier (TermRuntimePattern θ κ σ p)
  where
  rename ux x (CoreTermRuntimePattern p (RuntimePatternVariable x' σ)) | x == x' = CoreTermRuntimePattern p $ RuntimePatternVariable ux σ
  rename ux x (CoreTermRuntimePattern p pm) = CoreTermRuntimePattern p $ mapTermRuntimePatternF id go pm
    where
      go = rename ux x

instance
  () =>
  Bindings TermIdentifier (TermRuntimePattern θ κ σ p)
  where
  bindings (CoreTermRuntimePattern _ (RuntimePatternVariable x _)) = Set.singleton x
  bindings (CoreTermRuntimePattern _ pm) = foldTermRuntimePatternF mempty go pm
    where
      go = bindings

instance Reduce (TermRuntimePattern InstantiationInfer KindInfer TypeInfer p) where
  reduce (CoreTermRuntimePattern p pm) = CoreTermRuntimePattern p $ mapTermRuntimePatternF go go pm
    where
      go = reduce

instance
  ( FreeVariables TermIdentifier σ
  ) =>
  FreeVariables TermIdentifier (Term θ κ σ p)
  where
  freeVariables (CoreTerm _ (TermRuntime (Variable x _))) = Set.singleton x
  freeVariables (CoreTerm _ e) = foldTermF go go mempty mempty mempty go go go e
    where
      go = freeVariables

instance
  ( Semigroup p,
    FreeVariablesPositioned TermIdentifier p σ
  ) =>
  FreeVariablesPositioned TermIdentifier p (Term θ κ σ p)
  where
  freeVariablesPositioned (CoreTerm p (TermRuntime (Variable x _))) = Variables $ Map.singleton x p
  freeVariablesPositioned (CoreTerm _ e) = foldTermF go go mempty mempty mempty go go go e
    where
      go = freeVariablesPositioned

instance
  ( Convert TermIdentifier σ,
    Convert TypeIdentifier θ
  ) =>
  Convert TermIdentifier (Term θ κ σ p)
  where
  convert ux x (CoreTerm p (TermRuntime (Variable x' θ))) | x == x' = CoreTerm p $ TermRuntime $ Variable ux θ
  convert ux x (CoreTerm p e) = CoreTerm p $ mapTermF go go id id id go go go e
    where
      go = convert ux x

instance
  ( Correct θ (Term θ κ σ p),
    Convert TermIdentifier σ,
    Convert TypeIdentifier σ,
    Convert TypeIdentifier θ,
    FreeVariables TypeIdentifier σ,
    FreeVariables TypeIdentifier θ,
    FreeVariables TermIdentifier σ
  ) =>
  Substitute (Term θ κ σ p) TermIdentifier (Term θ κ σ p)
  where
  substitute ux x (CoreTerm _ (TermRuntime (Variable x' θ))) | x == x' = correct θ ux
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTermF go go id id id go go go e
    where
      go = substitute ux x

instance
  ( FreeVariables TypeIdentifier σ,
    FreeVariables TypeIdentifier θ
  ) =>
  FreeVariables TypeIdentifier (Term θ κ σ p)
  where
  freeVariables (CoreTerm _ e) = foldTermF go go go mempty go go go go e
    where
      go = freeVariables

instance
  ( Convert TypeIdentifier θ,
    Convert TypeIdentifier σ'
  ) =>
  Convert TypeIdentifier (Term θ κ σ' p)
  where
  convert ux x (CoreTerm p e) = CoreTerm p $ mapTermF go go go id go go go go e
    where
      go = convert ux x

instance
  ( Substitute σ TypeIdentifier θ,
    Substitute σ TypeIdentifier σ',
    Convert TypeIdentifier σ',
    FreeVariables TypeIdentifier σ,
    Convert TypeIdentifier θ
  ) =>
  Substitute σ TypeIdentifier (Term θ κ σ' p)
  where
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTermF go go go id go go go go e
    where
      go = substitute ux x

instance Substitute TypeUnify TypeLogicalRaw (Term InstantiationUnify KindUnify TypeUnify p) where
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTermF go go go id go go go go e
    where
      go = substitute ux x

instance
  ( Convert KindIdentifier θ,
    Convert KindIdentifier σ,
    Convert KindIdentifier κ
  ) =>
  Convert KindIdentifier (Term θ κ σ p)
  where
  convert ux x (CoreTerm p e) = CoreTerm p $ mapTermF go go go go go go go go e
    where
      go = convert ux x

instance
  ( Substitute κ KindIdentifier σ,
    Substitute κ KindIdentifier θ,
    Substitute κ KindIdentifier κ'
  ) =>
  Substitute κ KindIdentifier (Term θ κ' σ p)
  where
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTermF go go go go go go go go e
    where
      go = substitute ux x

instance Substitute KindUnify KindLogicalRaw (Term InstantiationUnify KindUnify TypeUnify p) where
  substitute ux x (CoreTerm p e) = CoreTerm p $ mapTermF go go go go go go go go e
    where
      go = substitute ux x

instance Correct InstantiationInfer (Term InstantiationInfer KindInfer TypeInfer p) where
  correct (InstantiateEmpty) e = e
  correct (InstantiateType x σ θ) e = correct θ'' (substitute σ x e'')
    where
      Bound θ' e' = avoidCapture @TypeIdentifier σ (Bound θ e)
      Bound θ'' e'' = avoidCapture @KindIdentifier σ (Bound θ' e')
  correct (InstantiateKind x κ θ) e = correct θ' (substitute κ x e')
    where
      Bound θ' e' = avoidCapture @KindIdentifier κ (Bound θ e)

instance Reduce (Term InstantiationInfer KindInfer TypeInfer p) where
  reduce (CoreTerm _ (Bind e λ)) = apply (reduce λ) (reduce e)
  reduce (CoreTerm _ (MacroApplication e1 e2 _)) | (CoreTerm _ (MacroAbstraction λ)) <- reduce e1 = apply λ (reduce e2)
  reduce (CoreTerm _ (TypeApplication e1 σ _ _)) | (CoreTerm _ (TypeAbstraction (Bound pm e) _)) <- reduce e1 = apply (Bound pm e) σ
  reduce (CoreTerm p e) = CoreTerm p (mapTermF go go go go go go go go e)
    where
      go = reduce

instance
  Apply
    (Bound (TermPattern InstantiationInfer KindInfer TypeInfer p) (Term InstantiationInfer KindInfer TypeInfer p))
    (Term InstantiationInfer KindInfer TypeInfer p)
    (Term InstantiationInfer KindInfer TypeInfer p)
  where
  apply (Bound (CoreTermPattern _ (PatternVariable x _)) e) ux = reduce $ substitute ux x e
  apply (Bound (CoreTermPattern _ (PatternOfCourse pm)) e) (CoreTerm _ (OfCourseIntroduction ux)) = apply (Bound pm e) ux
  -- todo find better position here
  apply λ ux@(CoreTerm p _) = CoreTerm p $ Bind ux λ

instance
  Apply
    ( Bound
        (Pattern TypeIdentifier KindInfer p)
        (Term InstantiationInfer KindInfer TypeInfer p)
    )
    TypeInfer
    (Term InstantiationInfer KindInfer TypeInfer p)
  where
  apply (Bound (Pattern _ α _) e) σ = reduce $ substitute σ α e

instance
  ( FreeVariables TermIdentifier u,
    FreeVariables TermIdentifier σ
  ) =>
  FreeVariables TermIdentifier (Bound (TermPattern θ κ σ p) u)
  where
  freeVariables = freeVariablesBoundDependent

instance
  ( FreeVariablesPositioned TermIdentifier p u,
    Semigroup p,
    FreeVariablesPositioned TermIdentifier p σ
  ) =>
  FreeVariablesPositioned TermIdentifier p (Bound (TermPattern θ κ σ p) u)
  where
  freeVariablesPositioned = freeVariablesBoundDependentPositioned

instance
  ( Convert TermIdentifier u,
    Convert TypeIdentifier θ,
    Convert TermIdentifier σ
  ) =>
  Convert TermIdentifier (Bound (TermPattern θ κ σ p) u)
  where
  convert = substituteDependent convert convert (avoidCaptureConvert @TermIdentifier)

instance
  ( Substitute (Term θ κ σ p) TermIdentifier u,
    Correct θ (Term θ κ σ p),
    Convert TermIdentifier u,
    Convert TermIdentifier σ,
    Convert TypeIdentifier σ,
    Convert TypeIdentifier θ,
    FreeVariables TermIdentifier σ
  ) =>
  Substitute (Term θ κ σ p) TermIdentifier (Bound (TermPattern θ κ σ p) u)
  where
  substitute = substituteDependent substitute substitute (avoidCapture @TermIdentifier)

instance
  ( FreeVariables TypeIdentifier u,
    FreeVariables TypeIdentifier σ,
    FreeVariables TypeIdentifier θ
  ) =>
  FreeVariables TypeIdentifier (Bound (TermPattern θ κ σ p) u)
  where
  freeVariables (Bound pm e) = freeVariables pm <> freeVariables e

instance
  ( Convert TypeIdentifier u,
    Convert TypeIdentifier θ,
    Convert TypeIdentifier σ
  ) =>
  Convert TypeIdentifier (Bound (TermPattern θ κ σ p) u)
  where
  convert = substituteHigher convert convert

instance
  ( Substitute σ TypeIdentifier σ',
    Substitute σ TypeIdentifier u,
    Substitute σ TypeIdentifier θ,
    FreeVariables TypeIdentifier σ,
    Convert TypeIdentifier σ',
    Convert TypeIdentifier θ
  ) =>
  Substitute σ TypeIdentifier (Bound (TermPattern θ κ' σ' p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  ( Convert KindIdentifier u,
    Convert KindIdentifier θ,
    Convert KindIdentifier σ,
    Convert KindIdentifier κ
  ) =>
  Convert KindIdentifier (Bound (TermPattern θ κ σ p) u)
  where
  convert = substituteHigher convert convert

instance
  ( Substitute κ KindIdentifier u,
    Substitute κ KindIdentifier σ,
    Substitute κ KindIdentifier θ,
    Substitute κ KindIdentifier κ'
  ) =>
  Substitute κ KindIdentifier (Bound (TermPattern θ κ' σ p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  (Substitute TypeUnify TypeLogicalRaw u) =>
  Substitute TypeUnify TypeLogicalRaw (Bound (TermPattern InstantiationUnify KindUnify TypeUnify p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  (Substitute KindUnify KindLogicalRaw u) =>
  Substitute KindUnify KindLogicalRaw (Bound (TermPattern InstantiationUnify KindUnify TypeUnify p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  ( FreeVariables TermIdentifier u,
    FreeVariables TermIdentifier σ
  ) =>
  FreeVariables TermIdentifier (Bound (TermRuntimePattern θ κ σ p) u)
  where
  freeVariables = freeVariablesBoundDependent

instance
  ( FreeVariablesPositioned TermIdentifier p u,
    Semigroup p,
    FreeVariablesPositioned TermIdentifier p σ
  ) =>
  FreeVariablesPositioned TermIdentifier p (Bound (TermRuntimePattern θ κ σ p) u)
  where
  freeVariablesPositioned = freeVariablesBoundDependentPositioned

instance
  ( Convert TermIdentifier u,
    Convert TypeIdentifier θ,
    Convert TermIdentifier σ
  ) =>
  Convert TermIdentifier (Bound (TermRuntimePattern θ κ σ p) u)
  where
  convert = substituteDependent convert convert (avoidCaptureConvert @TermIdentifier)

instance
  ( Substitute (Term θ κ σ p) TermIdentifier u,
    Correct θ (Term θ κ σ p),
    Convert TermIdentifier u,
    Convert TermIdentifier σ,
    Convert TypeIdentifier σ,
    Convert TypeIdentifier θ,
    FreeVariables TermIdentifier σ
  ) =>
  Substitute (Term θ κ σ p) TermIdentifier (Bound (TermRuntimePattern θ κ σ p) u)
  where
  substitute = substituteDependent substitute substitute (avoidCapture @TermIdentifier)

instance
  ( FreeVariables TypeIdentifier u,
    FreeVariables TypeIdentifier σ,
    FreeVariables TypeIdentifier θ
  ) =>
  FreeVariables TypeIdentifier (Bound (TermRuntimePattern θ κ σ p) u)
  where
  freeVariables (Bound pm e) = freeVariables pm <> freeVariables e

instance
  ( Convert TypeIdentifier u,
    Convert TypeIdentifier θ,
    Convert TypeIdentifier σ
  ) =>
  Convert TypeIdentifier (Bound (TermRuntimePattern θ κ σ p) u)
  where
  convert = substituteHigher convert convert

instance
  ( Substitute σ TypeIdentifier σ',
    Substitute σ TypeIdentifier u,
    Substitute σ TypeIdentifier θ,
    FreeVariables TypeIdentifier σ,
    Convert TypeIdentifier σ',
    Convert TypeIdentifier θ
  ) =>
  Substitute σ TypeIdentifier (Bound (TermRuntimePattern θ κ' σ' p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  ( Convert KindIdentifier u,
    Convert KindIdentifier θ,
    Convert KindIdentifier σ,
    Convert KindIdentifier κ
  ) =>
  Convert KindIdentifier (Bound (TermRuntimePattern θ κ σ p) u)
  where
  convert = substituteHigher convert convert

instance
  ( Substitute κ KindIdentifier u,
    Substitute κ KindIdentifier σ,
    Substitute κ KindIdentifier θ,
    Substitute κ KindIdentifier κ'
  ) =>
  Substitute κ KindIdentifier (Bound (TermRuntimePattern θ κ' σ p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  ( Substitute TypeUnify TypeLogicalRaw u
  ) =>
  Substitute TypeUnify TypeLogicalRaw (Bound (TermRuntimePattern InstantiationUnify KindUnify TypeUnify p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  ( Substitute KindUnify KindLogicalRaw u
  ) =>
  Substitute KindUnify KindLogicalRaw (Bound (TermRuntimePattern InstantiationUnify KindUnify TypeUnify p) u)
  where
  substitute = substituteHigher substitute substitute

instance Location (Term θ κ σ) where
  location (CoreTerm p _) = p

instance Location (TermPattern θ κ σ) where
  location (CoreTermPattern p _) = p

instance Location (TermRuntimePattern θ κ σ) where
  location (CoreTermRuntimePattern p _) = p
