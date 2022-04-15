module Ast.Term where

import Ast.Common
import Ast.Kind
import Ast.Sort
import Ast.Type
import Control.Category (id, (.))
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void)
import Misc.Isomorph
import Misc.Prism
import Misc.Symbol
import qualified Misc.Util as Util
import Prelude hiding (id, (.))

newtype TermIdentifier = TermIdentifier {runTermIdentifier :: String} deriving (Show, Eq, Ord)

data TermPatternF σ pm
  = PatternVariable TermIdentifier σ
  | PatternOfCourse pm
  deriving (Show)

data TermRuntimePatternF σ pm
  = RuntimePatternVariable TermIdentifier σ
  | RuntimePatternPair pm pm
  deriving (Show)

data Arithmatic
  = Addition
  | Subtraction
  | Multiplication
  | Division
  deriving (Show, Eq)

data TermRuntime θ s σ' σ λ ev e
  = Variable TermIdentifier θ
  | Alias e (λ e)
  | Extern Symbol σ σ' σ
  | FunctionApplication e e σ
  | PairIntroduction e e
  | ReadReference e
  | NumberLiteral Integer
  | Arithmatic Arithmatic e e s
  deriving (Show)

data TermF λσ θ κ σ λ λr e
  = TermRuntime (TermRuntime θ κ σ σ λr e e)
  | FunctionLiteral (λr e)
  | InlineAbstraction (λ e)
  | InlineApplication e e σ
  | OfCourseIntroduction e
  | Bind e (λ e)
  | TypeAbstraction (λσ e) (Set Constraint) [σ]
  | TypeApplication e σ (λσ σ) (Set Constraint) [σ]
  deriving (Show)

data TermSchemeF λσ λ σ e eς
  = MonoTerm e
  | ImplicitTypeAbstraction (λ eς) (Set Constraint) [σ]
  | ImplicitKindAbstraction (λσ eς)
  deriving (Show)

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

traverseTermRuntime ::
  Applicative m =>
  (θ -> m θ') ->
  (s -> m s') ->
  (σ2 -> m σ2') ->
  (σ -> m σ') ->
  (λ e -> m (λ' e')) ->
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
  (λσ e -> m (λσ' e')) ->
  (λσ σ -> m (λσ' σ')) ->
  (θ -> m θ') ->
  (κ -> m κ') ->
  (σ -> m σ') ->
  (λ e -> m (λ' e')) ->
  (λr e -> m (λr' e')) ->
  (e -> m e') ->
  TermF λσ θ κ σ λ λr e ->
  m (TermF λσ' θ' κ' σ' λ' λr' e')
traverseTermF k l d j f h m i e =
  case e of
    TermRuntime e -> pure TermRuntime <*> traverseTermRuntime d j f f m i e
    FunctionLiteral λ -> pure FunctionLiteral <*> m λ
    InlineAbstraction λ -> pure InlineAbstraction <*> h λ
    InlineApplication e1 e2 σ -> pure InlineApplication <*> i e1 <*> i e2 <*> f σ
    OfCourseIntroduction e -> pure OfCourseIntroduction <*> i e
    Bind e λ -> pure Bind <*> i e <*> h λ
    TypeAbstraction λ c π -> pure TypeAbstraction <*> k λ <*> pure c <*> traverse f π
    TypeApplication e σ λ c π -> pure TypeApplication <*> i e <*> f σ <*> l λ <*> pure c <*> traverse f π

foldTermF l k d j f h m i = getConst . traverseTermF (Const . l) (Const . k) (Const . d) (Const . j) (Const . f) (Const . h) (Const . m) (Const . i)

mapTermF l k d j f h m i = runIdentity . traverseTermF (Identity . l) (Identity . k) (Identity . d) (Identity . j) (Identity . f) (Identity . h) (Identity . m) (Identity . i)

traverseTermSchemeF ::
  Applicative m =>
  (λσ eς -> m (λσ' eς')) ->
  (λ eς -> m (λ' eς')) ->
  (σ -> m σ') ->
  (e -> m e') ->
  TermSchemeF λσ λ σ e eς ->
  m (TermSchemeF λσ' λ' σ' e' eς')
traverseTermSchemeF f g h i e = case e of
  MonoTerm e -> pure MonoTerm <*> i e
  ImplicitTypeAbstraction λ c π -> pure ImplicitTypeAbstraction <*> g λ <*> pure c <*> traverse h π
  ImplicitKindAbstraction λ -> pure ImplicitKindAbstraction <*> f λ

mapTermSchemeF f g h i = runIdentity . traverseTermSchemeF (Identity . f) (Identity . g) (Identity . h) (Identity . i)

foldTermSchemeF f g h i = getConst . traverseTermSchemeF (Const . f) (Const . g) (Const . h) (Const . i)

data TermPatternSource p = TermPatternSource p (TermPatternF (TypeAuto p) (TermPatternSource p)) deriving (Show)

data TermPattern p vσ vκ = TermPatternCore p (TermPatternF (Type vσ vκ) (TermPattern p vσ vκ)) deriving (Show)

type TermPatternUnify p = TermPattern p TypeLogical KindLogical

type TermPatternInfer p = TermPattern p Void Void

data TermRuntimePatternSource p = TermRuntimePatternSource p (TermRuntimePatternF (TypeAuto p) (TermRuntimePatternSource p)) deriving (Show)

data TermRuntimePattern p vσ vκ = TermRuntimePatternCore p (TermRuntimePatternF (Type vσ vκ) (TermRuntimePattern p vσ vκ)) deriving (Show)

type TermRuntimePatternUnify p = TermRuntimePattern p TypeLogical KindLogical

type TermRuntimePatternInfer p = TermRuntimePattern p Void Void

data TermSource p
  = TermSource
      p
      ( TermF
          (Bound (Pattern TypeIdentifier (KindAuto p) p))
          ()
          (KindAuto p)
          (TypeAuto p)
          (Bound (TermPatternSource p))
          (Bound (TermRuntimePatternSource p))
          (TermSource p)
      )
  deriving (Show)

data Term p vσ vκ
  = TermCore
      p
      ( TermF
          (Bound (TypePattern vκ))
          (Instantiation vσ vκ)
          (Kind vκ)
          (Type vσ vκ)
          (Bound (TermPattern p vσ vκ))
          (Bound (TermRuntimePattern p vσ vκ))
          (Term p vσ vκ)
      )
  deriving (Show)

type TermUnify p = Term p TypeLogical KindLogical

type TermInfer p = Term p Void Void

data TermSchemeSource p
  = TermSchemeSource
      p
      ( TermSchemeF
          (Bound (Pattern KindIdentifier Sort p))
          (Bound (Pattern TypeIdentifier (KindAuto p) p))
          (TypeSource p)
          (TermSource p)
          (TermSchemeSource p)
      )

data TermScheme p vσ vκ
  = TermSchemeCore
      p
      ( TermSchemeF
          (Bound KindPattern)
          (Bound (TypePattern vκ))
          (Type vσ vκ)
          (Term p vσ vκ)
          (TermScheme p vσ vκ)
      )

type TermSchemeUnify p = TermScheme p TypeLogical KindLogical

type TermSchemeInfer p = TermScheme p Void Void

termPatternSource = Isomorph (uncurry $ TermPatternSource) $ \(TermPatternSource p pm) -> (p, pm)

termRuntimePatternSource = Isomorph (uncurry $ TermRuntimePatternSource) $ \(TermRuntimePatternSource p pm) -> (p, pm)

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

termSource = Isomorph (uncurry TermSource) $ \(TermSource p e) -> (p, e)

termRuntime = Prism TermRuntime $ \case
  (TermRuntime e) -> Just e
  _ -> Nothing

variable = (termRuntime .) $
  Prism (uncurry Variable) $ \case
    (Variable x θ) -> Just (x, θ)
    _ -> Nothing

inlineAbstraction = Prism (InlineAbstraction) $ \case
  (InlineAbstraction λ) -> Just λ
  _ -> Nothing

inlineApplication = Prism (uncurry $ uncurry $ InlineApplication) $ \case
  (InlineApplication e e' σ) -> Just ((e, e'), σ)
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

typeLambda = Prism (uncurry $ uncurry TypeAbstraction) $ \case
  TypeAbstraction pm c π -> Just ((pm, c), π)
  _ -> Nothing

typeApplication = Prism (uncurry $ uncurry $ uncurry $ uncurry TypeApplication) $ \case
  TypeApplication e σ λ c π -> Just ((((e, σ), λ), c), π)
  _ -> Nothing

termSchemeSource = Isomorph (uncurry TermSchemeSource) $ \(TermSchemeSource p e) -> (p, e)

monoTerm = Prism MonoTerm $ \case
  (MonoTerm σ) -> Just σ
  _ -> Nothing

implicitTypeLambda = Prism (uncurry $ uncurry ImplicitTypeAbstraction) $ \case
  (ImplicitTypeAbstraction λ c π) -> Just ((λ, c), π)
  _ -> Nothing

implicitKindLambda = Prism ImplicitKindAbstraction $ \case
  (ImplicitKindAbstraction λ) -> Just λ
  _ -> Nothing

termIdentifier = Isomorph TermIdentifier runTermIdentifier

class BindingsTerm pm where
  bindingsTerm :: pm -> Set TermIdentifier

class RenameTerm pm where
  renameTerm :: TermIdentifier -> TermIdentifier -> pm -> pm

class FreeVariablesTerm u where
  freeVariablesTerm :: u -> Set TermIdentifier

class FreeVariablesTermSource u where
  freeVariablesTermSource :: Semigroup p => u p -> Variables TermIdentifier p

class ConvertTerm u where
  convertTerm :: TermIdentifier -> TermIdentifier -> u -> u

class SubstituteTerm u where
  substituteTerm :: (TermScheme p vσ vκ) -> TermIdentifier -> u p vσ vκ -> u p vσ vκ

freeVariablesSameTerm = freeVariablesSame' freeVariablesTerm bindingsTerm

freeVariablesSameTermSource = freeVariablesSameSource' freeVariablesTermSource bindingsTerm

convertSameTerm = substituteSame' convertTerm avoidTermConvert

substituteSameTerm = substituteSame' substituteTerm avoidTerm

freeVariablesLowerTerm = freeVariablesLower' freeVariablesTerm

freeVariablesLowerTermSource = freeVariablesLower' freeVariablesTermSource

convertLowerTerm = convertLower' convertTerm

substituteLowerTerm avoid = substituteLower' substituteTerm avoid

avoidTerm = Avoid bindingsTerm renameTerm freeVariablesTerm convertTerm

avoidTermConvert = Avoid bindingsTerm renameTerm Set.singleton convertTerm

instance Fresh TermIdentifier where
  fresh c (TermIdentifier x) = TermIdentifier $ Util.fresh (Set.mapMonotonic runTermIdentifier c) x

instance Functor TermPatternSource where
  fmap f (TermPatternSource p pm) = TermPatternSource (f p) (mapTermPatternF (fmap (fmap f)) (fmap f) pm)

instance Functor TermRuntimePatternSource where
  fmap f (TermRuntimePatternSource p pm) = TermRuntimePatternSource (f p) (mapTermRuntimePatternF (fmap (fmap f)) (fmap f) pm)

instance Functor TermSource where
  fmap f (TermSource p e) =
    TermSource (f p) $
      mapTermF
        (mapBound (mapPattern id (fmap (fmap f)) f) (fmap f))
        (mapBound (mapPattern id (fmap (fmap f)) f) (fmap (fmap f)))
        id
        (fmap (fmap f))
        (fmap (fmap f))
        (mapBound (fmap f) (fmap f))
        (mapBound (fmap f) (fmap f))
        (fmap f)
        e

instance Functor TermSchemeSource where
  fmap f (TermSchemeSource p e) =
    TermSchemeSource
      (f p)
      ( mapTermSchemeF
          (mapBound (mapPattern id id f) (fmap f))
          (mapBound (mapPattern id (fmap $ fmap f) f) (fmap f))
          (fmap f)
          (fmap f)
          e
      )

instance BindingsTerm (TermPatternSource p) where
  bindingsTerm (TermPatternSource _ (PatternVariable x _)) = Set.singleton x
  bindingsTerm (TermPatternSource _ pm) = foldTermPatternF mempty go pm
    where
      go = bindingsTerm

instance BindingsTerm (TermRuntimePatternSource p) where
  bindingsTerm (TermRuntimePatternSource _ (RuntimePatternVariable x _)) = Set.singleton x
  bindingsTerm (TermRuntimePatternSource _ pm) = foldTermRuntimePatternF mempty go pm
    where
      go = bindingsTerm

instance BindingsTerm (TermPattern p vσ vκ) where
  bindingsTerm (TermPatternCore _ (PatternVariable x _)) = Set.singleton x
  bindingsTerm (TermPatternCore _ pm) = foldTermPatternF mempty go pm
    where
      go = bindingsTerm

instance BindingsTerm (TermRuntimePattern p vσ vκ) where
  bindingsTerm (TermRuntimePatternCore _ (RuntimePatternVariable x _)) = Set.singleton x
  bindingsTerm (TermRuntimePatternCore _ pm) = foldTermRuntimePatternF mempty go pm
    where
      go = bindingsTerm

instance RenameTerm (TermRuntimePattern p vσ vκ) where
  renameTerm ux x (TermRuntimePatternCore p (RuntimePatternVariable x' σ)) | x == x' = TermRuntimePatternCore p $ RuntimePatternVariable ux σ
  renameTerm ux x (TermRuntimePatternCore p pm) = TermRuntimePatternCore p $ mapTermRuntimePatternF id go pm
    where
      go = renameTerm ux x

instance RenameTerm (TermPattern p vσ vκ) where
  renameTerm ux x (TermPatternCore p (PatternVariable x' σ)) | x == x' = TermPatternCore p $ PatternVariable ux σ
  renameTerm ux x (TermPatternCore p pm) = TermPatternCore p $ mapTermPatternF id go pm
    where
      go = renameTerm ux x

instance ConvertType (TermSource p) where
  convertType ux x (TermSource p e) = TermSource p $ mapTermF go' go' id id go go'' go'' go e
    where
      go = convertType ux x
      go' = convertSameTypeSource ux x
      go'' = convertHigherType ux x

instance FreeVariablesType (TermPattern p vσ vκ) where
  freeVariablesType (TermPatternCore _ pm) = foldTermPatternF go go pm
    where
      go = freeVariablesType

instance SubstituteType (TermPattern p) where
  substituteType ux x (TermPatternCore p pm) = TermPatternCore p $ mapTermPatternF go go pm
    where
      go = substituteType ux x

instance ConvertKind (TermPattern p vσ vκ) where
  convertKind ux x (TermPatternCore p pm) = TermPatternCore p $ mapTermPatternF go go pm
    where
      go = convertKind ux x

instance ConvertType (TermPattern p vσ vκ) where
  convertType ux x (TermPatternCore p pm) = TermPatternCore p $ mapTermPatternF go go pm
    where
      go = convertType ux x

instance FreeVariablesKind (TermPattern p vσ vκ) where
  freeVariablesKind (TermPatternCore _ pm) = foldTermPatternF go go pm
    where
      go = freeVariablesKind

instance SubstituteKind (TermPattern p vσ) where
  substituteKind ux x (TermPatternCore p pm) = TermPatternCore p $ mapTermPatternF go go pm
    where
      go = substituteKind ux x

instance Reduce (TermPattern p vσ vκ) where
  reduce (TermPatternCore p pm) = TermPatternCore p $ mapTermPatternF go go pm
    where
      go = reduce

instance FreeVariablesType (TermRuntimePattern p vσ vκ) where
  freeVariablesType (TermRuntimePatternCore _ pm) = foldTermRuntimePatternF go go pm
    where
      go = freeVariablesType

instance ConvertType (TermPatternSource p) where
  convertType ux x (TermPatternSource p pm) = TermPatternSource p $ mapTermPatternF go go pm
    where
      go = convertType ux x

instance ConvertType (TermRuntimePatternSource p) where
  convertType ux x (TermRuntimePatternSource p pm) = TermRuntimePatternSource p $ mapTermRuntimePatternF go go pm
    where
      go = convertType ux x

instance ConvertType (TermRuntimePattern p vσ vκ) where
  convertType ux x (TermRuntimePatternCore p pm) = TermRuntimePatternCore p $ mapTermRuntimePatternF go go pm
    where
      go = convertType ux x

instance SubstituteType (TermRuntimePattern p) where
  substituteType ux x (TermRuntimePatternCore p pm) = TermRuntimePatternCore p $ mapTermRuntimePatternF go go pm
    where
      go = substituteType ux x

instance FreeVariablesKind (TermRuntimePattern p vσ vκ) where
  freeVariablesKind (TermRuntimePatternCore _ pm) = foldTermRuntimePatternF go go pm
    where
      go = freeVariablesKind

instance ConvertKind (TermRuntimePattern p vσ vκ) where
  convertKind ux x (TermRuntimePatternCore p pm) = TermRuntimePatternCore p $ mapTermRuntimePatternF go go pm
    where
      go = convertKind ux x

instance SubstituteKind (TermRuntimePattern p vσ) where
  substituteKind ux x (TermRuntimePatternCore p pm) = TermRuntimePatternCore p $ mapTermRuntimePatternF go go pm
    where
      go = substituteKind ux x

instance Reduce (TermRuntimePattern p vσ vκ) where
  reduce (TermRuntimePatternCore p pm) = TermRuntimePatternCore p $ mapTermRuntimePatternF go go pm
    where
      go = reduce

instance FreeVariablesTerm (Term p vσ vκ) where
  freeVariablesTerm (TermCore _ (TermRuntime (Variable x _))) = Set.singleton x
  freeVariablesTerm (TermCore _ e) = foldTermF go' mempty mempty mempty mempty go'' go'' go e
    where
      go = freeVariablesTerm
      go' = freeVariablesLowerTerm
      go'' = freeVariablesSameTerm

instance FreeVariablesTermSource TermSource where
  freeVariablesTermSource (TermSource p (TermRuntime (Variable x _))) = Variables $ Map.singleton x p
  freeVariablesTermSource (TermSource _ e) = foldTermF go' mempty mempty mempty mempty go'' go'' go e
    where
      go = freeVariablesTermSource
      go' = freeVariablesLowerTermSource
      go'' = freeVariablesSameTermSource

instance ConvertTerm (Term p vσ vκ) where
  convertTerm ux x (TermCore p (TermRuntime (Variable x' θ))) | x == x' = TermCore p $ TermRuntime $ Variable ux θ
  convertTerm ux x (TermCore p e) = TermCore p $ mapTermF go' id id id id go'' go'' go e
    where
      go = convertTerm ux x
      go' = convertLowerTerm ux x
      go'' = convertSameTerm ux x

instance SubstituteTerm Term where
  substituteTerm ux x v@(TermCore _ (TermRuntime (Variable x' θ))) | x == x' = go ux θ
    where
      go (TermSchemeCore _ (ImplicitTypeAbstraction λ _ _)) (InstantiationCore (InstantiateType σ θ)) = go (apply λ σ) θ
        where
          apply (Bound (TypePatternCore α _) e) σ = substituteType σ α e
      go (TermSchemeCore _ (ImplicitKindAbstraction λ)) (InstantiationCore (InstantiateKind κ θ)) = go (apply λ κ) θ
        where
          apply (Bound (KindPatternCore α _) e) κ = substituteKind κ α e
      go (TermSchemeCore _ (MonoTerm e)) (InstantiationCore InstantiateEmpty) = e
      go _ _ = flip const (ux, v) $ error "unable to substitute"
  substituteTerm ux x (TermCore p e) = TermCore p $ mapTermF go' id id id id go'' go'' go e
    where
      go = substituteTerm ux x
      go' = substituteLowerTerm avoidType ux x
      go'' = substituteSameTerm ux x

instance FreeVariablesType (Term p vσ vκ) where
  freeVariablesType (TermCore _ e) = foldTermF go' go' go mempty go go'' go'' go e
    where
      go = freeVariablesType
      go' = freeVariablesSameType
      go'' = freeVariablesHigherType

instance ConvertType (Term p vσ vκ) where
  convertType ux x (TermCore p e) = TermCore p $ mapTermF go' go' go id go go'' go'' go e
    where
      go = convertType ux x
      go' = convertSameType ux x
      go'' = convertHigherType ux x

instance SubstituteType (Term p) where
  substituteType ux x (TermCore p e) = TermCore p $ mapTermF go' go' go id go go'' go'' go e
    where
      go = substituteType ux x
      go' = substituteSameType ux x
      go'' = substituteHigherType ux x

instance FreeVariablesKind (Term p vσ vκ) where
  freeVariablesKind (TermCore _ e) = foldTermF go' go' go go go go' go' go e
    where
      go = freeVariablesKind
      go' = freeVariablesHigherKind

instance ConvertKind (Term p vσ vκ) where
  convertKind ux x (TermCore p e) = TermCore p $ mapTermF go' go' go go go go' go' go e
    where
      go = convertKind ux x
      go' = convertHigherKind ux x

instance SubstituteKind (Term p vσ) where
  substituteKind ux x (TermCore p e) = TermCore p $ mapTermF go' go' go go go go' go' go e
    where
      go = substituteKind ux x
      go' = substituteHigherKind ux x

instance FreeVariablesTerm (TermScheme p vσ vκ) where
  freeVariablesTerm (TermSchemeCore _ e) = foldTermSchemeF go' go' mempty go e
    where
      go = freeVariablesTerm
      go' = freeVariablesLowerTerm

instance FreeVariablesTermSource TermSchemeSource where
  freeVariablesTermSource (TermSchemeSource _ e) = foldTermSchemeF go' go' mempty go e
    where
      go = freeVariablesTermSource
      go' = freeVariablesLowerTermSource

instance SubstituteTerm TermScheme where
  substituteTerm ux x (TermSchemeCore p e) = TermSchemeCore p $ mapTermSchemeF go'' go' id go e
    where
      go = substituteTerm ux x
      go' = substituteLowerTerm avoidType ux x
      go'' = substituteLowerTerm avoidKind ux x

instance FreeVariablesType (TermScheme p vσ vκ) where
  freeVariablesType (TermSchemeCore _ e) = foldTermSchemeF go'' go' go go e
    where
      go = freeVariablesType
      go' = freeVariablesSameType
      go'' = freeVariablesLowerType

instance ConvertType (TermScheme p vσ vκ) where
  convertType ux x (TermSchemeCore p e) = TermSchemeCore p $ mapTermSchemeF go'' go' go go e
    where
      go = convertType ux x
      go' = convertSameType ux x
      go'' = convertLowerType ux x

instance SubstituteType (TermScheme p) where
  substituteType ux x (TermSchemeCore p e) = TermSchemeCore p $ mapTermSchemeF go'' go' go go e
    where
      go = substituteType ux x
      go' = substituteSameType ux x
      go'' = substituteLowerType avoidKind ux x

instance FreeVariablesKind (TermScheme p vσ vκ) where
  freeVariablesKind (TermSchemeCore _ e) = foldTermSchemeF go'' go' go go e
    where
      go = freeVariablesKind
      go' = freeVariablesHigherKind
      go'' = freeVariablesSameKind

instance ConvertKind (TermScheme p vσ vκ) where
  convertKind ux x (TermSchemeCore p e) = TermSchemeCore p $ mapTermSchemeF go'' go' go go e
    where
      go = convertKind ux x
      go' = convertHigherKind ux x
      go'' = convertSameKind ux x

instance SubstituteKind (TermScheme p vσ) where
  substituteKind ux x (TermSchemeCore p e) = TermSchemeCore p $ mapTermSchemeF go'' go' go go e
    where
      go = substituteKind ux x
      go' = substituteHigherKind ux x
      go'' = substituteSameKind ux x

applyTerm (Bound (TermPatternCore _ (PatternVariable x _)) e@(TermCore p _)) ux =
  reduce $ substituteTerm (TermSchemeCore p (MonoTerm ux)) x e
applyTerm (Bound (TermPatternCore _ (PatternOfCourse pm)) e) (TermCore _ (OfCourseIntroduction ux)) = applyTerm (Bound pm e) ux
-- todo find better position here
applyTerm λ ux@(TermCore p _) = TermCore p $ Bind ux λ

instance Reduce (Term p vσ vκ) where
  reduce (TermCore _ (Bind e λ)) = applyTerm (reduce λ) (reduce e)
  reduce (TermCore _ (InlineApplication e1 e2 _)) | (TermCore _ (InlineAbstraction λ)) <- reduce e1 = applyTerm λ (reduce e2)
  reduce (TermCore _ (TypeApplication e1 σ _ _ _)) | (TermCore _ (TypeAbstraction (Bound pm e) _ _)) <- reduce e1 = applyType (Bound pm e) σ
    where
      applyType (Bound (TypePatternCore α _) e) σ = reduce $ substituteType σ α e
  reduce (TermCore p e) = TermCore p (mapTermF go go go go go go go go e)
    where
      go = reduce

instance ZonkType (TermScheme p) where
  zonkType f (TermSchemeCore p e) =
    pure TermSchemeCore <*> pure p
      <*> traverseTermSchemeF
        (traverseBound pure (zonkType f))
        (traverseBound pure (zonkType f))
        (zonkType f)
        (zonkType f)
        e

instance ZonkType (Term p) where
  zonkType f (TermCore p e) =
    pure TermCore <*> pure p
      <*> traverseTermF
        (traverseBound pure (zonkType f))
        (traverseBound pure (zonkType f))
        (zonkType f)
        pure
        (zonkType f)
        (traverseBound (zonkType f) (zonkType f))
        (traverseBound (zonkType f) (zonkType f))
        (zonkType f)
        e

instance ZonkType (TermPattern p) where
  zonkType f (TermPatternCore p pm) =
    pure TermPatternCore <*> pure p
      <*> traverseTermPatternF (zonkType f) (zonkType f) pm

instance ZonkType (TermRuntimePattern p) where
  zonkType f (TermRuntimePatternCore p pm) =
    pure TermRuntimePatternCore <*> pure p
      <*> traverseTermRuntimePatternF (zonkType f) (zonkType f) pm

instance ZonkKind (TermScheme p vσ) where
  zonkKind f (TermSchemeCore p e) =
    pure TermSchemeCore <*> pure p
      <*> traverseTermSchemeF
        (traverseBound pure (zonkKind f))
        (traverseBound (zonkKind f) (zonkKind f))
        (zonkKind f)
        (zonkKind f)
        e

instance ZonkKind (Term p vσ) where
  zonkKind f (TermCore p e) =
    pure TermCore <*> pure p
      <*> traverseTermF
        (traverseBound (zonkKind f) (zonkKind f))
        (traverseBound (zonkKind f) (zonkKind f))
        (zonkKind f)
        (zonkKind f)
        (zonkKind f)
        (traverseBound (zonkKind f) (zonkKind f))
        (traverseBound (zonkKind f) (zonkKind f))
        (zonkKind f)
        e

instance ZonkKind (TermPattern p vσ) where
  zonkKind f (TermPatternCore p pm) =
    pure TermPatternCore <*> pure p
      <*> traverseTermPatternF (zonkKind f) (zonkKind f) pm

instance ZonkKind (TermRuntimePattern p vσ) where
  zonkKind f (TermRuntimePatternCore p pm) =
    pure TermRuntimePatternCore <*> pure p
      <*> traverseTermRuntimePatternF (zonkKind f) (zonkKind f) pm

instance Reduce (TermScheme p vσ vκ) where
  reduce (TermSchemeCore p e) = TermSchemeCore p $ mapTermSchemeF go go go go e
    where
      go = reduce

instance Location TermSource where
  location (TermSource p _) = p

instance Location TermPatternSource where
  location (TermPatternSource p _) = p

instance Location TermRuntimePatternSource where
  location (TermRuntimePatternSource p _) = p

sourceTermScheme :: Monoid p' => TermScheme p Void Void -> TermSchemeSource p'
sourceTermScheme (TermSchemeCore _ e) =
  TermSchemeSource mempty $
    mapTermSchemeF
      (mapBound sourceKindPattern sourceTermScheme)
      (mapBound sourceTypePattern sourceTermScheme)
      sourceType
      sourceTerm
      e

sourceTerm :: Monoid p' => Term p Void Void -> TermSource p'
sourceTerm (TermCore _ e) =
  TermSource mempty $
    mapTermF
      (mapBound sourceTypePattern sourceTerm)
      (mapBound sourceTypePattern sourceTypeAuto)
      (const ())
      sourceKindAuto
      sourceTypeAuto
      (mapBound sourceTermPattern sourceTerm)
      (mapBound sourceTermRuntimePattern sourceTerm)
      sourceTerm
      e

sourceTermPattern :: Monoid p' => TermPattern p Void Void -> TermPatternSource p'
sourceTermPattern (TermPatternCore _ pm) =
  TermPatternSource mempty $
    mapTermPatternF sourceTypeAuto sourceTermPattern pm

sourceTermRuntimePattern :: Monoid p' => TermRuntimePattern p Void Void -> TermRuntimePatternSource p'
sourceTermRuntimePattern (TermRuntimePatternCore _ pm) =
  TermRuntimePatternSource mempty $
    mapTermRuntimePatternF sourceTypeAuto sourceTermRuntimePattern pm
