module Ast.Term where

import Ast.Common
import Ast.Type
import Control.Category (id, (.))
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
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
  | RuntimePatternTuple [pm]
  deriving (Show)

data Arithmatic
  = Addition
  | Subtraction
  | Multiplication
  | Division
  deriving (Show, Eq)

data Relational
  = Equal
  | NotEqual
  | LessThen
  | LessThenEqual
  | GreaterThen
  | GreaterThenEqual
  deriving (Show, Eq)

data TermRuntime θ σerase s σ λe e
  = Variable TermIdentifier θ
  | Alias e λe
  | Extern Symbol σ σerase σ
  | FunctionApplication e e σ
  | TupleIntroduction [e]
  | ReadReference e
  | WriteReference e e σ
  | NumberLiteral Integer
  | Arithmatic Arithmatic e e s
  | Relational Relational e e σ s
  | BooleanLiteral Bool
  | If e e e
  | PointerIncrement e e σ
  deriving (Show)

data TermSugar e
  = Not e
  | And e e
  | Or e e
  | Do e e
  deriving (Show)

data TermF sourceOnly θ σauto σ λrgn_e λσe λe λrun_e e
  = TermRuntime (TermRuntime θ σauto σauto σauto λrun_e e)
  | TermSugar (TermSugar e) sourceOnly
  | FunctionLiteral λrun_e
  | Borrow e λrgn_e
  | InlineAbstraction λe
  | InlineApplication e e σauto
  | OfCourseIntroduction e
  | Bind e λe
  | PolyIntroduction λσe
  | PolyElimination e θ σauto
  | TypeAnnotation e σ sourceOnly
  | PretypeAnnotation e σ sourceOnly
  deriving (Show)

data TermSchemeF λκe λσe e
  = MonoTerm e
  | TypeAbstraction λσe
  | KindAbstraction λκe
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
  RuntimePatternTuple pms -> pure RuntimePatternTuple <*> traverse h pms

foldTermRuntimePatternF f h = getConst . traverseTermRuntimePatternF (Const . f) (Const . h)

mapTermRuntimePatternF f h = runIdentity . traverseTermRuntimePatternF (Identity . f) (Identity . h)

traverseTermRuntime ::
  Applicative m =>
  (θ -> m θ') ->
  (σerase -> m σerase') ->
  (s -> m s') ->
  (σ -> m σ') ->
  (λe -> m λe') ->
  (e -> m e') ->
  TermRuntime θ σerase s σ λe e ->
  m (TermRuntime θ' σerase' s' σ' λe' e')
traverseTermRuntime d y h f g i e =
  case e of
    Variable x θ -> pure Variable <*> pure x <*> d θ
    Alias e λ -> pure Alias <*> i e <*> g λ
    Extern sm σ σ'' σ' -> pure Extern <*> pure sm <*> f σ <*> y σ'' <*> f σ'
    FunctionApplication e1 e2 σ -> pure FunctionApplication <*> i e1 <*> i e2 <*> f σ
    TupleIntroduction es -> pure TupleIntroduction <*> traverse i es
    ReadReference e -> pure ReadReference <*> i e
    WriteReference e e' σ -> pure WriteReference <*> i e <*> i e' <*> f σ
    NumberLiteral n -> pure NumberLiteral <*> pure n
    Arithmatic o e e' κ -> pure Arithmatic <*> pure o <*> i e <*> i e' <*> h κ
    Relational o e e' σ κ -> pure Relational <*> pure o <*> i e <*> i e' <*> f σ <*> h κ
    BooleanLiteral b -> pure BooleanLiteral <*> pure b
    If e e' e'' -> pure If <*> i e <*> i e' <*> i e''
    PointerIncrement e e' σ -> pure PointerIncrement <*> i e <*> i e' <*> f σ

traverseTermSugar ::
  Applicative m =>
  (e -> m e') ->
  TermSugar e ->
  m (TermSugar e')
traverseTermSugar f e = case e of
  Not e -> pure Not <*> f e
  And e e' -> pure And <*> f e <*> f e'
  Or e e' -> pure Or <*> f e <*> f e'
  Do e e' -> pure Do <*> f e <*> f e'

traverseTermF ::
  Applicative m =>
  (source -> m source') ->
  (θ -> m θ') ->
  (σauto -> m σauto') ->
  (σ -> m σ') ->
  (λrgn_e -> m λrgn_e') ->
  (λσe -> m λσe') ->
  (λe -> m λe') ->
  (λrun_e -> m λrun_e') ->
  (e -> m e') ->
  TermF source θ σauto σ λrgn_e λσe λe λrun_e e ->
  m (TermF source' θ' σauto' σ' λrgn_e' λσe' λe' λrun_e' e')
traverseTermF y d z f r k h m i e =
  case e of
    TermRuntime e -> pure TermRuntime <*> traverseTermRuntime d z z z m i e
    TermSugar e source -> pure TermSugar <*> traverseTermSugar i e <*> y source
    FunctionLiteral λ -> pure FunctionLiteral <*> m λ
    Borrow e λ -> pure Borrow <*> i e <*> r λ
    InlineAbstraction λ -> pure InlineAbstraction <*> h λ
    InlineApplication e1 e2 σ -> pure InlineApplication <*> i e1 <*> i e2 <*> z σ
    OfCourseIntroduction e -> pure OfCourseIntroduction <*> i e
    Bind e λ -> pure Bind <*> i e <*> h λ
    PolyIntroduction λ -> pure PolyIntroduction <*> k λ
    PolyElimination e θ σ2 -> pure PolyElimination <*> i e <*> d θ <*> z σ2
    TypeAnnotation e σ source -> pure TypeAnnotation <*> i e <*> f σ <*> y source
    PretypeAnnotation e σ source -> pure PretypeAnnotation <*> i e <*> f σ <*> y source

foldTermF y d j z f r h m i = getConst . traverseTermF (Const . y) (Const . d) (Const . j) (Const . z) (Const . f) (Const . r) (Const . h) (Const . m) (Const . i)

mapTermF y d j z f r h m i = runIdentity . traverseTermF (Identity . y) (Identity . d) (Identity . j) (Identity . z) (Identity . f) (Identity . r) (Identity . h) (Identity . m) (Identity . i)

traverseTermSchemeF ::
  Applicative m =>
  (λκe -> m λκe') ->
  (λσe -> m λσe') ->
  (e -> m e') ->
  TermSchemeF λκe λσe e ->
  m (TermSchemeF λκe' λσe' e')
traverseTermSchemeF f g i e = case e of
  MonoTerm e -> pure MonoTerm <*> i e
  TypeAbstraction λ -> pure TypeAbstraction <*> g λ
  KindAbstraction λ -> pure KindAbstraction <*> f λ

mapTermSchemeF g h i = runIdentity . traverseTermSchemeF (Identity . g) (Identity . h) (Identity . i)

foldTermSchemeF g h i = getConst . traverseTermSchemeF (Const . g) (Const . h) (Const . i)

data TermPatternSource p = TermPatternSource p (TermPatternF (TypeAuto p) (TermPatternSource p)) deriving (Show)

data TermPattern p v = TermPatternCore p (TermPatternF (Type v) (TermPattern p v)) deriving (Show)

type TermPatternUnify p = TermPattern p TypeLogical

type TermPatternInfer p = TermPattern p Void

data TermRuntimePatternSource p = TermRuntimePatternSource p (TermRuntimePatternF (TypeAuto p) (TermRuntimePatternSource p)) deriving (Show)

data TermRuntimePattern p v = TermRuntimePatternCore p (TermRuntimePatternF (Type v) (TermRuntimePattern p v)) deriving (Show)

type TermRuntimePatternUnify p = TermRuntimePattern p TypeLogical

type TermRuntimePatternInfer p = TermRuntimePattern p Void

data TermSource p
  = TermSource
      p
      ( TermF
          ()
          ()
          ()
          (TypeAuto p)
          (Bound (TypePatternSource p) (Bound (TermRuntimePatternSource p) (TermSource p)))
          (TermSchemeSource p)
          (Bound (TermPatternSource p) (TermSource p))
          (Bound (TermRuntimePatternSource p) (TermSource p))
          (TermSource p)
      )
  deriving (Show)

data Term p v
  = TermCore
      p
      ( TermF
          Void
          (Instantiation v)
          (Type v)
          (Type v)
          (Bound (TypePattern v) (Bound (TermRuntimePattern p v) (Term p v)))
          (TermScheme p v)
          (Bound (TermPattern p v) (Term p v))
          (Bound (TermRuntimePattern p v) (Term p v))
          (Term p v)
      )
  deriving (Show)

type TermUnify p = Term p TypeLogical

type TermInfer p = Term p Void

data TermSchemeSource p
  = TermSchemeSource
      p
      ( TermSchemeF
          (Bound (KindPatternSource p) (TermSchemeSource p))
          (Bound (TypePatternSource p) (TermSchemeSource p))
          (TermSource p)
      )
  deriving (Show)

data TermScheme p v
  = TermSchemeCore
      p
      ( TermSchemeF
          (Bound (KindPattern v) (TermScheme p v))
          (Bound (TypePattern v) (TermScheme p v))
          (Term p v)
      )
  deriving (Show)

type TermSchemeUnify p = TermScheme p TypeLogical

type TermSchemeInfer p = TermScheme p Void

data TermControlSource p
  = TermAutoSource (TermSource p)
  | TermManualSource (TermSchemeSource p)
  deriving (Show, Functor)

desugar p (Not e) =
  TermCore
    p
    ( TermRuntime $
        If
          e
          (TermCore p $ TermRuntime $ BooleanLiteral False)
          (TermCore p $ TermRuntime $ BooleanLiteral True)
    )
desugar p (And e e') =
  TermCore
    p
    ( TermRuntime $
        If
          e
          e'
          (TermCore p $ TermRuntime $ BooleanLiteral False)
    )
desugar p (Or e e') =
  TermCore
    p
    ( TermRuntime $
        If
          e
          (TermCore p $ TermRuntime $ BooleanLiteral True)
          e'
    )
desugar p (Do e e') =
  TermCore
    p
    ( TermRuntime $
        Alias e (Bound (TermRuntimePatternCore p $ RuntimePatternTuple []) e')
    )

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

-- n-arity tuples are supported internally but only pairs are supposed in the surface language
runtimePatternPair =
  Prism (\(pm, pm') -> RuntimePatternTuple [pm, pm']) $ \case
    (RuntimePatternTuple [pm, pm']) -> Just (pm, pm')
    _ -> Nothing

runtimePatternUnit =
  Prism (const $ RuntimePatternTuple []) $ \case
    (RuntimePatternTuple []) -> Just ()
    _ -> Nothing

termSource = Isomorph (uncurry TermSource) $ \(TermSource p e) -> (p, e)

termRuntime = Prism TermRuntime $ \case
  (TermRuntime e) -> Just e
  _ -> Nothing

termSugar = Prism (\e -> TermSugar e ()) $ \case
  (TermSugar e ()) -> Just e
  _ -> Nothing

variable = (termRuntime .) $
  Prism (uncurry Variable) $ \case
    (Variable x θ) -> Just (x, θ)
    _ -> Nothing

inlineAbstraction = Prism (InlineAbstraction) $ \case
  (InlineAbstraction λ) -> Just λ
  _ -> Nothing

inlineApplication = Prism (\(e, e') -> InlineApplication e e' ()) $ \case
  (InlineApplication e e' ()) -> Just (e, e')
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
  Prism (\sym -> Extern sym () () ()) $ \case
    (Extern sym () () ()) -> Just sym
    _ -> Nothing

functionApplication = (termRuntime .) $
  Prism (\(e, e') -> FunctionApplication e e' ()) $ \case
    (FunctionApplication e e' ()) -> Just (e, e')
    _ -> Nothing

functionLiteral =
  Prism (FunctionLiteral) $ \case
    (FunctionLiteral λ) -> Just λ
    _ -> Nothing

-- n-arity tuples are supported internally but only pairs are supposed in the surface language
pairIntroduction = (termRuntime .) $
  Prism (\(e1, e2) -> TupleIntroduction [e1, e2]) $ \case
    (TupleIntroduction [e1, e2]) -> Just (e1, e2)
    _ -> Nothing

unitIntroduction = (termRuntime .) $
  Prism (const $ TupleIntroduction []) $ \case
    (TupleIntroduction []) -> Just ()
    _ -> Nothing

readReference = (termRuntime .) $
  Prism (ReadReference) $ \case
    (ReadReference e) -> Just (e)
    _ -> Nothing

writeReference = (termRuntime .) $
  Prism (\(e, e') -> WriteReference e e' ()) $ \case
    (WriteReference e e' ()) -> Just (e, e')
    _ -> Nothing

numberLiteral = (termRuntime .) $
  Prism (NumberLiteral) $ \case
    (NumberLiteral n) -> Just n
    _ -> Nothing

truex = (termRuntime .) $
  Prism (const $ BooleanLiteral True) $ \case
    BooleanLiteral True -> Just ()
    _ -> Nothing

falsex = (termRuntime .) $
  Prism (const $ BooleanLiteral False) $ \case
    BooleanLiteral False -> Just ()
    _ -> Nothing

ifx = (termRuntime .) $
  Prism (uncurry $ uncurry $ If) $ \case
    If eb et ef -> Just ((eb, et), ef)
    _ -> Nothing

arithmatic o = (termRuntime .) $
  Prism (\(e, e') -> Arithmatic o e e' ()) $ \case
    Arithmatic o' e e' () | o == o' -> Just (e, e')
    _ -> Nothing

relational o = (termRuntime .) $
  Prism (\(e, e') -> Relational o e e' () ()) $ \case
    Relational o' e e' () () | o == o' -> Just (e, e')
    _ -> Nothing

pointerIncrement = (termRuntime .) $
  Prism (\(e, e') -> PointerIncrement e e' ()) $ \case
    PointerIncrement e e' () -> Just (e, e')
    _ -> Nothing

not = (termSugar .) $
  Prism Not $ \case
    Not e -> Just e
    _ -> Nothing

and = (termSugar .) $
  Prism (uncurry And) $ \case
    And e e' -> Just (e, e')
    _ -> Nothing

or = (termSugar .) $
  Prism (uncurry Or) $ \case
    Or e e' -> Just (e, e')
    _ -> Nothing

dox = (termSugar .) $
  Prism (uncurry Do) $ \case
    Do e e' -> Just (e, e')
    _ -> Nothing

polyIntroduction = Prism PolyIntroduction $ \case
  PolyIntroduction λ -> Just λ
  _ -> Nothing

polyElimination = Prism (\e -> PolyElimination e () ()) $ \case
  PolyElimination e () () -> Just e
  _ -> Nothing

termSchemeSource = Isomorph (uncurry TermSchemeSource) $ \(TermSchemeSource p e) -> (p, e)

monoTerm = Prism MonoTerm $ \case
  (MonoTerm σ) -> Just σ
  _ -> Nothing

typeAbstraction = Prism TypeAbstraction $ \case
  (TypeAbstraction λ) -> Just λ
  _ -> Nothing

kindAbstraction = Prism KindAbstraction $ \case
  (KindAbstraction λ) -> Just λ
  _ -> Nothing

typeAnnotation = Prism (\(e, σ) -> TypeAnnotation e σ ()) $ \case
  (TypeAnnotation e σ ()) -> Just (e, σ)
  _ -> Nothing

preTypeAnnotation = Prism (\(e, σ) -> PretypeAnnotation e σ ()) $ \case
  (PretypeAnnotation e σ ()) -> Just (e, σ)
  _ -> Nothing

borrow = Prism (uncurry Borrow) $ \case
  (Borrow e λ) -> Just (e, λ)
  _ -> Nothing

termAutoSource = Prism TermAutoSource $ \case
  TermAutoSource e -> Just e
  _ -> Nothing

termManualSource = Prism TermManualSource $ \case
  TermManualSource e -> Just e
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
  substituteTerm :: (TermScheme p v) -> TermIdentifier -> u p v -> u p v

freeVariablesSameTerm = freeVariablesSame bindingsTerm freeVariablesTerm

freeVariablesSameTermSource = freeVariablesSameSource bindingsTerm freeVariablesTermSource

convertSameTerm = substituteSame avoidTermConvert convertTerm

substituteSameTerm = substituteSame avoidTerm substituteTerm

freeVariablesLowerTerm = freeVariablesLower freeVariablesTerm

freeVariablesLowerTermSource = freeVariablesLower freeVariablesTermSource

convertLowerTerm = convertLower convertTerm

substituteLowerTerm avoid = substituteLower avoid substituteTerm

freeVariablesRgnForTerm = freeVariablesLower freeVariablesSameTerm

freeVariablesRgnSourceForTerm = freeVariablesLower freeVariablesSameTermSource

convertRgnForTerm = convertLower convertSameTerm

substituteRgnForTerm = substituteLower (avoidType' convertHigherType) substituteSameTerm

avoidTerm = avoidTerm' convertTerm

avoidTerm' = Avoid bindingsTerm renameTerm freeVariablesTerm

avoidTermConvert = avoidTermConvert' convertTerm

avoidTermConvert' = Avoid bindingsTerm renameTerm Set.singleton

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
        id
        id
        id
        (fmap (fmap f))
        (mapBound (fmap f) (mapBound (fmap f) (fmap f)))
        (fmap f)
        (mapBound (fmap f) (fmap f))
        (mapBound (fmap f) (fmap f))
        (fmap f)
        e

instance Functor TermSchemeSource where
  fmap f (TermSchemeSource p e) =
    TermSchemeSource
      (f p)
      ( mapTermSchemeF
          (mapBound (fmap f) (fmap f))
          (mapBound (fmap f) (fmap f))
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

instance BindingsTerm (TermPattern p v) where
  bindingsTerm (TermPatternCore _ (PatternVariable x _)) = Set.singleton x
  bindingsTerm (TermPatternCore _ pm) = foldTermPatternF mempty go pm
    where
      go = bindingsTerm

instance BindingsTerm (TermRuntimePattern p v) where
  bindingsTerm (TermRuntimePatternCore _ (RuntimePatternVariable x _)) = Set.singleton x
  bindingsTerm (TermRuntimePatternCore _ pm) = foldTermRuntimePatternF mempty go pm
    where
      go = bindingsTerm

instance RenameTerm (TermRuntimePattern p v) where
  renameTerm ux x (TermRuntimePatternCore p (RuntimePatternVariable x' σ)) | x == x' = TermRuntimePatternCore p $ RuntimePatternVariable ux σ
  renameTerm ux x (TermRuntimePatternCore p pm) = TermRuntimePatternCore p $ mapTermRuntimePatternF id go pm
    where
      go = renameTerm ux x

instance RenameTerm (TermPattern p v) where
  renameTerm ux x (TermPatternCore p (PatternVariable x' σ)) | x == x' = TermPatternCore p $ PatternVariable ux σ
  renameTerm ux x (TermPatternCore p pm) = TermPatternCore p $ mapTermPatternF id go pm
    where
      go = renameTerm ux x

instance ConvertType (TermSource p) where
  convertType ux x (TermSource p e) = TermSource p $ mapTermF id id id go go'' go go' go' go e
    where
      go = convertType ux x
      go' = convertHigherType ux x
      go'' = convertRgnForType ux x

instance FreeVariablesType (TermPattern p v) where
  freeVariablesType (TermPatternCore _ pm) = foldTermPatternF go go pm
    where
      go = freeVariablesType

instance SubstituteType (TermPattern p) where
  substituteType ux x (TermPatternCore p pm) = TermPatternCore p $ mapTermPatternF go go pm
    where
      go = substituteType ux x

instance ConvertType (TermPattern p v) where
  convertType ux x (TermPatternCore p pm) = TermPatternCore p $ mapTermPatternF go go pm
    where
      go = convertType ux x

instance Reduce (TermPattern p v) where
  reduce (TermPatternCore p pm) = TermPatternCore p $ mapTermPatternF go go pm
    where
      go = reduce

instance FreeVariablesType (TermRuntimePattern p v) where
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

instance ConvertType (TermRuntimePattern p v) where
  convertType ux x (TermRuntimePatternCore p pm) = TermRuntimePatternCore p $ mapTermRuntimePatternF go go pm
    where
      go = convertType ux x

instance SubstituteType (TermRuntimePattern p) where
  substituteType ux x (TermRuntimePatternCore p pm) = TermRuntimePatternCore p $ mapTermRuntimePatternF go go pm
    where
      go = substituteType ux x

instance Reduce (TermRuntimePattern p v) where
  reduce (TermRuntimePatternCore p pm) = TermRuntimePatternCore p $ mapTermRuntimePatternF go go pm
    where
      go = reduce

instance FreeVariablesTerm (Term p v) where
  freeVariablesTerm (TermCore _ (TermRuntime (Variable x _))) = Set.singleton x
  freeVariablesTerm (TermCore _ e) = foldTermF absurd mempty mempty mempty go'' go go' go' go e
    where
      go = freeVariablesTerm
      go' = freeVariablesSameTerm
      go'' = freeVariablesRgnForTerm

instance FreeVariablesTermSource TermSource where
  freeVariablesTermSource (TermSource p (TermRuntime (Variable x _))) = Variables $ Map.singleton x p
  freeVariablesTermSource (TermSource _ e) = foldTermF mempty mempty mempty mempty go'' go go' go' go e
    where
      go = freeVariablesTermSource
      go' = freeVariablesSameTermSource
      go'' = freeVariablesRgnSourceForTerm

instance ConvertTerm (Term p v) where
  convertTerm ux x (TermCore p (TermRuntime (Variable x' θ))) | x == x' = TermCore p $ TermRuntime $ Variable ux θ
  convertTerm ux x (TermCore p e) = TermCore p $ mapTermF absurd id id id go'' go go' go' go e
    where
      go = convertTerm ux x
      go' = convertSameTerm ux x
      go'' = convertRgnForTerm ux x

instance SubstituteTerm Term where
  substituteTerm ux x (TermCore _ (TermRuntime (Variable x' θ))) | x == x' = go ux θ
    where
      go (TermSchemeCore _ (TypeAbstraction λ)) (InstantiationCore (InstantiateType σ θ)) = go (apply λ σ) θ
        where
          apply (Bound (TypePattern α _ _ _) e) σ = substituteType σ α e
      go (TermSchemeCore _ (KindAbstraction λ)) (InstantiationCore (InstantiateKind κ θ)) = go (apply λ κ) θ
        where
          apply (Bound (KindPattern α _) e) κ = substituteType κ α e
      go (TermSchemeCore _ (MonoTerm e)) (InstantiationCore InstantiateEmpty) = e
      go _ _ = error "unable to substitute"
  substituteTerm ux x (TermCore p e) = TermCore p $ mapTermF absurd id id id go'' go go' go' go e
    where
      go = substituteTerm ux x
      go' = substituteSameTerm ux x
      go'' = substituteRgnForTerm ux x

instance FreeVariablesType (Term p v) where
  freeVariablesType (TermCore _ e) = foldTermF absurd go go go go'' go go' go' go e
    where
      go = freeVariablesType
      go' = freeVariablesHigherType
      go'' = freeVariablesRgnForType

instance ConvertType (Term p v) where
  convertType ux x (TermCore p e) = TermCore p $ mapTermF absurd go go go go'' go go' go' go e
    where
      go = convertType ux x
      go' = convertHigherType ux x
      go'' = convertRgnForType ux x

instance SubstituteType (Term p) where
  substituteType ux x (TermCore p e) = TermCore p $ mapTermF absurd go go go go'' go go' go' go e
    where
      go = substituteType ux x
      go' = substituteHigherType ux x
      go'' = substituteRgnForType ux x

instance FreeVariablesTerm (TermScheme p v) where
  freeVariablesTerm (TermSchemeCore _ e) = foldTermSchemeF go' go' go e
    where
      go = freeVariablesTerm
      go' = freeVariablesLowerTerm

instance FreeVariablesTermSource TermSchemeSource where
  freeVariablesTermSource (TermSchemeSource _ e) = foldTermSchemeF go' go' go e
    where
      go = freeVariablesTermSource
      go' = freeVariablesLowerTermSource

instance FreeVariablesTermSource TermControlSource where
  freeVariablesTermSource (TermAutoSource e) = freeVariablesTermSource e
  freeVariablesTermSource (TermManualSource e) = freeVariablesTermSource e

instance ConvertTerm (TermScheme p v) where
  convertTerm ux x (TermSchemeCore p e) = TermSchemeCore p $ mapTermSchemeF go' go' go e
    where
      go = convertTerm ux x
      go' = convertLowerTerm ux x

instance SubstituteTerm TermScheme where
  substituteTerm ux x (TermSchemeCore p e) = TermSchemeCore p $ mapTermSchemeF go' go' go e
    where
      go = substituteTerm ux x
      go' = substituteLowerTerm avoidType ux x

instance FreeVariablesType (TermScheme p v) where
  freeVariablesType (TermSchemeCore _ e) = foldTermSchemeF go' go' go e
    where
      go = freeVariablesType
      go' = freeVariablesSameType

instance ConvertType (TermSchemeSource p) where
  convertType ux x (TermSchemeSource p e) = TermSchemeSource p $ mapTermSchemeF go' go' go e
    where
      go = convertType ux x
      go' = convertSameType ux x

instance ConvertType (TermScheme p v) where
  convertType ux x (TermSchemeCore p e) = TermSchemeCore p $ mapTermSchemeF go' go' go e
    where
      go = convertType ux x
      go' = convertSameType ux x

instance SubstituteType (TermScheme p) where
  substituteType ux x (TermSchemeCore p e) = TermSchemeCore p $ mapTermSchemeF go' go' go e
    where
      go = substituteType ux x
      go' = substituteSameType ux x

applyTerm (Bound (TermPatternCore _ (PatternVariable x _)) e@(TermCore p _)) ux =
  reduce $ substituteTerm (TermSchemeCore p (MonoTerm ux)) x e
applyTerm (Bound (TermPatternCore _ (PatternOfCourse pm)) e) (TermCore _ (OfCourseIntroduction ux)) = applyTerm (Bound pm e) ux
-- todo find better position here
applyTerm λ ux@(TermCore p _) = TermCore p $ Bind ux λ

instance Reduce (Term p v) where
  reduce (TermCore _ (Bind e λ)) = applyTerm (reduce λ) (reduce e)
  reduce (TermCore _ (InlineApplication e1 e2 _)) | (TermCore _ (InlineAbstraction λ)) <- reduce e1 = applyTerm λ (reduce e2)
  reduce (TermCore _ (PolyElimination e1 (InstantiationCore InstantiateEmpty) _))
    | (TermCore _ (PolyIntroduction (TermSchemeCore _ (MonoTerm e)))) <- reduce e1 = reduce e
  reduce (TermCore p (PolyElimination e1 (InstantiationCore (InstantiateType σ θ)) σ'))
    | (TermCore _ (PolyIntroduction (TermSchemeCore _ (TypeAbstraction λ)))) <-
        reduce e1 =
      reduce $ TermCore p $ PolyElimination (TermCore p $ PolyIntroduction $ applyType λ σ) θ σ'
    where
      applyType (Bound (TypePattern α _ _ _) e) σ = substituteType σ α e
  reduce (TermCore p (PolyElimination e1 (InstantiationCore (InstantiateKind κ θ)) σ'))
    | (TermCore _ (PolyIntroduction (TermSchemeCore _ (KindAbstraction λ)))) <-
        reduce e1 =
      reduce $ TermCore p $ PolyElimination (TermCore p $ PolyIntroduction $ applyKind λ κ) θ σ'
    where
      applyKind (Bound (KindPattern α _) e) σ = substituteType σ α e
  reduce (TermCore p e) = TermCore p (mapTermF absurd go go go go go go go go e)
    where
      go = reduce

instance ZonkType (TermScheme p) where
  zonkType f (TermSchemeCore p e) =
    pure TermSchemeCore <*> pure p
      <*> traverseTermSchemeF
        (traverseBound (zonkType f) (zonkType f))
        (traverseBound (zonkType f) (zonkType f))
        (zonkType f)
        e

instance ZonkType (Term p) where
  zonkType f (TermCore p e) =
    pure TermCore <*> pure p
      <*> traverseTermF
        absurd
        (zonkType f)
        (zonkType f)
        (zonkType f)
        (traverseBound (zonkType f) (traverseBound (zonkType f) (zonkType f)))
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

instance Reduce (TermScheme p v) where
  reduce (TermSchemeCore p e) = TermSchemeCore p $ mapTermSchemeF go go go e
    where
      go = reduce

instance Location TermSource where
  location (TermSource p _) = p

instance Location TermPatternSource where
  location (TermPatternSource p _) = p

instance Location TermRuntimePatternSource where
  location (TermRuntimePatternSource p _) = p

sourceTermScheme :: Monoid p' => TermScheme p Void -> TermSchemeSource p'
sourceTermScheme (TermSchemeCore _ e) =
  TermSchemeSource mempty $
    mapTermSchemeF
      (mapBound sourceKindPattern sourceTermScheme)
      (mapBound sourceTypePattern sourceTermScheme)
      sourceTerm
      e

sourceTermAnnotate annotate e σ =
  TermSource mempty $
    annotate (sourceTerm e) (sourceTypeAuto σ) ()

-- todo consider not emitting type annotions for lambda bindings
-- as those don't need them (in checking mode)
sourceTerm :: Monoid p' => Term p Void -> TermSource p'
sourceTerm (TermCore _ e) =
  TermSource mempty $ case e of
    TermRuntime e -> TermRuntime $ case e of
      Variable x _ -> Variable x ()
      Alias e λ -> Alias (sourceTerm e) (mapBound sourceTermRuntimePattern sourceTerm λ)
      FunctionApplication e e' σ -> FunctionApplication (sourceTerm e) (sourceTermAnnotate PretypeAnnotation e' σ) ()
      TupleIntroduction es -> TupleIntroduction (map sourceTerm es)
      ReadReference e -> ReadReference (sourceTerm e)
      WriteReference e e' σ -> WriteReference (sourceTerm e) (sourceTermAnnotate PretypeAnnotation e' σ) ()
      NumberLiteral n -> NumberLiteral n
      Arithmatic o e e' _ -> Arithmatic o (sourceTerm e) (sourceTerm e') ()
      Relational o e e' σ _ -> Relational o (sourceTermAnnotate PretypeAnnotation e σ) (sourceTermAnnotate PretypeAnnotation e' σ) () ()
      BooleanLiteral b -> BooleanLiteral b
      If e e' e'' -> If (sourceTerm e) (sourceTerm e') (sourceTerm e'')
      Extern sym _ _ _ -> Extern sym () () ()
      PointerIncrement e e' _ -> PointerIncrement (sourceTerm e) (sourceTerm e') ()
    TermSugar _ invalid -> absurd invalid
    FunctionLiteral λ -> FunctionLiteral (mapBound sourceTermRuntimePattern sourceTerm λ)
    Borrow e λ -> Borrow (sourceTerm e) (mapBound sourceTypePattern (mapBound sourceTermRuntimePattern sourceTerm) λ)
    InlineAbstraction λ -> InlineAbstraction (mapBound sourceTermPattern sourceTerm λ)
    InlineApplication e e' σ -> InlineApplication (sourceTerm e) (sourceTermAnnotate TypeAnnotation e' σ) ()
    OfCourseIntroduction e -> OfCourseIntroduction (sourceTerm e)
    Bind e λ -> Bind (sourceTerm e) (mapBound sourceTermPattern sourceTerm λ)
    PolyIntroduction λ -> PolyIntroduction (sourceTermScheme λ)
    PolyElimination e _ σ ->
      PolyElimination
        (sourceTermAnnotate TypeAnnotation e σ)
        ()
        ()
    TypeAnnotation _ _ invalid -> absurd invalid
    PretypeAnnotation _ _ invalid -> absurd invalid

sourceTermPattern :: Monoid p' => TermPattern p Void -> TermPatternSource p'
sourceTermPattern (TermPatternCore _ pm) =
  TermPatternSource mempty $
    mapTermPatternF sourceTypeAuto sourceTermPattern pm

sourceTermRuntimePattern :: Monoid p' => TermRuntimePattern p Void -> TermRuntimePatternSource p'
sourceTermRuntimePattern (TermRuntimePatternCore _ pm) =
  TermRuntimePatternSource mempty $
    mapTermRuntimePatternF sourceTypeAuto sourceTermRuntimePattern pm
