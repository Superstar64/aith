{-# LANGUAGE LambdaCase #-}

module Ast.Term where

import Ast.Common
import Ast.Type
import Control.Category (id, (.))
import Data.Bifoldable (Bifoldable (bifoldMap))
import Data.Bifunctor (Bifunctor, bimap)
import Data.Bitraversable (Bitraversable, bitraverse)
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
import Misc.Isomorph
import Misc.Path
import Misc.Prism
import Misc.Symbol
import qualified Misc.Util as Util
import Prelude hiding (id, (.))

newtype TermIdentifier = TermIdentifier {runTermIdentifier :: String} deriving (Show, Eq, Ord)

newtype TermGlobalIdentifier = TermGlobalIdentifier {runTermGlobalIdentifier :: Path} deriving (Show, Eq, Ord)

data TermPatternF σ pm
  = PatternVariable TermIdentifier σ
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
  | Continue e
  | Break e
  | Loop e λe
  deriving (Show)

data TermSugar e
  = Not e
  | And e e
  | Or e e
  | Do e e
  deriving (Show, Functor)

data TermErasure σauto λrgn_e e
  = Borrow e λrgn_e
  | IsolatePointer e
  | Wrap σauto e
  | Unwrap σauto e
  deriving (Show)

data TermF ann θ σauto λrgn_e λσe λe λrun_e e
  = TermRuntime (TermRuntime θ σauto σauto σauto λrun_e e)
  | TermErasure (TermErasure σauto λrgn_e e)
  | TermSugar (TermSugar e)
  | Annotation ann
  | GlobalVariable TermGlobalIdentifier θ
  | FunctionLiteral λrun_e
  | InlineAbstraction λe
  | InlineApplication e e σauto
  | Bind e λe
  | PolyIntroduction λσe
  | PolyElimination e θ σauto
  deriving (Show)

traverseTermPatternF ::
  Applicative m =>
  (σ -> m σ') ->
  (pm -> m pm') ->
  TermPatternF σ pm ->
  m (TermPatternF σ' pm')
traverseTermPatternF f _ pm = case pm of
  PatternVariable x σ -> pure PatternVariable <*> pure x <*> f σ

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
    Continue e -> pure Continue <*> i e
    Break e -> pure Break <*> i e
    Loop e λ -> pure Loop <*> i e <*> g λ

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
  (ann -> m ann') ->
  (θ -> m θ') ->
  (σauto -> m σauto') ->
  (λrgn_e -> m λrgn_e') ->
  (λσe -> m λσe') ->
  (λe -> m λe') ->
  (λrun_e -> m λrun_e') ->
  (e -> m e') ->
  TermF ann θ σauto λrgn_e λσe λe λrun_e e ->
  m (TermF ann' θ' σauto' λrgn_e' λσe' λe' λrun_e' e')
traverseTermF y d z r k h m i e =
  case e of
    TermRuntime e -> pure TermRuntime <*> traverseTermRuntime d z z z m i e
    TermSugar e -> pure TermSugar <*> traverseTermSugar i e
    Annotation e -> pure Annotation <*> y e
    GlobalVariable x θ -> pure GlobalVariable <*> pure x <*> d θ
    FunctionLiteral λ -> pure FunctionLiteral <*> m λ
    TermErasure (Borrow e λ) -> TermErasure <$> (Borrow <$> i e <*> r λ)
    TermErasure (IsolatePointer e) -> TermErasure <$> (IsolatePointer <$> i e)
    TermErasure (Wrap σ e) -> TermErasure <$> (Wrap <$> z σ <*> i e)
    TermErasure (Unwrap σ e) -> TermErasure <$> (Unwrap <$> z σ <*> i e)
    InlineAbstraction λ -> pure InlineAbstraction <*> h λ
    InlineApplication e1 e2 σ -> pure InlineApplication <*> i e1 <*> i e2 <*> z σ
    Bind e λ -> pure Bind <*> i e <*> h λ
    PolyIntroduction λ -> pure PolyIntroduction <*> k λ
    PolyElimination e θ σ2 -> pure PolyElimination <*> i e <*> d θ <*> z σ2

foldTermF d j z f r h m i = getConst . traverseTermF (Const . d) (Const . j) (Const . z) (Const . f) (Const . r) (Const . h) (Const . m) (Const . i)

mapTermF d j z f r h m i = runIdentity . traverseTermF (Identity . d) (Identity . j) (Identity . z) (Identity . f) (Identity . r) (Identity . h) (Identity . m) (Identity . i)

data Term p phase p' v
  = Term
      p
      ( TermF
          (phase (Annotation p phase p' v) Void)
          (phase () (Instantiation p' v))
          (phase () (Type p' v))
          (Bound (TypePattern p' v) (Bound (TermRuntimePattern p phase p' v) (Term p phase p' v)))
          (TermScheme p phase p' v)
          (Bound (TermPattern p phase p' v) (Term p phase p' v))
          (Bound (TermRuntimePattern p phase p' v) (Term p phase p' v))
          (Term p phase p' v)
      )

type TermSource p = Term p Source p Void

type TermUnify p = Term p Core () TypeLogical

type TermInfer p = Term p Core () Void

data TermScheme p phase p' v = TermScheme p (TermSchemeF p phase p' v)

data TermSchemeF p phase p' v
  = MonoTerm (Term p phase p' v)
  | TypeAbstraction (Bound (TypePattern p' v) (TermScheme p phase p' v))

type TermSchemeSource p = TermScheme p Source p Void

type TermSchemeUnify p = TermScheme p Core () TypeLogical

type TermSchemeInfer p = TermScheme p Core () Void

data TermPattern p phase p' v = TermPattern p (TermPatternF (phase (Maybe (Type p' v)) (Type p' v)) (TermPattern p phase p' v))

type TermPatternSource p = TermPattern p Source p Void

type TermPatternUnify p = TermPattern p Core () TypeLogical

type TermPatternInfer p = TermPattern p Core () Void

data TermRuntimePattern p phase p' v = TermRuntimePattern p (TermRuntimePatternF (phase (Maybe (Type p' v)) (Type p' v)) (TermRuntimePattern p phase p' v))

type TermRuntimePatternSource p = TermRuntimePattern p Source p Void

type TermRuntimePatternUnify p = TermRuntimePattern p Core () TypeLogical

type TermRuntimePatternInfer p = TermRuntimePattern p Core () Void

data TermControl p phase p' v
  = TermAutoSource (Term p phase p' v)
  | TermManualSource (TermScheme p phase p' v)

type TermControlSource p = TermControl p Source p Void

data Annotation p phase p' v
  = TypeAnnotation (Term p phase p' v) (Type p' v)
  | PretypeAnnotation (Term p phase p' v) (Type p' v)

type AnnotationSource p = Annotation p Source p Void

desugar p (Not e) =
  Term
    p
    ( TermRuntime $
        If
          e
          (Term p $ TermRuntime $ BooleanLiteral False)
          (Term p $ TermRuntime $ BooleanLiteral True)
    )
desugar p (And e e') =
  Term
    p
    ( TermRuntime $
        If
          e
          e'
          (Term p $ TermRuntime $ BooleanLiteral False)
    )
desugar p (Or e e') =
  Term
    p
    ( TermRuntime $
        If
          e
          (Term p $ TermRuntime $ BooleanLiteral True)
          e'
    )
desugar p (Do e e') =
  Term
    p
    ( TermRuntime $
        Alias e (Bound (TermRuntimePattern p $ RuntimePatternTuple []) e')
    )

termPatternSource = Isomorph (uncurry TermPattern) $ \(TermPattern p pm) -> (p, pm)

termRuntimePatternSource = Isomorph (uncurry TermRuntimePattern) $ \(TermRuntimePattern p pm) -> (p, pm)

patternVariable =
  Prism (uncurry PatternVariable) $ \case
    (PatternVariable x σ) -> Just (x, σ)

runtimePatternVariable =
  Prism (uncurry RuntimePatternVariable) $ \case
    (RuntimePatternVariable x σ) -> Just (x, σ)
    _ -> Nothing

runtimePatternTuple = Prism RuntimePatternTuple $ \case
  (RuntimePatternTuple pms) -> Just pms
  _ -> Nothing

termSource = Isomorph (uncurry Term) $ \(Term p e) -> (p, e)

termRuntime = Prism TermRuntime $ \case
  (TermRuntime e) -> Just e
  _ -> Nothing

termSugar = Prism TermSugar $ \case
  (TermSugar e) -> Just e
  _ -> Nothing

variable = (termRuntime .) $
  Prism (\x -> Variable x (Source ())) $ \case
    (Variable x (Source ())) -> Just x
    _ -> Nothing

globalVariable = Prism (\x -> GlobalVariable x (Source ())) $ \case
  (GlobalVariable x (Source ())) -> Just x
  _ -> Nothing

inlineAbstraction = Prism (InlineAbstraction) $ \case
  (InlineAbstraction λ) -> Just λ
  _ -> Nothing

inlineApplication = Prism (\(e, e') -> InlineApplication e e' (Source ())) $ \case
  (InlineApplication e e' (Source ())) -> Just (e, e')
  _ -> Nothing

bind = Prism (uncurry $ Bind) $ \case
  (Bind e λ) -> Just (e, λ)
  _ -> Nothing

alias = (termRuntime .) $
  Prism (uncurry $ Alias) $ \case
    (Alias e λ) -> Just (e, λ)
    _ -> Nothing

extern = (termRuntime .) $
  Prism (\sym -> Extern sym (Source ()) (Source ()) (Source ())) $ \case
    (Extern sym (Source ()) (Source ()) (Source ())) -> Just sym
    _ -> Nothing

functionApplication = (termRuntime .) $
  Prism (\(e, e') -> FunctionApplication e e' (Source ())) $ \case
    (FunctionApplication e e' (Source ())) -> Just (e, e')
    _ -> Nothing

functionLiteral =
  Prism (FunctionLiteral) $ \case
    (FunctionLiteral λ) -> Just λ
    _ -> Nothing

tupleIntroduction = (termRuntime .) $
  Prism TupleIntroduction $ \case
    (TupleIntroduction es) -> Just es
    _ -> Nothing

readReference = (termRuntime .) $
  Prism (ReadReference) $ \case
    (ReadReference e) -> Just (e)
    _ -> Nothing

writeReference = (termRuntime .) $
  Prism (\(e, e') -> WriteReference e e' (Source ())) $ \case
    (WriteReference e e' (Source ())) -> Just (e, e')
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
  Prism (\(e, e') -> Arithmatic o e e' (Source ())) $ \case
    Arithmatic o' e e' (Source ()) | o == o' -> Just (e, e')
    _ -> Nothing

relational o = (termRuntime .) $
  Prism (\(e, e') -> Relational o e e' (Source ()) (Source ())) $ \case
    Relational o' e e' (Source ()) (Source ()) | o == o' -> Just (e, e')
    _ -> Nothing

pointerIncrement = (termRuntime .) $
  Prism (\(e, e') -> PointerIncrement e e' (Source ())) $ \case
    PointerIncrement e e' (Source ()) -> Just (e, e')
    _ -> Nothing

continue = (termRuntime .) $
  Prism Continue $ \case
    Continue e -> Just e
    _ -> Nothing

break = (termRuntime .) $
  Prism Break $ \case
    Break e -> Just e
    _ -> Nothing

loop = (termRuntime .) $
  Prism (uncurry Loop) $ \case
    Loop e λ -> Just (e, λ)
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

polyElimination = Prism (\e -> PolyElimination e (Source ()) (Source ())) $ \case
  PolyElimination e (Source ()) (Source ()) -> Just e
  _ -> Nothing

termSchemeSource = Isomorph (uncurry TermScheme) $ \(TermScheme p e) -> (p, e)

monoTerm = Prism MonoTerm $ \case
  (MonoTerm σ) -> Just σ
  _ -> Nothing

typeAbstraction = Prism TypeAbstraction $ \case
  (TypeAbstraction λ) -> Just λ
  _ -> Nothing

annotation = Prism Annotation $ \case
  Annotation e -> Just e
  _ -> Nothing

typeAnnotation = (annotation .) $
  (toPrism source .) $
    Prism (uncurry TypeAnnotation) $ \case
      (TypeAnnotation e σ) -> Just (e, σ)
      _ -> Nothing

preTypeAnnotation = (annotation .) $
  (toPrism source .) $
    Prism (uncurry PretypeAnnotation) $ \case
      (PretypeAnnotation e σ) -> Just (e, σ)
      _ -> Nothing

termErasure = Prism TermErasure $ \case
  TermErasure e -> Just e
  _ -> Nothing

borrow = (termErasure .) $
  Prism (uncurry Borrow) $ \case
    (Borrow e λ) -> Just (e, λ)
    _ -> Nothing

isolatePointer = (termErasure .) $
  Prism IsolatePointer $ \case
    IsolatePointer e -> Just e
    _ -> Nothing

wrap = (termErasure .) $
  Prism (Wrap (Source ())) $ \case
    Wrap (Source ()) e -> Just e
    _ -> Nothing

unwrap = (termErasure .) $
  Prism (Unwrap (Source ())) $ \case
    Unwrap (Source ()) e -> Just e
    _ -> Nothing

termAutoSource = Prism TermAutoSource $ \case
  TermAutoSource e -> Just e
  _ -> Nothing

termManualSource = Prism TermManualSource $ \case
  TermManualSource e -> Just e
  _ -> Nothing

termIdentifier = Isomorph TermIdentifier runTermIdentifier

termGlobalIdentifier = Isomorph TermGlobalIdentifier runTermGlobalIdentifier

class TraverseTerm u where
  traverseTerm ::
    (Bitraversable phase, Applicative m) =>
    (p1 -> m p1') ->
    (p2 -> m p2') ->
    (v -> m v') ->
    u p1 phase p2 v ->
    m (u p1' phase p2' v')

class TraverseTerm u => TermAlgebra u where
  freeVariablesTerm :: Bifoldable phase => u p phase p' v -> Set TermIdentifier
  freeVariablesGlobalTerm :: Bifoldable phase => u p phase p' v -> Set TermGlobalIdentifier
  convertTerm :: Bifunctor phase => TermIdentifier -> TermIdentifier -> u p phase p' v -> u p phase p' v

  freeVariablesTermSource :: Semigroup p => u p Source p v -> Variables TermIdentifier p
  freeVariablesGlobalTermSource :: Semigroup p => u p Source p v -> Variables TermGlobalIdentifier p

  substituteTerm :: TermScheme p Core p' v -> TermIdentifier -> u p Core p' v -> u p Core p' v
  substituteGlobalTerm :: TermScheme p Core p' v -> TermGlobalIdentifier -> u p Core p' v -> u p Core p' v

  -- Applicative Order Reduction
  -- see https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf

  reduce :: u p Core p' v -> u p Core p' v

class BindingsTerm pm where
  bindingsTerm :: pm -> Set TermIdentifier
  renameTerm :: TermIdentifier -> TermIdentifier -> pm -> pm

mapTermPosition f e = runIdentity $ traverseTerm (Identity . f) (Identity . f) pure e

freeVariablesSameTerm = freeVariablesSame bindingsTerm freeVariablesTerm

freeVariablesSameTermSource = freeVariablesSameSource bindingsTerm freeVariablesTermSource

freeVariablesLowerGlobalTerm = freeVariablesLower freeVariablesGlobalTerm

freeVariablesLowerGlobalTermSource = freeVariablesLower freeVariablesGlobalTermSource

convertSameTerm = substituteSame avoidTermConvert convertTerm

substituteSameTerm = substituteSame avoidTerm substituteTerm

freeVariablesLowerTerm = freeVariablesLower freeVariablesTerm

freeVariablesLowerTermSource = freeVariablesLower freeVariablesTermSource

convertLowerTerm = convertLower convertTerm

substituteLowerTerm avoid = substituteLower avoid substituteTerm

substituteLowerGlobalTerm = substituteLowerGlobalTerm' avoidTerm

substituteLowerGlobalTerm' avoid = substituteLower avoid substituteGlobalTerm

freeVariablesRgnForTerm = freeVariablesLower freeVariablesSameTerm

freeVariablesGlobalRgnForTerm = freeVariablesLower freeVariablesLowerGlobalTerm

freeVariablesRgnSourceForTerm = freeVariablesLower freeVariablesSameTermSource

freeVariablesGlobalRGNSourceForTerm = freeVariablesLower freeVariablesLowerGlobalTermSource

convertRgnForTerm = convertLower convertSameTerm

substituteRgnForTerm = substituteLower (avoidType' convertHigherType) substituteSameTerm

substituteRgnForTermGlobal = substituteLower (avoidType' convertHigherType) substituteLowerGlobalTerm

avoidTerm = avoidTerm' convertTerm

avoidTerm' = Avoid bindingsTerm renameTerm freeVariablesTerm

avoidTermConvert = avoidTermConvert' convertTerm

avoidTermConvert' = Avoid bindingsTerm renameTerm Set.singleton

applySchemeImpl (TermScheme _ (TypeAbstraction λ)) (Instantiation (InstantiateType σ θ)) = applySchemeImpl (apply λ σ) θ
  where
    apply (Bound (TypePattern _ α _ _) e) σ = substituteType σ α e
applySchemeImpl (TermScheme _ (MonoTerm e)) (Instantiation InstantiateEmpty) = e
applySchemeImpl _ _ = error "unable to substitute"

instance Fresh TermIdentifier where
  fresh c (TermIdentifier x) = TermIdentifier $ Util.fresh (Set.mapMonotonic runTermIdentifier c) x

instance TraverseTerm Term where
  traverseTerm fp fp' fv (Term p e) =
    Term <$> fp p
      <*> traverseTermF
        (bitraverse go absurd)
        (bitraverse pure go')
        (bitraverse pure go')
        (traverseBound go' (traverseBound go go))
        go
        (traverseBound go go)
        (traverseBound go go)
        go
        e
    where
      go = traverseTerm fp fp' fv
      go' = traverseType fp' fv

instance TermAlgebra Term where
  freeVariablesTerm (Term _ (TermRuntime (Variable x _))) = Set.singleton x
  freeVariablesTerm (Term _ e) = foldTermF (bifoldMap go absurd) mempty mempty go'' go go' go' go e
    where
      go = freeVariablesTerm
      go' = freeVariablesSameTerm
      go'' = freeVariablesRgnForTerm
  freeVariablesGlobalTerm (Term _ (GlobalVariable x _)) = Set.singleton x
  freeVariablesGlobalTerm (Term _ e) = foldTermF (bifoldMap go absurd) mempty mempty go'' go go' go' go e
    where
      go = freeVariablesGlobalTerm
      go' = freeVariablesLowerGlobalTerm
      go'' = freeVariablesGlobalRgnForTerm
  convertTerm ux x (Term p (TermRuntime (Variable x' θ))) | x == x' = Term p $ TermRuntime $ Variable ux θ
  convertTerm ux x (Term p e) = Term p $ mapTermF (bimap go absurd) id id go'' go go' go' go e
    where
      go = convertTerm ux x
      go' = convertSameTerm ux x
      go'' = convertRgnForTerm ux x
  freeVariablesTermSource (Term p (TermRuntime (Variable x _))) = Variables $ Map.singleton x p
  freeVariablesTermSource (Term _ e) = foldTermF (bifoldMap go absurd) mempty mempty go'' go go' go' go e
    where
      go = freeVariablesTermSource
      go' = freeVariablesSameTermSource
      go'' = freeVariablesRgnSourceForTerm
  freeVariablesGlobalTermSource (Term p (GlobalVariable x _)) = Variables $ Map.singleton x p
  freeVariablesGlobalTermSource (Term _ e) = foldTermF (bifoldMap go absurd) mempty mempty go'' go go' go' go e
    where
      go = freeVariablesGlobalTermSource
      go' = freeVariablesLowerGlobalTermSource
      go'' = freeVariablesGlobalRGNSourceForTerm
  substituteTerm ux x (Term _ (TermRuntime (Variable x' (Core θ)))) | x == x' = applySchemeImpl ux θ
  substituteTerm ux x (Term p e) = Term p $ mapTermF (bimap go absurd) id id go'' go go' go' go e
    where
      go = substituteTerm ux x
      go' = substituteSameTerm ux x
      go'' = substituteRgnForTerm ux x
  substituteGlobalTerm ux x (Term _ (GlobalVariable x' (Core θ))) | x == x' = applySchemeImpl ux θ
  substituteGlobalTerm ux x (Term p e) = Term p $ mapTermF (bimap go absurd) id id go'' go go' go' go e
    where
      go = substituteGlobalTerm ux x
      go' = substituteLowerGlobalTerm ux x
      go'' = substituteRgnForTermGlobal ux x
  reduce (Term _ (Bind e λ)) = applyTerm (mapBound id reduce λ) (reduce e)
  reduce (Term _ (InlineApplication e1 e2 _)) | (Term _ (InlineAbstraction λ)) <- reduce e1 = applyTerm λ (reduce e2)
  reduce (Term _ (PolyElimination e1 (Core (Instantiation InstantiateEmpty)) _))
    | (Term _ (PolyIntroduction (TermScheme _ (MonoTerm e)))) <- reduce e1 = reduce e
  reduce (Term p (PolyElimination e1 (Core (Instantiation (InstantiateType σ θ))) σ'))
    | (Term _ (PolyIntroduction (TermScheme _ (TypeAbstraction λ)))) <-
        reduce e1 =
      reduce $ Term p $ PolyElimination (Term p $ PolyIntroduction $ applyType λ σ) (Core θ) σ'
    where
      applyType (Bound (TypePattern _ α _ _) e) σ = substituteType σ α e
  reduce (Term p (TermSugar e)) = reduce (desugar p e)
  reduce (Term p e) = Term p (mapTermF (bimap go absurd) id id (mapBound id (mapBound id go)) go (mapBound id go) (mapBound id go) go e)
    where
      go = reduce

instance TraverseTerm TermScheme where
  traverseTerm fp fp' fv (TermScheme p e)
    | MonoTerm e <- e = TermScheme <$> fp p <*> (MonoTerm <$> go e)
    | TypeAbstraction λ <- e = TermScheme <$> fp p <*> (TypeAbstraction <$> traverseBound go' go λ)
    where
      go = traverseTerm fp fp' fv
      go' = traverseType fp' fv

instance TermAlgebra TermScheme where
  freeVariablesTerm (TermScheme _ (MonoTerm e)) = freeVariablesTerm e
  freeVariablesTerm (TermScheme _ (TypeAbstraction λ)) = freeVariablesLowerTerm λ
  freeVariablesGlobalTerm (TermScheme _ (MonoTerm e)) = freeVariablesGlobalTerm e
  freeVariablesGlobalTerm (TermScheme _ (TypeAbstraction λ)) = freeVariablesLowerGlobalTerm λ
  freeVariablesTermSource (TermScheme _ (MonoTerm e)) = freeVariablesTermSource e
  freeVariablesTermSource (TermScheme _ (TypeAbstraction λ)) = freeVariablesLowerTermSource λ
  freeVariablesGlobalTermSource (TermScheme _ (MonoTerm e)) = freeVariablesGlobalTermSource e
  freeVariablesGlobalTermSource (TermScheme _ (TypeAbstraction λ)) = freeVariablesLowerGlobalTermSource λ
  convertTerm ux x (TermScheme p (MonoTerm e)) = TermScheme p $ MonoTerm (convertTerm ux x e)
  convertTerm ux x (TermScheme p (TypeAbstraction λ)) = TermScheme p $ TypeAbstraction (convertLowerTerm ux x λ)
  substituteTerm ux x (TermScheme p (MonoTerm e)) = TermScheme p $ MonoTerm (substituteTerm ux x e)
  substituteTerm ux x (TermScheme p (TypeAbstraction λ)) = TermScheme p $ TypeAbstraction (substituteLowerTerm avoidType ux x λ)
  substituteGlobalTerm ux x (TermScheme p (MonoTerm e)) = TermScheme p $ MonoTerm (substituteGlobalTerm ux x e)
  substituteGlobalTerm ux x (TermScheme p (TypeAbstraction λ)) = TermScheme p $ TypeAbstraction (substituteLowerGlobalTerm' avoidType ux x λ)
  reduce (TermScheme p e)
    | MonoTerm e <- e = TermScheme p $ MonoTerm (go e)
    | TypeAbstraction λ <- e = TermScheme p $ TypeAbstraction (mapBound id go λ)
    where
      go = reduce

instance TraverseTerm TermPattern where
  traverseTerm fp fp' fv (TermPattern p pm) =
    TermPattern <$> fp p <*> traverseTermPatternF (bitraverse (traverse go') go') go pm
    where
      go = traverseTerm fp fp' fv
      go' = traverseType fp' fv

instance TraverseTerm TermRuntimePattern where
  traverseTerm fp fp' fv (TermRuntimePattern p pm) =
    TermRuntimePattern <$> fp p <*> traverseTermRuntimePatternF (bitraverse (traverse go') go') go pm
    where
      go = traverseTerm fp fp' fv
      go' = traverseType fp' fv

instance TraverseTerm Annotation where
  traverseTerm fp fp' fv (TypeAnnotation e σ) = TypeAnnotation <$> traverseTerm fp fp' fv e <*> traverseType fp' fv σ
  traverseTerm fp fp' fv (PretypeAnnotation e σ) = PretypeAnnotation <$> traverseTerm fp fp' fv e <*> traverseType fp' fv σ

instance TermAlgebra Annotation where
  freeVariablesTermSource (TypeAnnotation e _) = freeVariablesTermSource e
  freeVariablesTermSource (PretypeAnnotation e _) = freeVariablesTermSource e
  freeVariablesGlobalTermSource (TypeAnnotation e _) = freeVariablesGlobalTermSource e
  freeVariablesGlobalTermSource (PretypeAnnotation e _) = freeVariablesGlobalTermSource e
  freeVariablesTerm (TypeAnnotation e _) = freeVariablesTerm e
  freeVariablesTerm (PretypeAnnotation e _) = freeVariablesTerm e
  freeVariablesGlobalTerm (TypeAnnotation e _) = freeVariablesGlobalTerm e
  freeVariablesGlobalTerm (PretypeAnnotation e _) = freeVariablesGlobalTerm e
  convertTerm ux x (TypeAnnotation e σ) = TypeAnnotation (convertTerm ux x e) σ
  convertTerm ux x (PretypeAnnotation e σ) = PretypeAnnotation (convertTerm ux x e) σ
  substituteTerm ux x (TypeAnnotation e σ) = TypeAnnotation (substituteTerm ux x e) σ
  substituteTerm ux x (PretypeAnnotation e σ) = PretypeAnnotation (substituteTerm ux x e) σ
  substituteGlobalTerm ux x (TypeAnnotation e σ) = TypeAnnotation (substituteGlobalTerm ux x e) σ
  substituteGlobalTerm ux x (PretypeAnnotation e σ) = PretypeAnnotation (substituteGlobalTerm ux x e) σ
  reduce (TypeAnnotation e σ) = TypeAnnotation (reduce e) σ
  reduce (PretypeAnnotation e σ) = PretypeAnnotation (reduce e) σ

instance TraverseTerm TermControl where
  traverseTerm fp fp' fv (TermAutoSource e) = TermAutoSource <$> traverseTerm fp fp' fv e
  traverseTerm fp fp' fv (TermManualSource e) = TermManualSource <$> traverseTerm fp fp' fv e

instance TermAlgebra TermControl where
  freeVariablesTermSource (TermAutoSource e) = freeVariablesTermSource e
  freeVariablesTermSource (TermManualSource e) = freeVariablesTermSource e
  freeVariablesGlobalTermSource (TermAutoSource e) = freeVariablesGlobalTermSource e
  freeVariablesGlobalTermSource (TermManualSource e) = freeVariablesGlobalTermSource e
  freeVariablesTerm (TermAutoSource e) = freeVariablesTerm e
  freeVariablesTerm (TermManualSource e) = freeVariablesTerm e
  freeVariablesGlobalTerm (TermAutoSource e) = freeVariablesGlobalTerm e
  freeVariablesGlobalTerm (TermManualSource e) = freeVariablesGlobalTerm e
  convertTerm ux x (TermAutoSource e) = TermAutoSource (convertTerm ux x e)
  convertTerm ux x (TermManualSource e) = TermManualSource (convertTerm ux x e)
  substituteTerm ux x (TermAutoSource e) = TermAutoSource (substituteTerm ux x e)
  substituteTerm ux x (TermManualSource e) = TermManualSource (substituteTerm ux x e)
  substituteGlobalTerm ux x (TermAutoSource e) = TermAutoSource (substituteGlobalTerm ux x e)
  substituteGlobalTerm ux x (TermManualSource e) = TermManualSource (substituteGlobalTerm ux x e)
  reduce (TermAutoSource e) = TermAutoSource (reduce e)
  reduce (TermManualSource e) = TermManualSource (reduce e)

instance Bitraversable phase => TypeAlgebra (Term p phase) where
  freeVariablesType (Term _ e) = foldTermF (bifoldMap go absurd) (bifoldMap mempty go) (bifoldMap mempty go) go'' go go' go' go e
    where
      go = freeVariablesType
      go' = freeVariablesHigherType
      go'' = freeVariablesRgnForType
  freeVariablesGlobalType (Term _ e) = foldTermF (bifoldMap go absurd) (bifoldMap mempty go) (bifoldMap mempty go) go'' go go' go' go e
    where
      go = freeVariablesGlobalType
      go' = freeVariablesGlobalHigherType
      go'' = freeVariablesGlobalRgnForType
  freeVariablesTypeSource (Term _ e) = foldTermF (bifoldMap go absurd) (bifoldMap mempty go) (bifoldMap mempty go) go'' go go' go' go e
    where
      go = freeVariablesTypeSource
      go' = freeVariablesHigherTypeSource
      go'' = freeVariablesRgnForTypeSource
  freeVariablesGlobalTypeSource (Term _ e) = foldTermF (bifoldMap go absurd) (bifoldMap mempty go) (bifoldMap mempty go) go'' go go' go' go e
    where
      go = freeVariablesGlobalTypeSource
      go' = freeVariablesGlobalHigherTypeSource
      go'' = freeVariablesGlobalRgnForTypeSource
  convertType ux x (Term p e) = Term p $ mapTermF (bimap go absurd) (bimap id go) (bimap id go) go'' go go' go' go e
    where
      go = convertType ux x
      go' = convertHigherType ux x
      go'' = convertRgnForType ux x
  substituteType ux x (Term p e) = Term p $ mapTermF (bimap go absurd) (bimap id go) (bimap id go) go'' go go' go' go e
    where
      go = substituteType ux x
      go' = substituteHigherType ux x
      go'' = substituteRgnForType ux x
  substituteGlobalType ux x (Term p e) = Term p $ mapTermF (bimap go absurd) (bimap id go) (bimap id go) go'' go go' go' go e
    where
      go = substituteGlobalType ux x
      go' = substituteGlobalHigherType ux x
      go'' = substituteGlobalRgnForType ux x
  zonkType f (Term p e) =
    Term p
      <$> traverseTermF
        (bitraverse (zonkType f) absurd)
        (bitraverse pure (zonkType f))
        (bitraverse pure (zonkType f))
        (traverseBound (zonkType f) (traverseBound (zonkType f) (zonkType f)))
        (zonkType f)
        (traverseBound (zonkType f) (zonkType f))
        (traverseBound (zonkType f) (zonkType f))
        (zonkType f)
        e
  joinType = joinTypeDefault
  traverseType = traverseTerm pure

instance Bitraversable phase => TypeAlgebra (TermScheme p phase) where
  freeVariablesTypeSource (TermScheme _ e) = case e of
    MonoTerm e -> go e
    TypeAbstraction λ -> go' λ
    where
      go = freeVariablesTypeSource
      go' = freeVariablesSameTypeSource
  freeVariablesGlobalTypeSource (TermScheme _ e) = case e of
    MonoTerm e -> go e
    TypeAbstraction λ -> go' λ
    where
      go = freeVariablesGlobalTypeSource
      go' = freeVariablesGlobalHigherTypeSource
  freeVariablesType (TermScheme _ e) = case e of
    MonoTerm e -> go e
    TypeAbstraction λ -> go' λ
    where
      go = freeVariablesType
      go' = freeVariablesSameType
  freeVariablesGlobalType (TermScheme _ e) = case e of
    MonoTerm e -> go e
    TypeAbstraction λ -> go' λ
    where
      go = freeVariablesGlobalType
      go' = freeVariablesGlobalHigherType
  convertType ux x (TermScheme p e) =
    TermScheme p $
      ( case e of
          MonoTerm e -> MonoTerm (go e)
          TypeAbstraction λ -> TypeAbstraction (go' λ)
      )
    where
      go = convertType ux x
      go' = convertSameType ux x
  substituteType ux x (TermScheme p e) =
    TermScheme p $
      ( case e of
          MonoTerm e -> MonoTerm (go e)
          TypeAbstraction λ -> TypeAbstraction (go' λ)
      )
    where
      go = substituteType ux x
      go' = substituteSameType ux x
  substituteGlobalType ux x (TermScheme p e) =
    TermScheme p $
      ( case e of
          MonoTerm e -> MonoTerm (go e)
          TypeAbstraction λ -> TypeAbstraction (go' λ)
      )
    where
      go = substituteGlobalType ux x
      go' = substituteGlobalSemiDependType ux x
  zonkType f (TermScheme p e) =
    TermScheme <$> pure p
      <*> ( case e of
              MonoTerm e -> MonoTerm <$> zonkType f e
              TypeAbstraction λ -> TypeAbstraction <$> traverseBound (zonkType f) (zonkType f) λ
          )
  joinType = joinTypeDefault
  traverseType = traverseTerm pure

instance Bitraversable phase => TypeAlgebra (TermPattern p phase) where
  freeVariablesType (TermPattern _ pm) = foldTermPatternF (bifoldMap (foldMap go) go) go pm
    where
      go = freeVariablesType
  freeVariablesGlobalType (TermPattern _ pm) = foldTermPatternF (bifoldMap (foldMap go) go) go pm
    where
      go = freeVariablesGlobalType
  convertType ux x (TermPattern p pm) = TermPattern p $ mapTermPatternF (bimap (fmap go) go) go pm
    where
      go = convertType ux x
  freeVariablesTypeSource (TermPattern _ pm) = foldTermPatternF (bifoldMap (foldMap go) go) go pm
    where
      go = freeVariablesTypeSource
  freeVariablesGlobalTypeSource (TermPattern _ pm) = foldTermPatternF (bifoldMap (foldMap go) go) go pm
    where
      go = freeVariablesGlobalTypeSource
  substituteType ux x (TermPattern p pm) = TermPattern p $ mapTermPatternF (bimap (fmap go) go) go pm
    where
      go = substituteType ux x
  substituteGlobalType ux x (TermPattern p pm) = TermPattern p $ mapTermPatternF (bimap (fmap go) go) go pm
    where
      go = substituteGlobalType ux x
  zonkType f (TermPattern p pm) =
    TermPattern p <$> traverseTermPatternF (bitraverse (traverse (zonkType f)) (zonkType f)) (zonkType f) pm
  joinType = joinTypeDefault
  traverseType = traverseTerm pure

instance Bitraversable phase => TypeAlgebra (TermRuntimePattern p phase) where
  freeVariablesType (TermRuntimePattern _ pm) = foldTermRuntimePatternF (bifoldMap (foldMap go) go) go pm
    where
      go = freeVariablesType
  freeVariablesGlobalType (TermRuntimePattern _ pm) = foldTermRuntimePatternF (bifoldMap (foldMap go) go) go pm
    where
      go = freeVariablesGlobalType
  convertType ux x (TermRuntimePattern p pm) = TermRuntimePattern p $ mapTermRuntimePatternF (bimap (fmap go) go) go pm
    where
      go = convertType ux x
  freeVariablesTypeSource (TermRuntimePattern _ pm) = foldTermRuntimePatternF (bifoldMap (foldMap go) go) go pm
    where
      go = freeVariablesTypeSource
  freeVariablesGlobalTypeSource (TermRuntimePattern _ pm) = foldTermRuntimePatternF (bifoldMap (foldMap go) go) go pm
    where
      go = freeVariablesGlobalTypeSource
  substituteType ux x (TermRuntimePattern p pm) = TermRuntimePattern p $ mapTermRuntimePatternF (bimap (fmap go) go) go pm
    where
      go = substituteType ux x
  substituteGlobalType ux x (TermRuntimePattern p pm) = TermRuntimePattern p $ mapTermRuntimePatternF (bimap (fmap go) go) go pm
    where
      go = substituteGlobalType ux x
  zonkType f (TermRuntimePattern p pm) =
    TermRuntimePattern p <$> traverseTermRuntimePatternF (bitraverse (traverse (zonkType f)) (zonkType f)) (zonkType f) pm
  joinType = joinTypeDefault
  traverseType = traverseTerm pure

instance Bitraversable phase => TypeAlgebra (Annotation p phase) where
  freeVariablesType (TypeAnnotation e σ) = freeVariablesType e <> freeVariablesType σ
  freeVariablesType (PretypeAnnotation e σ) = freeVariablesType e <> freeVariablesType σ
  freeVariablesGlobalType (TypeAnnotation e σ) = freeVariablesGlobalType e <> freeVariablesGlobalType σ
  freeVariablesGlobalType (PretypeAnnotation e σ) = freeVariablesGlobalType e <> freeVariablesGlobalType σ
  convertType ux x (TypeAnnotation e σ) = TypeAnnotation (convertType ux x e) (convertType ux x σ)
  convertType ux x (PretypeAnnotation e σ) = PretypeAnnotation (convertType ux x e) (convertType ux x σ)
  freeVariablesTypeSource (TypeAnnotation e σ) = freeVariablesTypeSource e <> freeVariablesTypeSource σ
  freeVariablesTypeSource (PretypeAnnotation e σ) = freeVariablesTypeSource e <> freeVariablesTypeSource σ
  freeVariablesGlobalTypeSource (TypeAnnotation e σ) = freeVariablesGlobalTypeSource e <> freeVariablesGlobalTypeSource σ
  freeVariablesGlobalTypeSource (PretypeAnnotation e σ) = freeVariablesGlobalTypeSource e <> freeVariablesGlobalTypeSource σ

  substituteType ux x (TypeAnnotation e σ) = TypeAnnotation (substituteType ux x e) (substituteType ux x σ)
  substituteType ux x (PretypeAnnotation e σ) = PretypeAnnotation (substituteType ux x e) (substituteType ux x σ)

  substituteGlobalType ux x (TypeAnnotation e σ) = TypeAnnotation (substituteGlobalType ux x e) (substituteGlobalType ux x σ)
  substituteGlobalType ux x (PretypeAnnotation e σ) = PretypeAnnotation (substituteGlobalType ux x e) (substituteGlobalType ux x σ)

  joinType (TypeAnnotation e σ) = TypeAnnotation (joinType e) (joinType σ)
  joinType (PretypeAnnotation e σ) = PretypeAnnotation (joinType e) (joinType σ)

  zonkType = zonkTypeDefault

  traverseType = traverseTerm pure

instance Bitraversable phase => TypeAlgebra (TermControl p phase) where
  freeVariablesType (TermAutoSource e) = freeVariablesType e
  freeVariablesType (TermManualSource e) = freeVariablesType e
  freeVariablesGlobalType (TermAutoSource e) = freeVariablesGlobalType e
  freeVariablesGlobalType (TermManualSource e) = freeVariablesGlobalType e
  convertType ux x (TermAutoSource e) = TermAutoSource $ convertType ux x e
  convertType ux x (TermManualSource e) = TermManualSource $ convertType ux x e
  freeVariablesTypeSource (TermAutoSource e) = freeVariablesTypeSource e
  freeVariablesTypeSource (TermManualSource e) = freeVariablesTypeSource e
  freeVariablesGlobalTypeSource (TermAutoSource e) = freeVariablesGlobalTypeSource e
  freeVariablesGlobalTypeSource (TermManualSource e) = freeVariablesGlobalTypeSource e

  substituteType ux x (TermAutoSource e) = TermAutoSource (substituteType ux x e)
  substituteType ux x (TermManualSource e) = TermManualSource (substituteType ux x e)
  substituteGlobalType ux x (TermAutoSource e) = TermAutoSource (substituteGlobalType ux x e)
  substituteGlobalType ux x (TermManualSource e) = TermManualSource (substituteGlobalType ux x e)

  joinType (TermAutoSource e) = TermAutoSource (joinType e)
  joinType (TermManualSource e) = TermManualSource (joinType e)

  zonkType = zonkTypeDefault

  traverseType = traverseTerm pure

instance BindingsTerm (TermPattern p phase p' v) where
  bindingsTerm (TermPattern _ (PatternVariable x _)) = Set.singleton x
  renameTerm ux x (TermPattern p (PatternVariable x' σ)) | x == x' = TermPattern p $ PatternVariable ux σ
  renameTerm ux x (TermPattern p pm) = TermPattern p $ mapTermPatternF id go pm
    where
      go = renameTerm ux x

instance BindingsTerm (TermRuntimePattern p phase p' v) where
  bindingsTerm (TermRuntimePattern _ (RuntimePatternVariable x _)) = Set.singleton x
  bindingsTerm (TermRuntimePattern _ pm) = foldTermRuntimePatternF mempty go pm
    where
      go = bindingsTerm
  renameTerm ux x (TermRuntimePattern p (RuntimePatternVariable x' σ)) | x == x' = TermRuntimePattern p $ RuntimePatternVariable ux σ
  renameTerm ux x (TermRuntimePattern p pm) = TermRuntimePattern p $ mapTermRuntimePatternF id go pm
    where
      go = renameTerm ux x

applyTerm (Bound (TermPattern _ (PatternVariable x _)) e@(Term p _)) ux =
  reduce $ substituteTerm (TermScheme p (MonoTerm ux)) x e

sourceTermScheme :: TermSchemeInfer p -> TermSchemeSource ()
sourceTermScheme (TermScheme _ e) =
  TermScheme () $
    ( case e of
        MonoTerm e -> MonoTerm (sourceTerm e)
        TypeAbstraction λ -> TypeAbstraction (mapBound id sourceTermScheme λ)
    )

sourceTermAnnotate annotate e σ =
  Term () $
    Annotation $ Source $ annotate (sourceTerm e) σ

-- todo consider not emitting type annotions for lambda bindings
-- as those don't need them (in checking mode)
sourceTerm :: TermInfer p -> TermSource ()
sourceTerm (Term _ e) =
  Term () $ case e of
    TermRuntime e -> TermRuntime $ case e of
      Variable x _ -> Variable x ann
      Alias e λ -> Alias (sourceTerm e) (mapBound sourceTermRuntimePattern sourceTerm λ)
      FunctionApplication e e' (Core σ) -> FunctionApplication (sourceTerm e) (sourceTermAnnotate PretypeAnnotation e' σ) ann
      TupleIntroduction es -> TupleIntroduction (map sourceTerm es)
      ReadReference e -> ReadReference (sourceTerm e)
      WriteReference e e' (Core σ) -> WriteReference (sourceTerm e) (sourceTermAnnotate PretypeAnnotation e' σ) ann
      NumberLiteral n -> NumberLiteral n
      Arithmatic o e e' _ -> Arithmatic o (sourceTerm e) (sourceTerm e') ann
      Relational o e e' (Core σ) _ -> Relational o (sourceTermAnnotate PretypeAnnotation e σ) (sourceTermAnnotate PretypeAnnotation e' σ) ann ann
      BooleanLiteral b -> BooleanLiteral b
      If e e' e'' -> If (sourceTerm e) (sourceTerm e') (sourceTerm e'')
      Extern sym _ _ _ -> Extern sym ann ann ann
      PointerIncrement e e' _ -> PointerIncrement (sourceTerm e) (sourceTerm e') ann
      Continue e -> Continue (sourceTerm e)
      Break e -> Break (sourceTerm e)
      Loop e λ -> Loop (sourceTerm e) (mapBound sourceTermRuntimePattern sourceTerm λ)
    TermSugar e -> TermSugar (fmap sourceTerm e)
    GlobalVariable x _ -> GlobalVariable x ann
    FunctionLiteral λ -> FunctionLiteral (mapBound sourceTermRuntimePattern sourceTerm λ)
    TermErasure (Borrow e λ) -> TermErasure $ Borrow (sourceTerm e) (mapBound id (mapBound sourceTermRuntimePattern sourceTerm) λ)
    TermErasure (IsolatePointer e) -> TermErasure $ IsolatePointer (sourceTerm e)
    TermErasure (Wrap (Core σ) e) -> Annotation $ Source $ PretypeAnnotation (Term () $ TermErasure $ Wrap ann (sourceTerm e)) σ
    TermErasure (Unwrap (Core σ) e) -> TermErasure $ Unwrap ann (sourceTermAnnotate PretypeAnnotation e σ)
    InlineAbstraction λ -> InlineAbstraction (mapBound sourceTermPattern sourceTerm λ)
    InlineApplication e e' (Core σ) -> InlineApplication (sourceTerm e) (sourceTermAnnotate TypeAnnotation e' σ) ann
    Bind e λ -> Bind (sourceTerm e) (mapBound sourceTermPattern sourceTerm λ)
    PolyIntroduction λ -> PolyIntroduction (sourceTermScheme λ)
    PolyElimination e _ (Core σ) ->
      PolyElimination
        (sourceTermAnnotate TypeAnnotation e σ)
        ann
        ann
    Annotation (Core invalid) -> absurd invalid
  where
    ann = Source ()

sourceTermPattern :: TermPatternInfer p -> TermPatternSource ()
sourceTermPattern (TermPattern _ pm) =
  TermPattern () $
    mapTermPatternF (Source . Just . runCore) sourceTermPattern pm

sourceTermRuntimePattern :: TermRuntimePatternInfer p -> TermRuntimePatternSource ()
sourceTermRuntimePattern (TermRuntimePattern _ pm) =
  TermRuntimePattern () $
    mapTermRuntimePatternF (Source . Just . runCore) sourceTermRuntimePattern pm

positionTerm (Term p _) = p

isImport :: TermControlSource p -> Bool
isImport e
  | (TermAutoSource e) <- e = isImportTerm e
  | (TermManualSource e) <- e = isImportTermScheme e
  where
    isImportTerm (Term _ (GlobalVariable _ _)) = True
    isImportTerm (Term _ _) = False
    isImportTermScheme (TermScheme _ (MonoTerm e)) = isImportTerm e
    isImportTermScheme (TermScheme _ (TypeAbstraction (Bound _ e))) = isImportTermScheme e
