module Ast.Term.Algebra where

import Ast.Common.Variable
import Ast.Term.Runtime
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))

data TermMetaPatternF σ pm
  = PatternVariable TermIdentifier σ σ
  deriving (Show)

data TermSugar σ e
  = Not e
  | And e e
  | Or e e
  | Do e e
  | If e e e σ
  deriving (Show, Functor)

data TermErasure σauto λσe e
  = IsolatePointer e
  | Cast e σauto
  deriving (Show)

data TermF ann θ σ σauto λσe λe λrun_e e
  = TermRuntime (TermRuntime θ σauto σauto σauto λrun_e e)
  | TermErasure (TermErasure σauto λσe e)
  | TermSugar (TermSugar σauto e)
  | Annotation ann
  | GlobalVariable TermGlobalIdentifier θ
  | FunctionLiteral λrun_e σ σ
  | InlineAbstraction λe
  | InlineApplication e e
  | Bind e λe
  | PolyIntroduction λσe
  | PolyElimination e θ
  deriving (Show)

traverseTermMetaPatternF ::
  Applicative m =>
  (σ -> m σ') ->
  (pm -> m pm') ->
  TermMetaPatternF σ pm ->
  m (TermMetaPatternF σ' pm')
traverseTermMetaPatternF f _ pm = case pm of
  PatternVariable x π σ -> pure PatternVariable <*> pure x <*> f π <*> f σ

foldTermMetaPatternF f h = getConst . traverseTermMetaPatternF (Const . f) (Const . h)

mapTermMetaPatternF f h = runIdentity . traverseTermMetaPatternF (Identity . f) (Identity . h)

traverseTermSugar ::
  Applicative m =>
  (σ -> m σ') ->
  (e -> m e') ->
  TermSugar σ e ->
  m (TermSugar σ' e')
traverseTermSugar g f e = case e of
  Not e -> pure Not <*> f e
  And e e' -> pure And <*> f e <*> f e'
  Or e e' -> pure Or <*> f e <*> f e'
  Do e e' -> pure Do <*> f e <*> f e'
  If e e' e'' σ -> pure If <*> f e <*> f e' <*> f e'' <*> g σ

mapTermSugar f g = runIdentity . traverseTermSugar (Identity . f) (Identity . g)

traverseTermF ::
  Applicative m =>
  (ann -> m ann') ->
  (θ -> m θ') ->
  (σ -> m σ') ->
  (σauto -> m σauto') ->
  (λσe -> m λσe') ->
  (λe -> m λe') ->
  (λrun_e -> m λrun_e') ->
  (e -> m e') ->
  TermF ann θ σ σauto λσe λe λrun_e e ->
  m (TermF ann' θ' σ' σauto' λσe' λe' λrun_e' e')
traverseTermF y d a z k h m i e =
  case e of
    TermRuntime e -> pure TermRuntime <*> traverseTermRuntime d z z z m i e
    TermSugar e -> pure TermSugar <*> traverseTermSugar z i e
    Annotation e -> pure Annotation <*> y e
    GlobalVariable x θ -> pure GlobalVariable <*> pure x <*> d θ
    FunctionLiteral λ τ π -> pure FunctionLiteral <*> m λ <*> a τ <*> a π
    TermErasure (IsolatePointer e) -> TermErasure <$> (IsolatePointer <$> i e)
    TermErasure (Cast e σ) -> TermErasure <$> (Cast <$> i e <*> z σ)
    InlineAbstraction λ -> pure InlineAbstraction <*> h λ
    InlineApplication e1 e2 -> pure InlineApplication <*> i e1 <*> i e2
    Bind e λ -> pure Bind <*> i e <*> h λ
    PolyIntroduction λ -> pure PolyIntroduction <*> k λ
    PolyElimination e θ -> pure PolyElimination <*> i e <*> d θ

foldTermF d j z b a f r h = getConst . traverseTermF (Const . d) (Const . j) (Const . z) (Const . b) (Const . a) (Const . f) (Const . r) (Const . h)

mapTermF d j z b a f r h = runIdentity . traverseTermF (Identity . d) (Identity . j) (Identity . z) (Identity . b) (Identity . a) (Identity . f) (Identity . r) (Identity . h)
