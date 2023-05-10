module Ast.Term.Runtime where

import Ast.Common.Variable
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Misc.Symbol

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
  = Variable TermIdentifier θ σerase
  | Alias e λe
  | Case e σ [λe] σerase
  | Extern Symbol σ σerase σ
  | FunctionApplication e e σ
  | TupleIntroduction [e]
  | ReadReference e
  | WriteReference e e σ
  | NumberLiteral Integer σerase
  | Arithmatic Arithmatic e e s
  | Relational Relational e e σ s
  | BooleanLiteral Bool
  | PointerIncrement e e σ
  | Continue e σerase
  | Break e σerase
  | Loop e λe
  deriving (Show)

data TermPatternF σ pm
  = RuntimePatternVariable TermIdentifier σ
  | RuntimePatternTuple [pm]
  | RuntimePatternBoolean Bool
  deriving (Show)

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
    Variable x θ σ -> pure Variable <*> pure x <*> d θ <*> y σ
    Alias e λ -> pure Alias <*> i e <*> g λ
    Case e σ λs σ' -> pure Case <*> i e <*> f σ <*> traverse g λs <*> y σ'
    Extern sm σ σ'' σ' -> pure Extern <*> pure sm <*> f σ <*> y σ'' <*> f σ'
    FunctionApplication e1 e2 σ -> pure FunctionApplication <*> i e1 <*> i e2 <*> f σ
    TupleIntroduction es -> pure TupleIntroduction <*> traverse i es
    ReadReference e -> pure ReadReference <*> i e
    WriteReference e e' σ -> pure WriteReference <*> i e <*> i e' <*> f σ
    NumberLiteral n σ -> pure NumberLiteral <*> pure n <*> y σ
    Arithmatic o e e' κ -> pure Arithmatic <*> pure o <*> i e <*> i e' <*> h κ
    Relational o e e' σ κ -> pure Relational <*> pure o <*> i e <*> i e' <*> f σ <*> h κ
    BooleanLiteral b -> pure BooleanLiteral <*> pure b
    PointerIncrement e e' σ -> pure PointerIncrement <*> i e <*> i e' <*> f σ
    Continue e σ -> pure Continue <*> i e <*> y σ
    Break e σ -> pure Break <*> i e <*> y σ
    Loop e λ -> pure Loop <*> i e <*> g λ

traverseTermPatternF ::
  Applicative m =>
  (σ -> m σ') ->
  (pm -> m pm') ->
  TermPatternF σ pm ->
  m (TermPatternF σ' pm')
traverseTermPatternF f h pm = case pm of
  RuntimePatternVariable x σ -> pure RuntimePatternVariable <*> pure x <*> f σ
  RuntimePatternTuple pms -> pure RuntimePatternTuple <*> traverse h pms
  RuntimePatternBoolean b -> pure (RuntimePatternBoolean b)

foldTermPatternF f h = getConst . traverseTermPatternF (Const . f) (Const . h)

mapTermPatternF f h = runIdentity . traverseTermPatternF (Identity . f) (Identity . h)
