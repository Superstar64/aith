module Core.Pretty where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (State, get, put, runState)
import Control.Monad.Trans.Writer (WriterT, runWriterT, tell)
import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.Pattern
import Core.Ast.Stage
import Core.Ast.Term
import Core.Ast.Type
import Core.Ast.TypePattern
import Misc.Identifier

newtype Printer a = Printer (WriterT String (State Int) a) deriving (Functor, Applicative, Monad)

class Pretty a where
  pretty :: a -> Printer ()

token = Printer . tell

keyword name = Printer $ tell (('%' : name))

identfier (Identifier name) = Printer $ tell name

parens True e = token "(" >> e >> token ")"
parens False e = e

space = Printer $ tell " "

kspace = Printer $ tell " "

line = do
  indention <- Printer $ lift get
  Printer $ tell "\n"
  Printer $ sequence $ replicate indention (tell "\t")
  pure ()

lambda e = do
  indention <- Printer $ lift get
  space
  token "{"
  Printer $ lift (put $ indention + 1)
  line
  e
  Printer $ lift (put indention)
  line
  token "}"

lambdaMini e = do
  space
  token "{"
  e
  token "}"

prettyTerm' (Variable x) = identfier x
prettyTerm' (MacroAbstraction pm e) = do
  token "λ"
  pretty pm
  lambda (prettyTerm e)
prettyTerm' (MacroApplication e1 e2) = do
  prettyTerm e1
  token "("
  prettyTerm e2
  token ")"
prettyTerm' (TypeAbstraction pm e) = do
  token "Λ"
  token "<"
  pretty pm
  token ">"
  lambda (prettyTerm e)
prettyTerm' (TypeApplication e σ) = do
  prettyTerm e
  token "<"
  pretty σ
  token ">"
prettyTerm' (OfCourseIntroduction e) = do
  token "!"
  prettyTerm e
prettyTerm' (Bind pm e1 e2) = do
  keyword "let"
  kspace
  pretty pm
  space
  token "="
  space
  prettyTerm e1
  token ";"
  line
  prettyTerm e2

prettyTerm (CoreTerm Internal e) = prettyTerm' e

instance (i ~ Internal) => Pretty (Term i) where
  pretty = prettyTerm

data PatternPrecedence = BottomPattern | OfCoursePattern deriving (Eq, Ord)

prettyPattern' d (PatternVariable x σ) = parens (d > BottomPattern) $ do
  identfier x
  token ":"
  pretty σ
prettyPattern' d (PatternOfCourse pm) = parens (d > OfCoursePattern) $ do
  token "!"
  prettyPattern OfCoursePattern pm

prettyPattern d (CorePattern Internal pm) = prettyPattern' d pm

instance (i ~ Internal, σ ~ TypeInternal) => Pretty (Pattern σ i) where
  pretty = prettyPattern BottomPattern

data TypePrecedence = BottomType | InnerType deriving (Eq, Ord)

prettyType' _ (TypeVariable x) = identfier x
prettyType' d (Macro σ τ) = parens (d > BottomType) $ do
  prettyType InnerType σ
  space
  token "->"
  space
  prettyType BottomType τ
prettyType' _ (Forall pm σ) = do
  token "∀"
  token "<"
  pretty pm
  token ">"
  lambdaMini (prettyType BottomType σ)
prettyType' _ (OfCourse σ) = do
  token "!"
  prettyType InnerType σ
prettyType' _ (TypeConstruction σ τ) = do
  prettyType InnerType σ
  token "("
  prettyType BottomType τ
  token ")"
prettyType' _ (TypeOperator pm σ) = do
  token "λ"
  pretty pm
  lambdaMini (prettyType BottomType σ)

prettyType d (CoreType Internal σ) = prettyType' d σ

instance (i ~ Internal) => Pretty (Type i) where
  pretty = prettyType BottomType

prettyTypePattern' (TypePatternVariable x κ) = do
  identfier x
  token ":"
  pretty κ

prettyTypePattern (CoreTypePattern Internal pm) = prettyTypePattern' pm

instance (i ~ Internal, κ ~ KindInternal) => Pretty (TypePattern κ i) where
  pretty = prettyTypePattern

prettyLinear' Linear = keyword "linear"
prettyLinear' Unrestricted = keyword "unrestricted"

prettyLinear (CoreMultiplicity Internal l) = prettyLinear' l

instance (i ~ Internal) => Pretty (Multiplicity i) where
  pretty = prettyLinear

data StagePrecedence = BottomStage | ArrowStage | OfCourseStage deriving (Eq, Ord)

prettyStage _ Runtime = keyword "runtime"
prettyStage d (StageMacro s s') = parens (d > BottomStage) $ do
  prettyStage ArrowStage s
  space
  token "~>"
  space
  prettyStage BottomStage s'
prettyStage d (StageOfCourse s) = parens (d > OfCourseStage) $ do
  token "!"
  prettyStage OfCourseStage s

instance Pretty Stage where
  pretty = prettyStage BottomStage

data KindPrecedence = BottomKind | ArrowKind deriving (Eq, Ord)

prettyKind' _ (Type s) = do
  pretty s
prettyKind' d (Higher κ κ') = parens (d > BottomKind) $ do
  prettyKind ArrowKind κ
  space
  token "->"
  space
  prettyKind BottomKind κ'

prettyKind d (CoreKind Internal κ) = prettyKind' d κ

instance (i ~ Internal) => Pretty (Kind i) where
  pretty = prettyKind BottomKind

showItem e = s
  where
    run (Printer p) = p
    (((), s), _) = runState (runWriterT $ run $ pretty e) 0
