module Core.Pretty where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (State, get, put, runState)
import Control.Monad.Trans.Writer (WriterT, runWriterT, tell)
import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.Pattern
import Core.Ast.Stage
import Core.Ast.StagePattern
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
  token "Λ<"
  pretty pm
  token ">"
  lambda (prettyTerm e)
prettyTerm' (TypeApplication e σ) = do
  prettyTerm e
  token "<"
  pretty σ
  token ">"
prettyTerm' (StageAbstraction pm e) = do
  token "Λ@"
  pretty pm
  lambda (prettyTerm e)
prettyTerm' (StageApplication e s) = do
  prettyTerm e
  token "@"
  token "("
  prettyStage s
  token ")"
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

instance Pretty TermInternal where
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

instance Pretty (Pattern TypeInternal Internal) where
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
  token "∀<"
  pretty pm
  token ">"
  lambdaMini (prettyType BottomType σ)
prettyType' _ (StageForall pm σ) = do
  token "∀@"
  pretty pm
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

instance Pretty TypeInternal where
  pretty = prettyType BottomType

prettyTypePattern' (TypePatternVariable x κ) = do
  identfier x
  token ":"
  pretty κ

prettyTypePattern (CoreTypePattern Internal pm) = prettyTypePattern' pm

instance Pretty (TypePattern KindInternal Internal) where
  pretty = prettyTypePattern

prettyStagePattern' (StagePatternVariable x) = identfier x

prettyStagePattern (CoreStagePattern Internal pm) = prettyStagePattern' pm

instance Pretty StagePatternInternal where
  pretty = prettyStagePattern

prettyLinear' Linear = keyword "linear"
prettyLinear' Unrestricted = keyword "unrestricted"

prettyLinear (CoreMultiplicity Internal l) = prettyLinear' l

instance Pretty MultiplicityInternal where
  pretty = prettyLinear

prettyStage' (StageVariable x) = identfier x
prettyStage' Runtime = keyword "runtime"
prettyStage' Meta = keyword "meta"

prettyStage (CoreStage Internal s) = prettyStage' s

instance Pretty StageInternal where
  pretty = prettyStage

data KindPrecedence = BottomKind | ArrowKind deriving (Eq, Ord)

prettyKind' _ (Type s) = do
  keyword "type"
  space
  pretty s
prettyKind' d (Higher κ κ') = parens (d > BottomKind) $ do
  prettyKind ArrowKind κ
  space
  token "->"
  space
  prettyKind BottomKind κ'

prettyKind d (CoreKind Internal κ) = prettyKind' d κ

instance Pretty KindInternal where
  pretty = prettyKind BottomKind

showItem e = s
  where
    run (Printer p) = p
    (((), s), _) = runState (runWriterT $ run $ pretty e) 0
