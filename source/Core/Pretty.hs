module Core.Pretty where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (State, get, put, runState)
import Control.Monad.Trans.Writer (WriterT, runWriterT, tell)
import Core.Ast
import Misc.Identifier

parens True e = tell "(" >> e >> tell ")"
parens False e = e

line = do
  indention <- lift get
  tell "\n"
  sequence $ replicate indention (tell "\t")

brace :: WriterT String (State Int) () -> WriterT String (State Int) ()
brace e = do
  indention <- lift get
  tell " {"
  lift (put $ indention + 1)
  line
  e
  lift (put indention)
  line
  tell "}"

braceMini e = do
  tell " {"
  e
  tell " }"

prettyTerm' (Variable (Identifier x)) = tell x
prettyTerm' (MacroAbstraction (Identifier x) σ e) = do
  tell "λ("
  tell x
  tell " : "
  prettyType BottomType σ
  tell ")"
  brace (prettyTerm e)
prettyTerm' (MacroApplication e1 e2) = do
  prettyTerm e1
  tell "("
  prettyTerm e2
  tell ")"
prettyTerm' (TypeAbstraction (Identifier x) κ e) = do
  tell "Λ<"
  tell x
  tell " : "
  prettyKind κ
  tell ">"
  brace (prettyTerm e)
prettyTerm' (TypeApplication e σ) = do
  prettyTerm e
  tell "<"
  prettyType BottomType σ
  tell ">"
prettyTerm' (OfCourseIntroduction e) = do
  tell "!"
  prettyTerm e
prettyTerm' (OfCourseElimination (Identifier x) e1 e2) = do
  tell "%let"
  tell "!"
  tell x
  tell " = "
  prettyTerm e1
  tell ";"
  line
  prettyTerm e2

prettyTerm (CoreTerm Internal e) = prettyTerm' e

data TypePrecedence = BottomType | ArrowType | OfCourseType deriving (Eq, Ord)

prettyType' _ (TypeVariable (Identifier x)) = tell x
prettyType' d (Macro σ τ) = parens (d > BottomType) $ do
  prettyType ArrowType σ
  tell " -> "
  prettyType BottomType τ
prettyType' _ (Forall (Identifier x) κ σ) = do
  tell "∀"
  tell "<"
  tell x
  tell ":"
  prettyKind κ
  tell ">"
  braceMini (prettyType BottomType σ)
prettyType' d (OfCourse σ) = parens (d > OfCourseType) $ do
  tell "!"
  prettyType OfCourseType σ

prettyType d (CoreType Internal σ) = prettyType' d σ

prettyLinear' Linear = tell "%linear"
prettyLinear' Unrestricted = tell "%unrestricted"

prettyLinear (CoreMultiplicity Internal l) = prettyLinear' l

data StagePrecedence = BottomStage | ArrowStage deriving (Eq, Ord)

prettyStage _ Runtime = tell "%runtime"
prettyStage d (StageMacro s s') = parens (d > BottomStage) $ do
  prettyStage ArrowStage s
  tell " -> "
  prettyStage BottomStage s'

prettyKind' (Type s) = do
  prettyStage BottomStage s

prettyKind (CoreKind Internal κ) = prettyKind' κ

showTerm e = s
  where
    (((), s), _) = runState (runWriterT (prettyTerm e)) 0

showType σ = s
  where
    (((), s), _) = runState (runWriterT (prettyType BottomType σ)) 0

showKind κ = s
  where
    (((), s), _) = runState (runWriterT (prettyKind κ)) 0
