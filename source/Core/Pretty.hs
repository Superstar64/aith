module Core.Pretty where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (State, get, put, runState)
import Control.Monad.Trans.Writer (WriterT, runWriterT, tell)
import Core.Ast
import Misc.Identifier

parens True e = tell "(" >> e >> tell ")"
parens False e = e

brace :: WriterT String (State Int) () -> WriterT String (State Int) ()
brace e = do
  indention <- lift get
  tell " {"
  tell "\n"
  sequence $ replicate (indention + 1) (tell "\t")
  lift (put $ indention + 1)
  e
  lift (put indention)
  tell "\n"
  sequence $ replicate indention (tell "\t")
  tell "}"

braceMini e = do
  tell " {"
  e
  tell " }"

prettyTerm' (Variable (Identifier x)) = tell x
prettyTerm' (MacroAbstraction (Identifier x) l σ e) = do
  tell "λ["
  prettyLinear l
  tell "]("
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
prettyTerm' (LinearAbstraction (Identifier x) e) = do
  tell "Λ["
  tell x
  tell "]"
  brace (prettyTerm e)
prettyTerm' (LinearApplication e l) = do
  prettyTerm e
  tell "["
  prettyLinear l
  tell "]"

prettyTerm (CoreTerm Internal e) = prettyTerm' e

data TypePrecedence = BottomType | ArrowType deriving (Eq, Ord)

prettyType' _ (TypeVariable (Identifier x)) = tell x
prettyType' d (Macro l σ τ) = parens (d > BottomType) $ do
  prettyType ArrowType σ
  tell " -["
  prettyLinear l
  tell "]> "
  prettyType BottomType τ
prettyType' _ (Forall (Identifier x) κ σ) = do
  tell "∀"
  tell "<"
  tell x
  tell ":"
  prettyKind κ
  tell ">"
  braceMini (prettyType BottomType σ)
prettyType' _ (LinearForall (Identifier x) σ) = do
  tell "∀"
  tell "["
  tell x
  tell "]"
  braceMini (prettyType BottomType σ)

prettyType d (CoreType Internal σ) = prettyType' d σ

prettyLinear' Linear = tell "%linear"
prettyLinear' Unrestricted = tell "%unrestricted"
prettyLinear' (LinearVariable (Identifier x)) = tell x

prettyLinear (CoreMultiplicity Internal l) = prettyLinear' l

data StagePrecedence = BottomStage | ArrowStage deriving (Eq, Ord)

prettyStage _ Runtime = tell "%runtime"
prettyStage d (StageMacro s s') = parens (d > BottomStage) $ do
  prettyStage ArrowStage s
  tell " -> "
  prettyStage BottomStage s'

prettyKind' (Type l s) = do
  prettyLinear l
  tell " @ "
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
