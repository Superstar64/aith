module Codegen where

import qualified C.Ast as C
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (State, evalState, get, put)
import Control.Monad.Trans.Writer (WriterT (..), runWriterT, tell)
import Core.Ast.Common
import Core.Ast.RuntimePattern
import Core.Ast.Term
import Data.Functor.Identity (Identity (..))
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Decorate
import Misc.Identifier
import Misc.Path
import Misc.Silent
import Misc.Symbol
import Misc.Variables (Variables)
import qualified Misc.Variables as Variables
import Module

external (CoreTerm _ (Extern _ _ sm _ _)) = [sm]
external (CoreTerm _ e) = foldTerm external go go bound bound bound bound bound e
  where
    go = const mempty
    bound (Bound _ e) = external e

newtype Codegen a = Codegen (State (Variables (), Map Identifier String) a) deriving (Functor, Applicative, Monad)

runCodegen (Codegen x) symbols = evalState x (Variables.fromList $ go <$> symbols, mempty)
  where
    go (Symbol x) = (Identifier x, ())

lookupVariable x = do
  (_, mapping) <- Codegen get
  pure $ mapping ! x

nameArgument :: RuntimePattern Decorate p p -> Codegen String
nameArgument (CoreRuntimePattern _ _ (RuntimePatternVariable x _)) = do
  (vars, mapping) <- Codegen get
  let (Identifier name) = Variables.fresh vars x
  Codegen $ put (vars <> Variables.singleton x (), Map.insert x name mapping)
  pure name

compileTerm :: Term Decorate p -> WriterT [C.Statement] Codegen C.Expression
compileTerm (CoreTerm _ (Variable _ x)) = do
  x' <- lift $ lookupVariable x
  pure $ C.Variable x'
compileTerm (CoreTerm _ (Extern (Decorate (Identity dσ)) (Decorate dτs) (Symbol name) _ _)) = do
  tell [C.ForwardDeclare dσ name dτs]
  pure $ C.Variable name
compileTerm (CoreTerm _ (FunctionApplication (Decorate (Identity dσ)) (Decorate dτs) e1 e2s)) = do
  e1' <- compileTerm e1
  e2s' <- traverse compileTerm e2s
  pure $ C.Call dσ dτs e1' e2s'
compileTerm (CoreTerm _ (Alias e1 (Bound pm@(CoreRuntimePattern (Decorate (Identity dσ)) _ _) e2))) = do
  e1' <- compileTerm e1
  x <- lift $ nameArgument pm
  tell $ [C.VariableDeclaration dσ x e1']
  compileTerm e2
compileTerm (CoreTerm _ (FunctionLiteral _ _ _)) = error "function literal inside runtime"
compileTerm (CoreTerm _ (MacroAbstraction (Decorate i) _)) = absurd i
compileTerm (CoreTerm _ (TypeAbstraction (Decorate i) _)) = absurd i
compileTerm (CoreTerm _ (KindAbstraction (Decorate i) _)) = absurd i
compileTerm (CoreTerm _ (MacroApplication (Decorate i) _ _)) = absurd i
compileTerm (CoreTerm _ (TypeApplication (Decorate i) _ _)) = absurd i
compileTerm (CoreTerm _ (KindApplication (Decorate i) _ _)) = absurd i
compileTerm (CoreTerm _ (OfCourseIntroduction (Decorate i) _)) = absurd i
compileTerm (CoreTerm _ (Bind (Decorate i) _ _)) = absurd i
compileTerm (CoreTerm _ (ErasedQualifiedAssume (Decorate i) _ _)) = absurd i
compileTerm (CoreTerm _ (ErasedQualifiedCheck (Decorate i) _)) = absurd i

compileFunctionLiteral :: Symbol -> Term Decorate p -> Codegen C.FunctionDefinition
compileFunctionLiteral (Symbol name) (CoreTerm _ (FunctionLiteral (Decorate (Identity dσ)) _ (Bound pms e))) = do
  arguments <- traverse nameArgument pms
  let argumentTypes = map (\(CoreRuntimePattern (Decorate σ) _ _) -> runIdentity σ) pms
  (result, depend) <- runWriterT (compileTerm e)
  pure $ C.FunctionDefinition dσ name (zip argumentTypes arguments) (depend ++ [C.Return result])
compileFunctionLiteral _ _ = error "top level non function literal"

compileModule path (CoreModule code) = Map.toList code >>= compileItem
  where
    compileItem (x, (Module items)) = compileModule (path ++ [x]) items
    compileItem (x, (Global (Text e))) = [run $ compileFunctionLiteral manging decorated]
      where
        manging = mangle $ Path path x
        decorated = runDecorate $ decorateTerm e
        run c = runCodegen c (external e)
    compileItem (_, (Global (Inline _))) = []
    compileItem (_, (Global (Import _ _))) = []
