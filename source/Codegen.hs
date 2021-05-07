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
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (for)
import Decorate
import Misc.Identifier
import Misc.Path
import Misc.Silent
import Misc.Symbol
import Misc.Util
import Module

type CStatement = C.Statement (C.Representation C.RepresentationFix)

type CExpression = C.Expression (C.Representation C.RepresentationFix)

external (CoreTerm _ (Extern _ _ (Symbol sm) _ _)) = Set.singleton sm
external (CoreTerm _ e) = foldTerm external go go bound bound bound bound bound go e
  where
    go = const mempty
    bound (Bound _ e) = external e

newtype Codegen a = Codegen (State (Set String, Map Identifier String) a) deriving (Functor, Applicative, Monad)

runCodegen (Codegen x) symbols = evalState x (symbols, mempty)

lookupVariable x = do
  (_, mapping) <- Codegen get
  pure $ mapping ! x

temporary = do
  (vars, mapping) <- Codegen get
  let name = fresh vars "_"
  Codegen $ put (vars <> Set.singleton name, mapping)
  pure name

compilePattern :: RuntimePattern Decorate p p -> CExpression -> Codegen ([CStatement])
compilePattern (CoreRuntimePattern (Decorate (Identity dσ)) _ (RuntimePatternVariable x@(Identifier base) _)) target = do
  (vars, mapping) <- Codegen get
  let name = fresh vars base
  Codegen $ put (Set.insert name vars, Map.insert x name mapping)
  pure [C.VariableDeclaration dσ name target]
compilePattern (CoreRuntimePattern (Decorate (Identity dσ)) _ (RuntimePatternPair pm1 pm2)) target = do
  new <- temporary
  let initial = C.VariableDeclaration dσ new target
  pm1' <- compilePattern pm1 (C.Member (C.Variable new) "_0")
  pm2' <- compilePattern pm2 (C.Member (C.Variable new) "_1")
  pure $ initial : pm1' ++ pm2'

compileTerm :: Term Decorate p -> WriterT [CStatement] Codegen CExpression
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
compileTerm (CoreTerm _ (Alias e1 (Bound pm e2))) = do
  e1' <- compileTerm e1
  bindings <- lift $ compilePattern pm e1'
  tell $ bindings
  compileTerm e2
compileTerm (CoreTerm _ (RuntimePairIntroduction (Decorate (Identity dσ)) e1 e2)) = do
  e1' <- compileTerm e1
  e2' <- compileTerm e2
  pure $ C.CompoundLiteral dσ [e1', e2']
compileTerm (CoreTerm _ (FunctionLiteral _ _)) = error "function literal inside runtime"
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
compileTerm (CoreTerm _ (Pack (Decorate i) _ _)) = absurd i
compileTerm (CoreTerm _ (Unpack (Decorate i) _)) = absurd i

compileFunctionLiteralImpl :: Symbol -> Term Decorate p -> Codegen (C.Global (C.Representation C.RepresentationFix))
compileFunctionLiteralImpl (Symbol name) (CoreTerm _ (FunctionLiteral (Decorate (Identity dσ)) (Bound pms e))) = do
  let argumentTypes = map (\(CoreRuntimePattern (Decorate σ) _ _) -> runIdentity σ) pms
  heading <- for pms $ \pm -> do
    new <- temporary
    bindings <- compilePattern pm (C.Variable new)
    pure (new, bindings)
  let (argumentNames, bindings) = unzip heading
  let arguments = zip argumentTypes argumentNames
  (result, depend) <- runWriterT (compileTerm e)
  let body = concat bindings ++ depend ++ [C.Return result]
  pure $ C.FunctionDefinition dσ name arguments body
compileFunctionLiteralImpl _ _ = error "top level non function literal"

compileFunctionLiteral path name e = [run $ compileFunctionLiteralImpl manging decorated]
  where
    manging = mangle $ Path path name
    decorated = runDecorate $ decorateTerm e
    run c = runCodegen c (external e)

compileModule path (CoreModule code) = Map.toList code >>= (uncurry $ compileItem path)

compileItem path name (Module items) = compileModule (path ++ [name]) items
compileItem path name (Global (Text _ e)) = compileFunctionLiteral path name e
compileItem _ _ (Global (Inline _ _)) = []
compileItem _ _ (Global (Import _ _)) = []
compileItem _ _ (Global (Synonym _)) = []
