module Codegen where

import qualified C.Ast as C
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (State, evalState, get, put)
import Control.Monad.Trans.Writer (WriterT (..), runWriterT, tell)
import Core.Ast.Common
import Core.Ast.Kind (Kind)
import Core.Ast.RuntimePattern
import Core.Ast.Term
import Core.Ast.Type
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Decorate
import Misc.Identifier
import Misc.Path
import Misc.Symbol
import Misc.Util
import Module

type CStatement = C.Statement (C.Representation C.RepresentationFix)

type CExpression = C.Expression (C.Representation C.RepresentationFix)

class External e where
  external :: e -> Set String

instance External (Term p) where
  external = foldTerm external

instance (External a, External b) => External (Either a b) where
  external (Left a) = external a
  external (Right b) = external b

instance External b => External (Bound a b) where
  external (Bound _ b) = external b

instance (External a, External b) => External (a, b) where
  external (a, b) = external a <> external b

instance External (Type p) where
  external = mempty

instance External (Kind p) where
  external = mempty

instance External Identifier where
  external = mempty

instance External Symbol where
  external (Symbol sm) = Set.singleton sm

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

compilePattern :: PatternDecorated p -> CExpression -> Codegen ([CStatement])
compilePattern (PatternDecorated dσ _ (RuntimePatternVariable x@(Identifier base) _)) target = do
  (vars, mapping) <- Codegen get
  let name = fresh vars base
  Codegen $ put (Set.insert name vars, Map.insert x name mapping)
  pure [C.VariableDeclaration dσ name target]
compilePattern (PatternDecorated dσ _ (RuntimePatternPair pm1 pm2)) target = do
  new <- temporary
  let initial = C.VariableDeclaration dσ new target
  pm1' <- compilePattern pm1 (C.Member (C.Variable new) "_0")
  pm2' <- compilePattern pm2 (C.Member (C.Variable new) "_1")
  pure $ initial : pm1' ++ pm2'

compileTerm :: TermDecerated p -> WriterT [CStatement] Codegen CExpression
compileTerm (TermDecerated _ (Variable x)) = do
  x' <- lift $ lookupVariable x
  pure $ C.Variable x'
compileTerm (TermDecerated _ (Extern dσ dτ (Symbol name) _ _)) = do
  tell [C.ForwardDeclare dτ name [dσ]]
  pure $ C.Variable name
compileTerm (TermDecerated _ (FunctionApplication dσ dτ e1 e2)) = do
  e1' <- compileTerm e1
  e2' <- compileTerm e2
  pure $ C.Call dσ [dτ] e1' [e2']
compileTerm (TermDecerated _ (Alias e1 (Bound pm e2))) = do
  e1' <- compileTerm e1
  bindings <- lift $ compilePattern pm e1'
  tell $ bindings
  compileTerm e2
compileTerm (TermDecerated _ (RuntimePairIntroduction dσ e1 e2)) = do
  e1' <- compileTerm e1
  e2' <- compileTerm e2
  pure $ C.CompoundLiteral dσ [e1', e2']
compileTerm (TermDecerated _ (ReadReference dσ e)) = do
  e' <- compileTerm e
  pure $ C.Dereference dσ e'
compileTerm (TermDecerated _ (LocalRegion dσ (Bound () ((), (e1, (Bound pm e2)))))) = do
  e1' <- compileTerm e1
  stack <- lift temporary
  tell $ [C.VariableDeclaration dσ stack e1']
  binding <- lift $ compilePattern pm (C.Address $ C.Variable stack)
  tell $ binding
  compileTerm e2
compileTerm (TermDecerated _ (FunctionLiteral _ _)) = error "function literal inside runtime"

compileFunctionLiteralImpl :: Symbol -> TermDecerated p -> Codegen (C.Global (C.Representation C.RepresentationFix))
compileFunctionLiteralImpl (Symbol name) (TermDecerated _ (FunctionLiteral dσ (Bound pm@(PatternDecorated argumentType _ _) e))) = do
  argumentName <- temporary
  bindings <- compilePattern pm (C.Variable argumentName)
  let arguments = [(argumentType, argumentName)]
  (result, depend) <- runWriterT (compileTerm e)
  let body = bindings ++ depend ++ [C.Return result]
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
