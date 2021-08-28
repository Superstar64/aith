module Codegen where

import qualified C.Ast as C
import Control.Monad.State (State, evalState, get, put)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (WriterT (..), runWriterT, tell)
import Data.Set (Set)
import qualified Data.Set as Set
import Decorate
import Language.Ast.Common hiding (fresh)
import Language.Ast.Kind (KindRuntime (..))
import Language.Ast.Term
import Misc.MonoidMap (Map, (!))
import qualified Misc.MonoidMap as Map
import Misc.Symbol
import Misc.Util

newtype Codegen a = Codegen (State (Set String, Map TermIdentifier String) a) deriving (Functor, Applicative, Monad)

runCodegen (Codegen x) symbols = evalState x (symbols, mempty)

lookupVariable x = do
  (_, mapping) <- Codegen get
  pure $ mapping ! x

temporary = do
  (vars, mapping) <- Codegen get
  let name = fresh vars "_"
  Codegen $ put (vars <> Set.singleton name, mapping)
  pure name

ctype :: TypeDecorated -> C.Representation C.RepresentationFix
ctype (TypeDecorated PointerRep) = C.Pointer
ctype (TypeDecorated (StructRep σs)) = C.Struct $ C.RepresentationFix $ fmap ctype σs

compilePattern :: PatternDecorated TypeDecorated -> C.Expression TypeDecorated -> Codegen ([C.Statement TypeDecorated])
compilePattern (PatternDecorated σ (PatternVariable x@(TermIdentifier base) _)) target = do
  (vars, mapping) <- Codegen get
  let name = fresh vars base
  Codegen $ put (Set.insert name vars, Map.insert x name mapping)
  pure [C.VariableDeclaration σ name target]
compilePattern (PatternDecorated σ (RuntimePatternPair pm1 pm2)) target = do
  new <- temporary
  let initial = C.VariableDeclaration σ new target
  pm1' <- compilePattern pm1 (C.Member (C.Variable new) "_0")
  pm2' <- compilePattern pm2 (C.Member (C.Variable new) "_1")
  pure $ initial : pm1' ++ pm2'

compileTerm :: TermDecerated TypeDecorated -> WriterT [C.Statement TypeDecorated] Codegen (C.Expression TypeDecorated)
compileTerm (TermDecerated _ (Variable x ())) = do
  x' <- lift $ lookupVariable x
  pure $ C.Variable x'
compileTerm (TermDecerated _ (Extern (Symbol name) σ τ)) = do
  tell [C.ForwardDeclare τ name [σ]]
  pure $ C.Variable name
compileTerm (TermDecerated _ (FunctionApplication e1 e2@(TermDecerated τ _) σ)) = do
  e1' <- compileTerm e1
  e2' <- compileTerm e2
  pure $ C.Call σ [τ] e1' [e2']
compileTerm (TermDecerated _ (Alias e1 (Bound pm e2))) = do
  e1' <- compileTerm e1
  bindings <- lift $ compilePattern pm e1'
  tell $ bindings
  compileTerm e2
compileTerm (TermDecerated σ (RuntimePairIntroduction e1 e2)) = do
  e1' <- compileTerm e1
  e2' <- compileTerm e2
  pure $ C.CompoundLiteral σ [e1', e2']
compileTerm (TermDecerated _ (ReadReference () e σ)) = do
  e' <- compileTerm e
  pure $ C.Dereference σ e'
{-
compileTerm (TermDecerated _ (LocalRegion (e1@(TermDecerated σ _), (Bound pm e2)))) = do
  e1' <- compileTerm e1
  stack <- lift temporary
  tell $ [C.VariableDeclaration σ stack e1']
  binding <- lift $ compilePattern pm (C.Address $ C.Variable stack)
  tell $ binding
  compileTerm e2
-}
compileTerm (TermDecerated _ (FunctionLiteral _)) = error "function literal inside runtime"

compileFunctionLiteralImpl :: Symbol -> TermDecerated TypeDecorated -> Codegen (C.Global TypeDecorated)
compileFunctionLiteralImpl (Symbol name) (TermDecerated _ (FunctionLiteral (Bound pm@(PatternDecorated σ _) e@(TermDecerated τ _)))) = do
  argumentName <- temporary
  bindings <- compilePattern pm (C.Variable argumentName)
  let arguments = [(σ, argumentName)]
  (result, depend) <- runWriterT (compileTerm e)
  let body = bindings ++ depend ++ [C.Return result]
  pure $ C.FunctionDefinition τ name arguments body
compileFunctionLiteralImpl _ _ = error "top level non function literal"

{-
compileFunctionLiteral :: [Identifier] -> Identifier -> Term Internal -> [C.Global (C.Representation C.RepresentationFix)]
compileFunctionLiteral path name e = [fmap ctype $ run $ compileFunctionLiteralImpl manging decorated]
  where
    manging = mangle $ Path path name
    decorated = fmap snd $ runReader (decorateTypeCheck (runDecorate $ decorateTerm e)) Map.empty
    run c = runCodegen c (external e)
-}
