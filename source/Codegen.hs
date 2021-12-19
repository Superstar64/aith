module Codegen where

import qualified C.Ast as C
import Control.Monad.State (State, evalState, get, put)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (WriterT (..), runWriterT, tell)
import Data.Set (Set)
import qualified Data.Set as Set
import Language.Ast.Common hiding (fresh)
import Language.Ast.Kind (KindRuntime (..), KindSignedness (..), KindSize (..))
import Language.Ast.Term
import Misc.MonoidMap (Map, (!))
import qualified Misc.MonoidMap as Map
import Misc.Symbol
import Misc.Util
import Simple

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

ctype :: SimpleType -> C.Representation C.RepresentationFix
ctype (SimpleType PointerRep) = C.Pointer
ctype (SimpleType (StructRep σs)) = C.Struct $ C.RepresentationFix $ fmap ctype σs
ctype (SimpleType (WordRep Byte)) = C.Byte
ctype (SimpleType (WordRep Short)) = C.Short
ctype (SimpleType (WordRep Int)) = C.Int
ctype (SimpleType (WordRep Long)) = C.Long

compilePattern :: SimplePattern p -> C.Expression SimpleType -> Codegen ([C.Statement SimpleType])
compilePattern pm@(SimplePattern _ (PatternVariable x@(TermIdentifier base) _)) target = do
  let σ = simplePatternType pm
  (vars, mapping) <- Codegen get
  let name = fresh vars base
  Codegen $ put (Set.insert name vars, Map.insert x name mapping)
  pure [C.VariableDeclaration σ name target]
compilePattern pm@(SimplePattern _ (RuntimePatternPair pm1 pm2)) target = do
  let σ = simplePatternType pm
  new <- temporary
  let initial = C.VariableDeclaration σ new target
  pm1' <- compilePattern pm1 (C.Member (C.Variable new) "_0")
  pm2' <- compilePattern pm2 (C.Member (C.Variable new) "_1")
  pure $ initial : pm1' ++ pm2'

compileTerm :: SimpleTerm p -> SimpleType -> WriterT [C.Statement SimpleType] Codegen (C.Expression SimpleType)
compileTerm (SimpleTerm _ (Variable x ())) _ = do
  x' <- lift $ lookupVariable x
  pure $ C.Variable x'
compileTerm (SimpleTerm _ (Extern (Symbol name) σ τ)) _ = do
  tell [C.ForwardDeclare τ name [σ]]
  pure $ C.Variable name
compileTerm (SimpleTerm _ (FunctionApplication e1 e2 τ)) σ = do
  e1' <- compileTerm e1 (SimpleType PointerRep)
  e2' <- compileTerm e2 τ
  pure $ C.Call σ [τ] e1' [e2']
compileTerm (SimpleTerm _ (Alias e1 (Bound pm e2))) σ = do
  let τ = simplePatternType pm
  e1' <- compileTerm e1 τ
  bindings <- lift $ compilePattern pm e1'
  tell $ bindings
  compileTerm e2 σ
compileTerm (SimpleTerm _ (RuntimePairIntroduction e1 e2)) σ@(SimpleType (StructRep [τ, τ'])) = do
  e1' <- compileTerm e1 τ
  e2' <- compileTerm e2 τ'
  pure $ C.CompoundLiteral σ [e1', e2']
compileTerm (SimpleTerm _ (ReadReference () e)) σ = do
  e' <- compileTerm e (SimpleType PointerRep)
  pure $ C.Dereference σ e'
compileTerm (SimpleTerm _ (NumberLiteral n)) _ = pure $ C.IntegerLiteral n
compileTerm (SimpleTerm _ (Arithmatic o e1 e2 s)) σ = do
  e1' <- compileTerm e1 σ
  e2' <- compileTerm e2 σ
  pure $ op (sign, σ) e1' (sign, σ) e2'
  where
    op = case o of
      Addition -> C.Addition
      Subtraction -> C.Subtraction
      Multiplication -> C.Multiplication
      Division -> C.Division
    sign = case s of
      Signed -> C.Signed
      Unsigned -> C.Unsigned
compileTerm _ _ = error "invalid type for simple term"

compileFunction :: Symbol -> SimpleFunction p -> SimpleFunctionType -> Codegen (C.Global SimpleType)
compileFunction (Symbol name) (SimpleFunction _ (Bound pm e)) (SimpleFunctionType σ τ) = do
  argumentName <- temporary
  bindings <- compilePattern pm (C.Variable argumentName)
  let arguments = [(σ, argumentName)]
  (result, depend) <- runWriterT (compileTerm e τ)
  let body = bindings ++ depend ++ [C.Return result]
  pure $ C.FunctionDefinition τ name arguments body
