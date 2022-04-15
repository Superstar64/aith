module Codegen where

import Ast.Common hiding (fresh)
import Ast.Kind (KindRuntime (..), KindSignedness (..), KindSize (..))
import Ast.Term
import qualified C.Ast as C
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (State, evalState, get, put)
import Control.Monad.Trans.Writer.Strict (WriterT (..), runWriterT, tell)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Misc.Symbol
import Misc.Util
import Simple

data CodegenState = CodegenState
  { temporaryCounter :: Int,
    variables :: Map TermIdentifier String,
    cLocals :: Set String
  }

newtype Codegen a = Codegen (State CodegenState a) deriving (Functor, Applicative, Monad)

-- todo, search symbols if any symbol begins with _n, where n is an integero
runCodegen (Codegen x) symbols = evalState x $ CodegenState 0 Map.empty symbols

lookupVariable x = do
  CodegenState _ variables _ <- Codegen get
  pure $ variables ! x

temporary = do
  state@(CodegenState i _ _) <- Codegen get
  let name = "_" ++ show i
  Codegen $ put state {temporaryCounter = i + 1}
  pure name

ctype :: SimpleType -> C.Representation C.RepresentationFix
ctype (SimpleType PointerRep) = C.Pointer
ctype (SimpleType (StructRep σs)) = C.Struct $ C.RepresentationFix $ fmap ctype σs
ctype (SimpleType (WordRep Byte)) = C.Byte
ctype (SimpleType (WordRep Short)) = C.Short
ctype (SimpleType (WordRep Int)) = C.Int
ctype (SimpleType (WordRep Long)) = C.Long

-- only effectless expressions can be passed in
compilePattern :: SimplePattern p -> C.Expression SimpleType -> Codegen ([C.Statement SimpleType])
compilePattern pm@(SimplePattern _ (RuntimePatternVariable x@(TermIdentifier base) _)) target = do
  let σ = simplePatternType pm
  state@(CodegenState _ variables cLocals) <- Codegen get
  let name = fresh cLocals base
  Codegen $ put state {variables = Map.insert x name variables, cLocals = Set.insert name cLocals}
  pure [C.VariableDeclaration σ name target]
compilePattern (SimplePattern _ (RuntimePatternPair pm1 pm2)) target = do
  pm1' <- compilePattern pm1 (C.Member target "_0")
  pm2' <- compilePattern pm2 (C.Member target "_1")
  pure $ pm1' ++ pm2'

putIntoVariable :: SimpleType -> C.Expression SimpleType -> WriterT [C.Statement SimpleType] Codegen (C.Expression SimpleType)
putIntoVariable σ e = do
  result <- lift temporary
  tell [C.VariableDeclaration σ result $ e]
  pure $ C.Variable result

-- always returns effectless expressions
compileTerm :: SimpleTerm p -> SimpleType -> WriterT [C.Statement SimpleType] Codegen (C.Expression SimpleType)
compileTerm (SimpleTerm _ (Variable x ())) _ = do
  x' <- lift $ lookupVariable x
  pure $ C.Variable x'
compileTerm (SimpleTerm _ (Extern (Symbol name) σ () τ)) _ = do
  tell [C.ForwardDeclare τ name [σ]]
  pure $ C.Variable name
compileTerm (SimpleTerm _ (FunctionApplication e1 e2 τ)) σ = do
  e1' <- compileTerm e1 (SimpleType PointerRep)
  e2' <- compileTerm e2 τ
  putIntoVariable σ $ C.Call σ [τ] e1' [e2']
compileTerm (SimpleTerm _ (Alias e1 (Bound pm e2))) σ = do
  let τ = simplePatternType pm
  e1' <- compileTerm e1 τ
  bindings <- lift $ compilePattern pm e1'
  tell $ bindings
  compileTerm e2 σ
compileTerm (SimpleTerm _ (PairIntroduction e1 e2)) σ@(SimpleType (StructRep [τ, τ'])) = do
  e1' <- compileTerm e1 τ
  e2' <- compileTerm e2 τ'
  pure $ C.CompoundLiteral σ [e1', e2']
compileTerm (SimpleTerm _ (ReadReference e)) σ = do
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
