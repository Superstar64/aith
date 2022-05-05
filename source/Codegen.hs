module Codegen where

import Ast.Common hiding (fresh)
import Ast.Kind (KindRuntime (..), KindSignedness (..), KindSize (..))
import Ast.Term
import qualified C.Ast as C
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Control.Monad.Trans.Writer.Strict (Writer, WriterT (..), runWriter, runWriterT, tell)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Misc.Symbol
import Misc.Util
import Simple

newtype DependencyState = DependencyState (Set [SimpleType])

newtype Dependency a = Dependency (StateT DependencyState (Writer [C.Statement]) a) deriving (Functor, Applicative, Monad)

runDependency :: Dependency a -> (a, [C.Statement])
runDependency (Dependency m) = runWriter $ evalStateT m (DependencyState $ Set.empty)

data CodegenState = CodegenState
  { temporaryCounter :: Int,
    variables :: Map TermIdentifier String,
    cLocals :: Set String
  }

newtype Codegen a = Codegen (StateT CodegenState Dependency a) deriving (Functor, Applicative, Monad)

runCodegen :: Codegen a -> Set String -> Dependency a
runCodegen (Codegen m) symbols = evalStateT m $ CodegenState 0 Map.empty symbols

lookupVariable x = do
  CodegenState _ variables _ <- Codegen get
  pure $ variables ! x

-- todo, search symbols if any symbol begins with _n, where n is an integer
temporary = do
  state@(CodegenState i _ _) <- Codegen get
  let name = "_" ++ show i
  Codegen $ put state {temporaryCounter = i + 1}
  pure name

ctype :: SimpleType -> Codegen C.Type
ctype (SimpleType PointerRep) = pure $ C.Composite $ C.Pointer $ C.Base C.Void
ctype (SimpleType (StructRep σs)) = do
  DependencyState solved <- Codegen $ lift $ Dependency $ get
  let mangling = σs >>= mangleType
  if σs `Set.notMember` solved
    then do
      Codegen $ lift $ Dependency $ put $ DependencyState (Set.insert σs solved)
      members <- traverse ctype σs
      let σ = (C.Base $ C.Struct $ C.StructDefinition mangling (zipWith C.Declaration members fields))
      let binding = C.Binding (C.Declaration σ Nothing) C.Uninitialized
      Codegen $ lift $ Dependency $ lift $ tell [binding]
    else pure ()
  pure $ C.Base $ C.Struct $ C.StructUse mangling
  where
    fields = Just <$> map (\x -> '_' : show x) [0 ..]
ctype (SimpleType (WordRep Byte)) = pure $ C.Base C.Byte
ctype (SimpleType (WordRep Short)) = pure $ C.Base C.Short
ctype (SimpleType (WordRep Int)) = pure $ C.Base C.Int
ctype (SimpleType (WordRep Long)) = pure $ C.Base C.Long

cint :: KindSize -> KindSignedness -> C.Type
cint Byte Signed = C.Base C.Byte
cint Short Signed = C.Base C.Short
cint Int Signed = C.Base C.Int
cint Long Signed = C.Base C.Long
cint Byte Unsigned = C.Base C.UByte
cint Short Unsigned = C.Base C.UShort
cint Int Unsigned = C.Base C.UInt
cint Long Unsigned = C.Base C.ULong

-- only effectless expressions can be passed in
compilePattern :: SimplePattern p -> C.Expression -> Codegen [C.Statement]
compilePattern pm@(SimplePattern _ (RuntimePatternVariable x@(TermIdentifier base) _)) target = do
  let σ = simplePatternType pm
  state@(CodegenState _ variables cLocals) <- Codegen get
  let name = fresh cLocals base
  Codegen $ put state {variables = Map.insert x name variables, cLocals = Set.insert name cLocals}
  σ <- ctype σ
  pure [C.Binding (C.Declaration σ (Just name)) (C.Initializer $ C.Scalar target)]
compilePattern (SimplePattern _ (RuntimePatternPair pm1 pm2)) target = do
  pm1' <- compilePattern pm1 (C.Member target "_0")
  pm2' <- compilePattern pm2 (C.Member target "_1")
  pure $ pm1' ++ pm2'

putIntoVariable :: SimpleType -> C.Expression -> WriterT [C.Statement] Codegen C.Expression
putIntoVariable σ e = do
  σ <- lift $ ctype σ
  putIntoVariableRaw σ (C.Scalar e)

putIntoVariableRaw σ e = do
  result <- lift temporary
  tell [C.Binding (C.Declaration σ (Just result)) (C.Initializer e)]
  pure $ C.Variable result

-- always returns effectless expressions
compileTerm :: SimpleTerm p -> SimpleType -> WriterT [C.Statement] Codegen C.Expression
compileTerm (SimpleTerm _ (Variable x ())) _ = do
  x' <- lift $ lookupVariable x
  pure $ C.Variable x'
compileTerm (SimpleTerm _ (Extern (Symbol name) σ () τ)) _ = do
  τ <- lift $ ctype τ
  σ <- lift $ ctype σ
  tell [C.Binding (C.Declaration (C.Composite $ C.Function τ [C.Declaration σ Nothing]) (Just name)) C.Uninitialized]
  pure $ C.Variable name
compileTerm (SimpleTerm _ (FunctionApplication e1 e2 τ)) σ = do
  σ' <- lift $ ctype σ
  τ' <- lift $ ctype τ
  e1 <- compileTerm e1 (SimpleType PointerRep)
  e1 <-
    putIntoVariableRaw
      (C.Composite $ C.Pointer $ C.Composite $ C.Function σ' [C.Declaration τ' Nothing])
      (C.Scalar e1)
  e2 <- compileTerm e2 τ
  putIntoVariable σ $ C.Call e1 [e2]
compileTerm (SimpleTerm _ (Alias e1 (Bound pm e2))) σ = do
  let τ = simplePatternType pm
  e1' <- compileTerm e1 τ
  bindings <- lift $ compilePattern pm e1'
  tell $ bindings
  compileTerm e2 σ
compileTerm (SimpleTerm _ (PairIntroduction e1 e2)) σ@(SimpleType (StructRep [τ, τ'])) = do
  e1' <- compileTerm e1 τ
  e2' <- compileTerm e2 τ'
  σ <- lift $ ctype σ
  putIntoVariableRaw σ (C.Brace [C.Scalar e1', C.Scalar e2'])
compileTerm (SimpleTerm _ (ReadReference e)) σ = do
  σ' <- lift $ ctype σ
  e <- compileTerm e (SimpleType PointerRep)
  e <- putIntoVariableRaw (C.Composite $ C.Pointer $ σ') (C.Scalar e)
  pure $ C.Dereference e
compileTerm (SimpleTerm _ (NumberLiteral n)) _ = pure $ C.IntegerLiteral n
compileTerm (SimpleTerm _ (Arithmatic o e1 e2 s)) σ@(SimpleType (WordRep size)) = do
  let σ' = cint size s
  e1 <- compileTerm e1 σ
  e1 <- putIntoVariableRaw σ' (C.Scalar e1)
  e2 <- compileTerm e2 σ
  e2 <- putIntoVariableRaw σ' (C.Scalar e2)
  pure $ op e1 e2
  where
    op = case o of
      Addition -> C.Addition
      Subtraction -> C.Subtraction
      Multiplication -> C.Multiplication
      Division -> C.Division
compileTerm (SimpleTerm _ (BooleanLiteral True)) _ = pure $ C.IntegerLiteral 1
compileTerm (SimpleTerm _ (BooleanLiteral False)) _ = pure $ C.IntegerLiteral 0
compileTerm (SimpleTerm _ (If eb et ef)) σ = do
  eb <- compileTerm eb (SimpleType $ WordRep $ Byte)
  result <- lift temporary
  σ' <- lift $ ctype σ
  tell [C.Binding (C.Declaration σ' (Just result)) C.Uninitialized]
  (et, tDepend) <- lift $ runWriterT $ compileTerm et σ
  (ef, fDepend) <- lift $ runWriterT $ compileTerm ef σ
  let finish e = C.Expression $ C.Assign (C.Variable result) e
  tell [C.If eb (tDepend ++ [finish et]) (fDepend ++ [finish ef])]
  pure $ C.Variable result
compileTerm _ _ = error "invalid type for simple term"

compileFunction :: Symbol -> SimpleFunction p -> SimpleFunctionType -> Codegen C.Statement
compileFunction (Symbol name) (SimpleFunction _ (Bound pm e)) (SimpleFunctionType σ τ) = do
  argumentName <- temporary
  bindings <- compilePattern pm (C.Variable argumentName)
  σ <- ctype σ
  let arguments = [C.Declaration σ (Just argumentName)]
  (result, depend) <- runWriterT (compileTerm e τ)
  let body = bindings ++ depend ++ [C.Return result]
  τ <- ctype τ
  pure $ C.Binding (C.Declaration (C.Composite $ C.Function τ arguments) (Just name)) (C.FunctionBody body)

codegen sym σ e = runCodegen (compileFunction sym e σ) (external e)
