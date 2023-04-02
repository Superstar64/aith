module Codegen where

import Ast.Common hiding (fresh)
import Ast.Term
import Ast.Type (KindRuntime (..), KindSignedness (..), KindSize (..))
import qualified C.Ast as C
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT, withReaderT)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Control.Monad.Trans.Writer.Strict (Writer, WriterT (..), execWriterT, runWriter, runWriterT, tell)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Misc.Symbol
import Simple

data Nominal
  = Struct [SimpleType]
  | Union [SimpleType]
  deriving (Eq, Ord)

newtype Dependency a = Dependency (StateT (Set Nominal) (Writer [C.Statement]) a) deriving (Functor, Applicative, Monad)

runDependency :: Dependency a -> (a, [C.Statement])
runDependency (Dependency m) = runWriter $ evalStateT m (Set.empty)

newtype Codegen a = Codegen
  { runCodegen' ::
      ReaderT
        (Map TermIdentifier (C.Expression))
        (StateT Int Dependency)
        a
  }
  deriving (Functor, Applicative, Monad)

runCodegen :: Codegen a -> Dependency a
runCodegen (Codegen m) = evalStateT (runReaderT m Map.empty) 0

lookupVariable x = do
  variables <- Codegen ask
  pure $ variables ! x

temporary = do
  i <- Codegen $ lift get
  let name = "_" ++ show i
  Codegen $ lift $ put $ i + 1
  pure name

ctype' :: SimpleType -> Dependency C.Type
ctype' (SimpleType PointerRep) = pure $ C.Composite $ C.Pointer $ C.Base C.Void
ctype' (SimpleType (StructRep [])) = pure $ C.Base C.Byte
ctype' σ
  | (SimpleType (StructRep σs)) <- σ = nominal Struct C.Struct "s" σs
  | (SimpleType (UnionRep σs)) <- σ = nominal Union C.Union "u" σs
  where
    fields = Just <$> map (\x -> '_' : show x) [0 ..]
    nominal struct cstruct prefix σs = do
      solved <- Dependency $ get
      let mangling = prefix ++ (σs >>= mangleType)
      if struct σs `Set.notMember` solved
        then do
          Dependency $ put $ (Set.insert (struct σs) solved)
          members <- traverse ctype' σs
          let σ = (C.Base $ cstruct $ C.StructDefinition mangling (zipWith C.Declaration members fields))
          let binding = C.Binding (C.Declaration σ Nothing) C.Uninitialized
          Dependency $ lift $ tell [binding]
        else pure ()
      pure $ C.Base $ cstruct $ C.StructUse mangling
ctype' (SimpleType (WordRep Byte)) = pure $ C.Base C.Byte
ctype' (SimpleType (WordRep Short)) = pure $ C.Base C.Short
ctype' (SimpleType (WordRep Int)) = pure $ C.Base C.Int
ctype' (SimpleType (WordRep Long)) = pure $ C.Base C.Long
ctype' (SimpleType (WordRep Native)) = pure $ C.Base C.Size

ctype :: SimpleType -> Codegen C.Type
ctype = Codegen . lift . lift . ctype'

cint :: KindSize -> KindSignedness -> C.Type
cint Byte Signed = C.Base C.Byte
cint Short Signed = C.Base C.Short
cint Int Signed = C.Base C.Int
cint Long Signed = C.Base C.Long
cint Native Signed = C.Base C.PtrDiff
cint Byte Unsigned = C.Base C.UByte
cint Short Unsigned = C.Base C.UShort
cint Int Unsigned = C.Base C.UInt
cint Long Unsigned = C.Base C.ULong
cint Native Unsigned = C.Base C.Size

-- only effectless expressions can be passed in
augmentPattern' augment target (SimplePattern _ (RuntimePatternVariable x _)) f = augment x target f
augmentPattern' augment target (SimplePattern _ (RuntimePatternTuple pms)) f = do
  foldr (uncurry (augmentPattern' augment)) f $ zip [C.Member target ("_" ++ show i) | i <- [0 ..]] pms
augmentPattern' _ _ (SimplePattern _ (RuntimePatternBoolean _)) x = x

augmentPattern = augmentPattern' augmentPatternImpl

augmentPatternImpl x target f = Codegen $ withReaderT (Map.insert x target) $ runCodegen' f

augmentPatternW = augmentPattern' go
  where
    go x target f = WriterT $ augmentPatternImpl x target $ runWriterT f

putIntoVariable :: SimpleType -> C.Expression -> WriterT [C.Statement] Codegen C.Expression
putIntoVariable σ e = putIntoVariableInit σ (C.Scalar e)

putIntoVariableInit :: SimpleType -> C.Initializer -> WriterT [C.Statement] Codegen C.Expression
putIntoVariableInit σ e = do
  σ <- lift $ ctype σ
  putIntoVariableRaw σ e

putIntoVariableRaw σ e = do
  result <- lift temporary
  tell [C.Binding (C.Declaration σ (Just result)) (C.Initializer e)]
  pure $ C.Variable result

compileMatch :: C.Expression -> SimplePattern p -> WriterT [C.Statement] Codegen C.Expression
compileMatch _ (SimplePattern _ (RuntimePatternVariable _ _)) = pure $ C.IntegerLiteral 1
compileMatch target (SimplePattern _ (RuntimePatternTuple pms)) = do
  checks <- sequence $ zipWith compileMatch [C.Member target ("_" ++ show i) | i <- [0 ..]] pms
  pure $ foldl C.LogicalAnd (C.IntegerLiteral 1) checks
compileMatch target (SimplePattern _ (RuntimePatternBoolean True)) = pure $ C.Equal target (C.IntegerLiteral 1)
compileMatch target (SimplePattern _ (RuntimePatternBoolean False)) = pure $ C.Equal target (C.IntegerLiteral 0)

compileTerm :: SimpleTerm p -> SimpleType -> WriterT [C.Statement] Codegen C.Expression
compileTerm (SimpleTerm _ (Variable x () _)) _ = do
  x' <- lift $ lookupVariable x
  pure $ x'
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
  e1' <- putIntoVariable τ =<< compileTerm e1 τ
  augmentPatternW e1' pm $ do
    compileTerm e2 σ
compileTerm (SimpleTerm _ (TupleIntroduction [])) (SimpleType (StructRep [])) = do
  pure $ C.IntegerLiteral 0
compileTerm (SimpleTerm _ (TupleIntroduction es)) σ@(SimpleType (StructRep τs)) | length es == length τs = do
  es <- sequence $ zipWith compileTerm es τs
  putIntoVariableInit σ (C.Brace $ map C.Scalar es)
compileTerm (SimpleTerm _ (ReadReference e)) σ = do
  σ' <- lift $ ctype σ
  e <- compileTerm e (SimpleType PointerRep)
  e <- putIntoVariableRaw (C.Composite $ C.Pointer $ σ') (C.Scalar e)
  pure $ C.Dereference e
compileTerm (SimpleTerm _ (WriteReference ep ev σ)) (SimpleType (StructRep [])) = do
  σ' <- lift $ ctype σ
  ep <- compileTerm ep (SimpleType $ PointerRep)
  ep <- putIntoVariableRaw (C.Composite $ C.Pointer $ σ') (C.Scalar ep)
  ev <- compileTerm ev σ
  tell [C.Expression $ C.Assign (C.Dereference ep) ev]
  pure $ C.IntegerLiteral 0
compileTerm (SimpleTerm _ (NumberLiteral n _)) _ = pure $ C.IntegerLiteral n
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
compileTerm (SimpleTerm _ (Relational o e1 e2 σ@(SimpleType (WordRep size)) s)) (SimpleType (WordRep Byte)) = do
  let σ' = cint size s
  e1 <- compileTerm e1 σ
  e1 <- putIntoVariableRaw σ' (C.Scalar e1)
  e2 <- compileTerm e2 σ
  e2 <- putIntoVariableRaw σ' (C.Scalar e2)
  pure $ op e1 e2
  where
    op = case o of
      Equal -> C.Equal
      NotEqual -> C.NotEqual
      LessThen -> C.LessThen
      LessThenEqual -> C.LessThenEqual
      GreaterThen -> C.GreaterThen
      GreaterThenEqual -> C.GreaterThenEqual
compileTerm (SimpleTerm _ (BooleanLiteral True)) _ = pure $ C.IntegerLiteral 1
compileTerm (SimpleTerm _ (BooleanLiteral False)) _ = pure $ C.IntegerLiteral 0
compileTerm (SimpleTerm _ (Case e τ λs ())) σ = do
  e <- compileTerm e τ
  result <- lift temporary
  σ' <- lift $ ctype σ
  tell [C.Binding (C.Declaration σ' (Just result)) C.Uninitialized]
  go e result λs
  pure $ C.Variable result
  where
    go e result (Bound pm et : λs) = do
      valid <- compileMatch e pm
      (et, depend) <- lift $ runWriterT $ compileTerm et σ
      remain <- lift $ execWriterT $ go e result λs
      tell [C.If valid (depend ++ [C.Expression $ C.Assign (C.Variable result) et]) remain]
      pure ()
    go _ _ [] = do
      tell [C.Binding (C.Declaration (C.Composite $ C.Function (C.Base C.Void) []) (Just "abort")) C.Uninitialized]
      tell [C.Expression $ C.Call (C.Variable "abort") []]
compileTerm (SimpleTerm _ (PointerIncrement ep ei σ)) (SimpleType PointerRep) = do
  ep <- compileTerm ep (SimpleType $ PointerRep)
  σ <- lift $ ctype σ
  ep <- putIntoVariableRaw (C.Composite $ C.Pointer σ) (C.Scalar ep)
  ei <- compileTerm ei (SimpleType $ WordRep $ Native)
  ei <- putIntoVariableRaw (cint Native Unsigned) (C.Scalar ei)
  pure $ C.Addition ep ei
compileTerm (SimpleTerm _ (Continue e ())) μ@(SimpleType (StructRep [_, SimpleType (UnionRep [_, σ])])) = do
  e <- compileTerm e σ
  putIntoVariableInit μ (C.Brace [C.Scalar (C.IntegerLiteral 1), C.Designator [("_1", C.Scalar e)]])
compileTerm (SimpleTerm _ (Break e ())) μ@(SimpleType (StructRep [_, SimpleType (UnionRep [τ, _])])) = do
  e <- compileTerm e τ
  putIntoVariableInit μ (C.Brace [C.Scalar (C.IntegerLiteral 0), C.Designator [("_0", C.Scalar e)]])
compileTerm (SimpleTerm _ (Loop es (Bound pm el))) τ = do
  let σ = simplePatternType pm
  let μ = SimpleType $ StructRep [SimpleType $ WordRep $ Byte, SimpleType $ UnionRep [τ, σ]]
  μ' <- lift $ ctype μ

  es <- compileTerm es σ
  x <- lift $ temporary
  (el, depend) <- lift $
    augmentPattern (C.Member (C.Member (C.Variable x) "_1") "_1") pm $
      runWriterT $ do
        compileTerm el μ
  depend <- pure $ depend ++ [C.Expression $ C.Assign (C.Variable x) el]
  tell
    [ C.Binding (C.Declaration μ' $ Just x) C.Uninitialized,
      C.Expression $ C.Assign (C.Member (C.Member (C.Variable x) "_1") "_1") es,
      C.DoWhile depend (C.Member (C.Variable x) "_0")
    ]
  pure $ C.Member (C.Member (C.Variable x) "_1") "_0"
compileTerm _ _ = error "invalid type for simple term"

compileFunction :: Symbol -> SimpleFunction p -> SimpleFunctionType -> Codegen C.Statement
compileFunction (Symbol name) (SimpleFunction _ (Bound pm e)) (SimpleFunctionType σ τ) = do
  argumentName <- temporary
  (result, depend) <- augmentPattern (C.Variable argumentName) pm $ do
    runWriterT (compileTerm e τ)

  σ <- ctype σ
  τ <- ctype τ
  let arguments = [C.Declaration σ (Just argumentName)]
  let body = depend ++ [C.Return result]
  pure $ C.Binding (C.Declaration (C.Composite $ C.Function τ arguments) (Just name)) (C.FunctionBody body)

codegen sym σ e = runCodegen (compileFunction sym e σ)
