module Codegen
  ( codegen,
    Dependency,
    runDependency,
  )
where

import qualified C.Ast as C
import Control.Monad (replicateM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT, withReaderT)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Control.Monad.Trans.Writer.Strict (Writer, WriterT (..), execWriterT, runWriter, runWriterT, tell)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Simple

data Nominal
  = Struct [Simple.Type]
  | Union [Simple.Type]
  deriving (Eq, Ord)

newtype Dependency a = Dependency (StateT (Set Nominal) (Writer [C.Statement]) a) deriving (Functor, Applicative, Monad)

runDependency :: Dependency a -> (a, [C.Statement])
runDependency (Dependency m) = runWriter $ evalStateT m (Set.empty)

newtype Codegen a = Codegen
  { runCodegen' ::
      ReaderT
        (Map Simple.TermIdentifier (C.Expression))
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

ctype' :: Simple.Type -> Dependency C.Type
ctype' Simple.Pointer = pure $ C.Composite $ C.Pointer $ C.Base C.Void
ctype' (Simple.Struct []) = pure $ C.Base C.Byte
ctype' σ
  | (Simple.Struct σs) <- σ = nominal Struct C.Struct "s" σs
  | (Simple.Union σs) <- σ = nominal Union C.Union "u" σs
  where
    fields = Just <$> map (\x -> '_' : show x) [0 ..]
    nominal struct cstruct prefix σs = do
      solved <- Dependency $ get
      let mangling = prefix ++ (σs >>= Simple.mangleType)
      if struct σs `Set.notMember` solved
        then do
          Dependency $ put $ (Set.insert (struct σs) solved)
          members <- traverse ctype' σs
          let σ = (C.Base $ cstruct $ C.StructDefinition mangling (zipWith C.Declaration members fields))
          let binding = C.Binding (C.Declaration σ Nothing) C.Uninitialized
          Dependency $ lift $ tell [binding]
        else pure ()
      pure $ C.Base $ cstruct $ C.StructUse mangling
ctype' (Simple.Word Simple.Byte) = pure $ C.Base C.Byte
ctype' (Simple.Word Simple.Short) = pure $ C.Base C.Short
ctype' (Simple.Word Simple.Int) = pure $ C.Base C.Int
ctype' (Simple.Word Simple.Long) = pure $ C.Base C.Long
ctype' (Simple.Word Simple.Native) = pure $ C.Base C.Size

ctype :: Simple.Type -> Codegen C.Type
ctype = Codegen . lift . lift . ctype'

cint :: Simple.Size -> Simple.Signedness -> C.Type
cint Simple.Byte Simple.Signed = C.Base C.Byte
cint Simple.Short Simple.Signed = C.Base C.Short
cint Simple.Int Simple.Signed = C.Base C.Int
cint Simple.Long Simple.Signed = C.Base C.Long
cint Simple.Native Simple.Signed = C.Base C.PtrDiff
cint Simple.Byte Simple.Unsigned = C.Base C.UByte
cint Simple.Short Simple.Unsigned = C.Base C.UShort
cint Simple.Int Simple.Unsigned = C.Base C.UInt
cint Simple.Long Simple.Unsigned = C.Base C.ULong
cint Simple.Native Simple.Unsigned = C.Base C.Size

-- only effectless expressions can be passed in
augmentPattern' augment target (Simple.MatchVariable _ x _) f = augment x target f
augmentPattern' augment target (Simple.MatchTuple _ pms) f = do
  foldr (uncurry (augmentPattern' augment)) f $ zip [C.Member target ("_" ++ show i) | i <- [0 ..]] pms
augmentPattern' _ _ (Simple.MatchBoolean _ _) x = x

augmentPatternImpl x target f = Codegen $ withReaderT (Map.insert x target) $ runCodegen' f

augmentPattern = augmentPattern' augmentPatternImpl

augmentPatterns [] = id
augmentPatterns ((e, pm) : xs) = augmentPattern e pm . augmentPatterns xs

augmentPatternW = augmentPattern' go
  where
    go x target f = WriterT $ augmentPatternImpl x target $ runWriterT f

putIntoVariable :: Simple.Type -> C.Expression -> WriterT [C.Statement] Codegen C.Expression
putIntoVariable σ e = putIntoVariableInit σ (C.Scalar e)

putIntoVariableInit :: Simple.Type -> C.Initializer -> WriterT [C.Statement] Codegen C.Expression
putIntoVariableInit σ e = do
  σ <- lift $ ctype σ
  putIntoVariableRaw σ e

putIntoVariableRaw σ e = do
  result <- lift temporary
  tell [C.Binding (C.Declaration σ (Just result)) (C.Initializer e)]
  pure $ C.Variable result

compileMatch :: C.Expression -> Simple.Pattern p -> WriterT [C.Statement] Codegen C.Expression
compileMatch _ (Simple.MatchVariable _ _ _) = pure $ C.IntegerLiteral 1
compileMatch target (Simple.MatchTuple _ pms) = do
  checks <- sequence $ zipWith compileMatch [C.Member target ("_" ++ show i) | i <- [0 ..]] pms
  pure $ foldl C.LogicalAnd (C.IntegerLiteral 1) checks
compileMatch target (Simple.MatchBoolean _ True) = pure $ C.Equal target (C.IntegerLiteral 1)
compileMatch target (Simple.MatchBoolean _ False) = pure $ C.Equal target (C.IntegerLiteral 0)

compileTerm :: Simple.Term p -> Simple.Type -> WriterT [C.Statement] Codegen C.Expression
compileTerm (Simple.Variable _ x) _ = do
  x' <- lift $ lookupVariable x
  pure $ x'
compileTerm (Simple.Extern _ (Simple.Symbol name) σs τ) _ = do
  τ <- lift $ ctype τ
  σs <- lift $ traverse ctype σs
  tell [C.Binding (C.Declaration (C.Composite $ C.Function τ [C.Declaration σ Nothing | σ <- σs]) (Just name)) C.Uninitialized]
  pure $ C.Variable name
compileTerm (Simple.Application _ e1 e2s) σ = do
  σ' <- lift $ ctype σ
  τs' <- lift $ traverse (ctype . snd) e2s
  e1 <- compileTerm e1 Simple.Pointer
  e1 <-
    putIntoVariableRaw
      (C.Composite $ C.Pointer $ C.Composite $ C.Function σ' [C.Declaration τ' Nothing | τ' <- τs'])
      (C.Scalar e1)
  e2s <- traverse (uncurry compileTerm) e2s
  putIntoVariable σ $ C.Call e1 e2s
compileTerm (Simple.Let _ e1 (Simple.Bound pm e2)) σ = do
  let τ = Simple.patternType pm
  e1' <- putIntoVariable τ =<< compileTerm e1 τ
  augmentPatternW e1' pm $ do
    compileTerm e2 σ
compileTerm (Simple.TupleLiteral _ []) (Simple.Struct []) = do
  pure $ C.IntegerLiteral 0
compileTerm (Simple.TupleLiteral _ es) σ@(Simple.Struct τs) | length es == length τs = do
  es <- sequence $ zipWith compileTerm es τs
  putIntoVariableInit σ (C.Brace $ map C.Scalar es)
compileTerm (Simple.Read _ e) σ = do
  σ' <- lift $ ctype σ
  e <- compileTerm e Simple.Pointer
  e <- putIntoVariableRaw (C.Composite $ C.Pointer $ σ') (C.Scalar e)
  pure $ C.Dereference e
compileTerm (Simple.Write _ ep ev σ) (Simple.Struct []) = do
  σ' <- lift $ ctype σ
  ep <- compileTerm ep Simple.Pointer
  ep <- putIntoVariableRaw (C.Composite $ C.Pointer $ σ') (C.Scalar ep)
  ev <- compileTerm ev σ
  tell [C.Expression $ C.Assign (C.Dereference ep) ev]
  pure $ C.IntegerLiteral 0
compileTerm (Simple.NumberLiteral _ n) _ = pure $ C.IntegerLiteral n
compileTerm (Simple.Arithmatic _ o e1 e2 s) σ@(Simple.Word size) = do
  let σ' = cint size s
  e1 <- compileTerm e1 σ
  e1 <- putIntoVariableRaw σ' (C.Scalar e1)
  e2 <- compileTerm e2 σ
  e2 <- putIntoVariableRaw σ' (C.Scalar e2)
  pure $ op e1 e2
  where
    op = case o of
      Simple.Addition -> C.Addition
      Simple.Subtraction -> C.Subtraction
      Simple.Multiplication -> C.Multiplication
      Simple.Division -> C.Division
      Simple.Modulus -> C.Modulus
compileTerm (Simple.Relational _ o e1 e2 σ@(Simple.Word size) s) (Simple.Word Simple.Byte) = do
  let σ' = cint size s
  e1 <- compileTerm e1 σ
  e1 <- putIntoVariableRaw σ' (C.Scalar e1)
  e2 <- compileTerm e2 σ
  e2 <- putIntoVariableRaw σ' (C.Scalar e2)
  pure $ op e1 e2
  where
    op = case o of
      Simple.Equal -> C.Equal
      Simple.NotEqual -> C.NotEqual
      Simple.LessThen -> C.LessThen
      Simple.LessThenEqual -> C.LessThenEqual
      Simple.GreaterThen -> C.GreaterThen
      Simple.GreaterThenEqual -> C.GreaterThenEqual
compileTerm (Simple.Resize _ e τ) σ = do
  e <- compileTerm e τ
  e <- putIntoVariable σ e
  pure e
compileTerm (Simple.BooleanLiteral _ True) _ = pure $ C.IntegerLiteral 1
compileTerm (Simple.BooleanLiteral _ False) _ = pure $ C.IntegerLiteral 0
compileTerm (Simple.Case _ e τ λs) σ = do
  e <- compileTerm e τ
  result <- lift temporary
  σ' <- lift $ ctype σ
  tell [C.Binding (C.Declaration σ' (Just result)) C.Uninitialized]
  go e result λs
  pure $ C.Variable result
  where
    go e result (Simple.Bound pm et : λs) = do
      valid <- compileMatch e pm
      (et, depend) <- lift $ runWriterT $ compileTerm et σ
      remain <- lift $ execWriterT $ go e result λs
      tell [C.If valid (depend ++ [C.Expression $ C.Assign (C.Variable result) et]) remain]
      pure ()
    go _ _ [] = do
      tell [C.Binding (C.Declaration (C.Composite $ C.Function (C.Base C.Void) []) (Just "abort")) C.Uninitialized]
      tell [C.Expression $ C.Call (C.Variable "abort") []]
compileTerm (Simple.PointerAddition _ ep ei σ) Simple.Pointer = do
  ep <- compileTerm ep Simple.Pointer
  σ <- lift $ ctype σ
  ep <- putIntoVariableRaw (C.Composite $ C.Pointer σ) (C.Scalar ep)
  ei <- compileTerm ei (Simple.Word Simple.Native)
  ei <- putIntoVariableRaw (cint Simple.Native Simple.Unsigned) (C.Scalar ei)
  pure $ C.Addition ep ei
compileTerm (Simple.Continue _ e) κ@(Simple.Struct [Simple.Word Simple.Byte, Simple.Union [_, σ]]) = do
  e <- compileTerm e σ
  putIntoVariableInit κ (C.Brace [C.Scalar (C.IntegerLiteral 1), C.Designator [("_1", C.Scalar e)]])
compileTerm (Simple.Break _ e) κ@(Simple.Struct [Simple.Word Simple.Byte, Simple.Union [τ, _]]) = do
  e <- compileTerm e τ
  putIntoVariableInit κ (C.Brace [C.Scalar (C.IntegerLiteral 0), C.Designator [("_0", C.Scalar e)]])
compileTerm (Simple.Loop _ es (Simple.Bound pm el)) τ = do
  let σ = Simple.patternType pm
  let κ = Simple.Struct [Simple.Word Simple.Byte, Simple.Union [τ, σ]]
  κ' <- lift $ ctype κ

  es <- compileTerm es σ
  x <- lift $ temporary
  (el, depend) <- lift $
    augmentPattern (C.Member (C.Member (C.Variable x) "_1") "_1") pm $
      runWriterT $ do
        compileTerm el κ
  depend <- pure $ depend ++ [C.Expression $ C.Assign (C.Variable x) el]
  tell
    [ C.Binding (C.Declaration κ' $ Just x) C.Uninitialized,
      C.Expression $ C.Assign (C.Member (C.Member (C.Variable x) "_1") "_1") es,
      C.DoWhile depend (C.Member (C.Variable x) "_0")
    ]
  pure $ C.Member (C.Member (C.Variable x) "_1") "_0"
compileTerm _ _ = error "invalid type for simple term"

compileFunction :: Simple.Symbol -> Simple.Function p -> Simple.FunctionType -> Codegen C.Statement
compileFunction (Simple.Symbol name) (Simple.Function _ pms e) (Simple.FunctionType σs τ) = do
  argumentNames <- replicateM (length pms) temporary
  (result, depend) <-
    augmentPatterns [(C.Variable argumentName, pm) | (argumentName, pm) <- zip argumentNames pms] $
      runWriterT (compileTerm e τ)

  σs <- traverse ctype σs
  τ <- ctype τ
  let arguments = [C.Declaration σ (Just argumentName) | (σ, argumentName) <- zip σs argumentNames]
  let body = depend ++ [C.Return result]
  pure $ C.Binding (C.Declaration (C.Composite $ C.Function τ arguments) (Just name)) (C.FunctionBody body)

codegen :: Simple.Symbol -> Simple.FunctionType -> Simple.Function p -> Dependency C.Statement
codegen sym σ e = runCodegen (compileFunction sym e σ)
