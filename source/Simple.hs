module Simple where

import Ast.Common
import Ast.Term hiding (convertTerm)
import Ast.Type hiding (convertType)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (Reader, ReaderT, ask, runReader, runReaderT, withReaderT)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Void (absurd)

newtype Simplify a = Simplify
  { runSimplify' ::
      ReaderT (Map TypeIdentifier TypeInfer) (Reader (Map TypeGlobalIdentifier TypeInfer)) a
  }
  deriving (Functor, Applicative, Monad)

withSimplify :: (Map TypeIdentifier TypeInfer -> Map TypeIdentifier TypeInfer) -> Simplify a -> Simplify a
withSimplify f (Simplify s) = Simplify $ withReaderT f s

runSimplify :: Simplify a -> Map TypeIdentifier TypeInfer -> Map TypeGlobalIdentifier TypeInfer -> a
runSimplify (Simplify s) = runReader . runReaderT s

newtype SimpleType = SimpleType (KindRuntime KindSize SimpleType) deriving (Eq, Ord)

data SimplePattern p = SimplePattern p (TermRuntimePatternF SimpleType (SimplePattern p))

data SimpleTerm p
  = SimpleTerm
      p
      ( TermRuntime
          ()
          ()
          KindSignedness
          SimpleType
          (Bound (SimplePattern p) (SimpleTerm p))
          (SimpleTerm p)
      )

data SimpleFunction p = SimpleFunction p (Bound (SimplePattern p) (SimpleTerm p))

data SimpleFunctionType = SimpleFunctionType SimpleType SimpleType

mangleType :: SimpleType -> String
mangleType (SimpleType PointerRep) = "p"
mangleType (SimpleType (StructRep σs)) = "s" ++ (σs >>= mangleType) ++ "e"
mangleType (SimpleType (UnionRep σs)) = "u" ++ (σs >>= mangleType) ++ "e"
mangleType (SimpleType (WordRep Byte)) = "b"
mangleType (SimpleType (WordRep Short)) = "s"
mangleType (SimpleType (WordRep Int)) = "i"
mangleType (SimpleType (WordRep Long)) = "l"
mangleType (SimpleType (WordRep Native)) = "n"

convertKindImpl :: TypeInfer -> SimpleType
convertKindImpl (TypeAst () (KindRuntime PointerRep)) = SimpleType $ PointerRep
convertKindImpl (TypeAst () (KindRuntime (StructRep ρs))) = SimpleType $ StructRep (convertKindImpl <$> ρs)
convertKindImpl (TypeAst () (KindRuntime (UnionRep ρs))) = SimpleType $ UnionRep (convertKindImpl <$> ρs)
convertKindImpl (TypeAst () (KindRuntime (WordRep (TypeAst () (KindSize s))))) = SimpleType $ WordRep s
convertKindImpl _ = simpleFailType

simpleFailType = error "illegal simple type"

convertKind :: TypeInfer -> SimpleType
convertKind (TypeAst () (Pretype κ _)) = convertKindImpl κ
convertKind _ = simpleFailType

reconstruct = reconstructF index indexGlobal absurd poly representation multiplicities propositional
  where
    poly = error "poly type in runtime types"
    index x = do
      map <- Simplify ask
      pure $ map ! x
    indexGlobal x = do
      map <- Simplify $ lift ask
      pure $ map ! x
    representation σ = do
      κ <- reconstruct σ
      pure $ checkRepresentation κ
    multiplicities _ = error "multiplicity not needed during simple reconstruction"
    propositional _ = error "propostional not needed during simple reconstruction"

    checkRepresentation (TypeAst () (Pretype κ _)) = κ
    checkRepresentation _ = error "reconstruction of pair didn't return pretype"

convertType σ = convertKind <$> reconstruct σ

convertTypeSigned (TypeAst () (KindSignedness Signed)) = Signed
convertTypeSigned (TypeAst () (KindSignedness Unsigned)) = Unsigned
convertTypeSigned _ = error "bad sign"

convertTermPattern :: TermRuntimePatternInfer p -> Simplify (SimplePattern p)
convertTermPattern (TermRuntimePattern p pm) =
  SimplePattern p <$> traverseTermRuntimePatternF (convertType) convertTermPattern pm

simpleFailPattern = error "illegal simple pattern"

convertTerm :: TermInfer p -> Simplify (SimpleTerm p)
convertTerm (Term p (TermRuntime e)) =
  SimpleTerm p
    <$> traverseTermRuntime (const $ pure ()) (const $ pure ()) (pure . convertTypeSigned . runCore) (convertType . runCore) (traverseBound convertTermPattern convertTerm) convertTerm e
convertTerm (Term p (TermErasure e)) = case e of
  (Borrow ep (Bound (TypePattern () α κ) (Bound pm@(TermRuntimePattern _ (RuntimePatternVariable x _)) e)) _) -> do
    ep <- convertTerm ep
    withSimplify (Map.insert α κ) $ do
      pm <- convertTermPattern pm
      e <- convertTerm e
      pure $ SimpleTerm p $ Alias ep (Bound pm $ SimpleTerm p $ TupleIntroduction [e, SimpleTerm p $ Variable x ()])
  Borrow _ _ _ -> simpleFailTerm
  Wrap _ e -> convertTerm e
  Unwrap _ e -> convertTerm e
  IsolatePointer e -> convertTerm e
convertTerm (Term _ _) = simpleFailTerm

simpleFailTerm = error "illegal simple term"

convertFunctionType (TypeScheme () (TypeForall (Bound (TypePattern () x κ) σ))) = withSimplify (Map.insert x κ) $ convertFunctionType σ
convertFunctionType (TypeScheme () (MonoType (TypeAst () (FunctionLiteralType σ _ τ)))) = do
  σ' <- convertType σ
  τ' <- convertType τ
  pure $ SimpleFunctionType σ' τ'
convertFunctionType _ = error "failed to convert function type"

convertFunction (TermScheme _ (TypeAbstraction (Bound (TypePattern () x κ) e))) = withSimplify (Map.insert x κ) $ convertFunction e
convertFunction (TermScheme _ (MonoTerm (Term p (FunctionLiteral (Bound pm e))) _)) = do
  pm' <- convertTermPattern pm
  e' <- convertTerm e
  pure $ SimpleFunction p $ Bound pm' e'
convertFunction _ = error "failed to convert function"

simplePatternType :: SimplePattern p -> SimpleType
simplePatternType (SimplePattern _ (RuntimePatternVariable _ σ)) = σ
simplePatternType (SimplePattern _ (RuntimePatternTuple pms)) = SimpleType $ StructRep $ map simplePatternType pms
simplePatternType (SimplePattern _ (RuntimePatternBoolean _)) = SimpleType $ WordRep Byte
