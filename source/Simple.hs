module Simple where

import Ast.Common.Variable
import Ast.Term.Algebra
import Ast.Term.Core hiding (convertTerm)
import Ast.Term.Runtime
import Ast.Type.Algebra hiding (Type)
import Ast.Type.Core hiding (convertType, reconstruct)
import qualified Ast.Type.Core as Core (reconstruct)
import Ast.Type.Runtime
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

data SimplePattern p = SimplePattern p (TermPatternF SimpleType (SimplePattern p))

data SimpleTerm p
  = SimpleTerm
      p
      ( TermRuntime
          ()
          ()
          KindSignedness
          SimpleType
          (SimpleBound p)
          (SimpleTerm p)
      )

data SimpleBound p = SimpleBound (SimplePattern p) (SimpleTerm p)

data SimpleFunction p = SimpleFunction p (SimpleBound p)

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
convertKindImpl (Type (KindRuntime PointerRep)) = SimpleType $ PointerRep
convertKindImpl (Type (KindRuntime (StructRep ρs))) = SimpleType $ StructRep (convertKindImpl <$> ρs)
convertKindImpl (Type (KindRuntime (UnionRep ρs))) = SimpleType $ UnionRep (convertKindImpl <$> ρs)
convertKindImpl (Type (KindRuntime (WordRep (Type (KindSize s))))) = SimpleType $ WordRep s
convertKindImpl _ = simpleFailType

simpleFailType = error "illegal simple type"

convertKind :: TypeInfer -> SimpleType
convertKind (Type (Pretype κ _)) = convertKindImpl κ
convertKind _ = simpleFailType

reconstruct = Core.reconstruct index indexGlobal absurd poly representation multiplicities propositional
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

    checkRepresentation (Type (Pretype κ _)) = κ
    checkRepresentation _ = error "reconstruction of pair didn't return pretype"

convertType σ = convertKind <$> reconstruct σ

convertTypeSigned (Type (KindSignedness Signed)) = Signed
convertTypeSigned (Type (KindSignedness Unsigned)) = Unsigned
convertTypeSigned _ = error "bad sign"

convertTermMetaPattern :: TermPatternInfer p -> Simplify (SimplePattern p)
convertTermMetaPattern (TermPattern p pm) =
  SimplePattern p <$> traverseTermPatternF (convertType) convertTermMetaPattern pm

simpleFailPattern = error "illegal simple pattern"

-- used for borrow, so augmenting types is not neccisary
convertTermScheme (TermScheme _ (MonoTerm e)) = convertTerm e
convertTermScheme (TermScheme _ (TypeAbstraction _ e)) = convertTermScheme e

convertTerm :: TermInfer p -> Simplify (SimpleTerm p)
convertTerm (Term p (TermRuntime e)) =
  SimpleTerm p
    <$> traverseTermRuntime
      (const $ pure ())
      (const $ pure ())
      (pure . convertTypeSigned)
      (convertType)
      (\(TermBound pm e) -> SimpleBound <$> (convertTermMetaPattern pm) <*> (convertTerm e))
      convertTerm
      e
convertTerm (Term _ (TermErasure e)) = case e of
  IsolatePointer e -> convertTerm e
  Cast e _ -> convertTerm e
convertTerm (Term _ _) = simpleFailTerm

simpleFailTerm = error "illegal simple term"

convertFunctionType (TypeForall (TypePattern x κ) σ) = withSimplify (Map.insert x κ) $ convertFunctionType σ
convertFunctionType (MonoType (Type (FunctionLiteralType σ _ τ))) = do
  σ' <- convertType σ
  τ' <- convertType τ
  pure $ SimpleFunctionType σ' τ'
convertFunctionType _ = error "failed to convert function type"

convertFunction (TermScheme _ (TypeAbstraction (TypePattern x κ) e)) = withSimplify (Map.insert x κ) $ convertFunction e
convertFunction (TermScheme _ (MonoTerm (Term p (FunctionLiteral (TermBound pm e) _ _)))) = do
  pm' <- convertTermMetaPattern pm
  e' <- convertTerm e
  pure $ SimpleFunction p $ SimpleBound pm' e'
convertFunction _ = error "failed to convert function"

simplePatternType :: SimplePattern p -> SimpleType
simplePatternType (SimplePattern _ (RuntimePatternVariable _ σ)) = σ
simplePatternType (SimplePattern _ (RuntimePatternTuple pms)) = SimpleType $ StructRep $ map simplePatternType pms
simplePatternType (SimplePattern _ (RuntimePatternBoolean _)) = SimpleType $ WordRep Byte
