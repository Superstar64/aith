module Simple where

import Ast.Common
import Ast.Term hiding (convertTerm)
import Ast.Type hiding (convertType)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (Reader, ReaderT, ask, runReader, runReaderT, withReaderT)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Void (absurd)
import TypeCheck.Unify hiding (reconstruct)

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
convertKindImpl (TypeCore (KindRuntime PointerRep)) = SimpleType $ PointerRep
convertKindImpl (TypeCore (KindRuntime (StructRep ρs))) = SimpleType $ StructRep (convertKindImpl <$> ρs)
convertKindImpl (TypeCore (KindRuntime (UnionRep ρs))) = SimpleType $ UnionRep (convertKindImpl <$> ρs)
convertKindImpl (TypeCore (KindRuntime (WordRep (TypeCore (KindSize Byte))))) = SimpleType $ WordRep Byte
convertKindImpl (TypeCore (KindRuntime (WordRep (TypeCore (KindSize Short))))) = SimpleType $ WordRep Short
convertKindImpl (TypeCore (KindRuntime (WordRep (TypeCore (KindSize Int))))) = SimpleType $ WordRep Int
convertKindImpl (TypeCore (KindRuntime (WordRep (TypeCore (KindSize Long))))) = SimpleType $ WordRep Long
convertKindImpl (TypeCore (KindRuntime (WordRep (TypeCore (KindSize Native))))) = SimpleType $ WordRep Native
convertKindImpl _ = simpleFailType

simpleFailType = error "illegal simple type"

convertKind :: TypeInfer -> SimpleType
convertKind (TypeCore (Pretype κ _)) = convertKindImpl κ
convertKind _ = simpleFailType

reconstruct (TypeCore σ) = reconstructF index indexGlobal absurd todo checkRuntime reconstruct σ
  where
    todo = error "poly type in runtime types"
    index x = do
      map <- Simplify ask
      pure $ map ! x
    indexGlobal x = do
      map <- Simplify $ lift ask
      pure $ map ! x
    checkRuntime (TypeCore (Pretype κ _)) = pure κ
    checkRuntime _ = error "reconstruction of pair didn't return pretype"

convertType σ = convertKind <$> reconstruct σ

convertTermPattern (TermRuntimePatternCore p (RuntimePatternVariable x σ)) = do
  σ' <- convertType σ
  pure $ SimplePattern p $ RuntimePatternVariable x σ'
convertTermPattern (TermRuntimePatternCore p (RuntimePatternTuple pms)) = do
  pms <- traverse convertTermPattern pms
  pure $ SimplePattern p $ RuntimePatternTuple pms

simpleFailPattern = error "illegal simple pattern"

convertTerm (TermCore p (TermRuntime (Variable x _))) = pure $ SimpleTerm p (Variable x ())
convertTerm (TermCore p (TermRuntime (Extern sym σ _ τ))) = do
  σ' <- convertType σ
  τ' <- convertType τ
  pure $ SimpleTerm p $ Extern sym σ' () τ'
convertTerm (TermCore p (TermRuntime (FunctionApplication e1 e2 σ))) = do
  e1' <- convertTerm e1
  e2' <- convertTerm e2
  σ' <- convertType σ
  pure $ SimpleTerm p $ FunctionApplication e1' e2' σ'
convertTerm (TermCore p (TermRuntime (Alias e1 (Bound pm e2)))) = do
  e1' <- convertTerm e1
  pm' <- convertTermPattern pm
  e2' <- convertTerm e2
  pure $ SimpleTerm p $ Alias e1' (Bound pm' e2')
convertTerm (TermCore p (TermRuntime (TupleIntroduction es))) = do
  es <- traverse convertTerm es
  pure $ SimpleTerm p $ TupleIntroduction es
convertTerm (TermCore p (TermRuntime (ReadReference e))) = do
  e' <- convertTerm e
  pure $ SimpleTerm p $ ReadReference e'
convertTerm (TermCore p (TermRuntime (WriteReference ep ev σ))) = do
  ep <- convertTerm ep
  ev <- convertTerm ev
  σ <- convertType σ
  pure $ SimpleTerm p $ WriteReference ep ev σ
convertTerm (TermCore p (TermRuntime (NumberLiteral n))) = do
  pure $ SimpleTerm p $ NumberLiteral n
convertTerm (TermCore p (TermRuntime (Arithmatic o e1 e2 κ))) = do
  e1' <- convertTerm e1
  e2' <- convertTerm e2
  pure $ SimpleTerm p $ Arithmatic o e1' e2' s
  where
    s = case κ of
      TypeCore (KindSignedness Signed) -> Signed
      TypeCore (KindSignedness Unsigned) -> Unsigned
      _ -> error "bad sign"
convertTerm (TermCore p (TermRuntime (Relational o e1 e2 σ κ))) = do
  e1' <- convertTerm e1
  e2' <- convertTerm e2
  σ <- convertType σ
  pure $ SimpleTerm p $ Relational o e1' e2' σ s
  where
    s = case κ of
      TypeCore (KindSignedness Signed) -> Signed
      TypeCore (KindSignedness Unsigned) -> Unsigned
      _ -> error "bad sign"
convertTerm (TermCore p (TermRuntime (BooleanLiteral b))) = pure $ SimpleTerm p $ BooleanLiteral b
convertTerm (TermCore p (TermRuntime (If eb et ef))) = do
  eb <- convertTerm eb
  et <- convertTerm et
  ef <- convertTerm ef
  pure $ SimpleTerm p $ If eb et ef
convertTerm (TermCore p (TermRuntime (PointerIncrement ep ei σ))) = do
  ep <- convertTerm ep
  ei <- convertTerm ei
  σ <- convertType σ
  pure $ SimpleTerm p $ PointerIncrement ep ei σ
convertTerm (TermCore p (TermRuntime (Continue e))) = do
  e <- convertTerm e
  pure $ SimpleTerm p $ Continue e
convertTerm (TermCore p (TermRuntime (Break e))) = do
  e <- convertTerm e
  pure $ SimpleTerm p $ Break e
convertTerm (TermCore p (TermRuntime (Loop e1 (Bound pm e2)))) = do
  e1' <- convertTerm e1
  pm' <- convertTermPattern pm
  e2' <- convertTerm e2
  pure $ SimpleTerm p $ Loop e1' (Bound pm' e2')
convertTerm (TermCore p (TermErasure (Borrow ep (Bound (TypePattern α κ _) (Bound pm@(TermRuntimePatternCore _ (RuntimePatternVariable x _)) e))))) = do
  ep <- convertTerm ep
  withSimplify (Map.insert α κ) $ do
    pm <- convertTermPattern pm
    e <- convertTerm e
    pure $ SimpleTerm p $ Alias ep (Bound pm $ SimpleTerm p $ TupleIntroduction [e, SimpleTerm p $ Variable x ()])
convertTerm (TermCore _ (TermErasure (Wrap _ e))) = convertTerm e
convertTerm (TermCore _ (TermErasure (Unwrap _ e))) = convertTerm e
convertTerm (TermCore _ (TermErasure (Borrow _ _))) = simpleFailTerm
convertTerm (TermCore _ (TermErasure (IsolatePointer e))) = convertTerm e
convertTerm (TermCore _ (PolyIntroduction _)) = simpleFailTerm
convertTerm (TermCore _ (PolyElimination _ _ _)) = simpleFailPattern
convertTerm (TermCore _ (InlineAbstraction _)) = simpleFailTerm
convertTerm (TermCore _ (InlineApplication _ _ _)) = simpleFailTerm
convertTerm (TermCore _ (Bind _ _)) = simpleFailTerm
convertTerm (TermCore _ (FunctionLiteral _)) = simpleFailTerm
convertTerm (TermCore _ (Annotation invalid)) = absurd invalid
convertTerm (TermCore _ (TermSugar _)) = simpleFailTerm
convertTerm (TermCore _ (GlobalVariable _ _)) = simpleFailTerm

simpleFailTerm = error "illegal simple term"

convertFunctionType (TypeSchemeCore (TypeForall (Bound (TypePattern x κ _) σ))) = withSimplify (Map.insert x κ) $ convertFunctionType σ
convertFunctionType (TypeSchemeCore (MonoType (TypeCore (FunctionLiteralType σ _ τ)))) = do
  σ' <- convertType σ
  τ' <- convertType τ
  pure $ SimpleFunctionType σ' τ'
convertFunctionType _ = error "failed to convert function type"

convertFunction (TermSchemeCore _ (TypeAbstraction (Bound (TypePattern x κ _) e))) = withSimplify (Map.insert x κ) $ convertFunction e
convertFunction (TermSchemeCore _ (MonoTerm (TermCore p (FunctionLiteral (Bound pm e))))) = do
  pm' <- convertTermPattern pm
  e' <- convertTerm e
  pure $ SimpleFunction p $ Bound pm' e'
convertFunction _ = error "failed to convert function"

simplePatternType :: SimplePattern p -> SimpleType
simplePatternType (SimplePattern _ (RuntimePatternVariable _ σ)) = σ
simplePatternType (SimplePattern _ (RuntimePatternTuple pms)) = SimpleType $ StructRep $ map simplePatternType pms
