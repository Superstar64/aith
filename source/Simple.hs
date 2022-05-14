module Simple where

import Ast.Common
import Ast.Kind hiding (convertKind)
import Ast.Term hiding (convertTerm)
import Ast.Type hiding (convertType)
import Control.Monad.Trans.Reader (ReaderT, ask, runReader, withReaderT)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set, singleton)
import Data.Void (absurd)
import Misc.Symbol
import TypeCheck.Unify

data SimpleType = SimpleType (KindRuntime KindSize SimpleType) deriving (Eq, Ord)

data SimplePattern p = SimplePattern p (TermRuntimePatternF SimpleType (SimplePattern p))

data SimpleTerm p = SimpleTerm p (TermRuntime () KindSignedness SimpleType () SimpleType (Bound (SimplePattern p)) (SimpleTerm p))

data SimpleFunction p = SimpleFunction p (Bound (SimplePattern p) (SimpleTerm p))

data SimpleFunctionType = SimpleFunctionType SimpleType SimpleType

externalImpl :: SimpleTerm p -> Set String
externalImpl (SimpleTerm _ (Variable _ ())) = mempty
externalImpl (SimpleTerm _ (Extern (Symbol sym) _ _ _)) = singleton sym
externalImpl (SimpleTerm _ (Alias e (Bound _ e'))) = externalImpl e <> externalImpl e'
externalImpl (SimpleTerm _ (FunctionApplication e e' _)) = externalImpl e <> externalImpl e'
externalImpl (SimpleTerm _ (TupleIntroduction es)) = foldMap externalImpl es
externalImpl (SimpleTerm _ (ReadReference e)) = externalImpl e
externalImpl (SimpleTerm _ (WriteReference ep ev _)) = externalImpl ep <> externalImpl ev
externalImpl (SimpleTerm _ (NumberLiteral _)) = mempty
externalImpl (SimpleTerm _ (Arithmatic _ e e' _)) = externalImpl e <> externalImpl e'
externalImpl (SimpleTerm _ (Relational _ e e' _ _)) = externalImpl e <> externalImpl e'
externalImpl (SimpleTerm _ (BooleanLiteral _)) = mempty
externalImpl (SimpleTerm _ (If eb et ef)) = externalImpl eb <> externalImpl et <> externalImpl ef

external (SimpleFunction _ (Bound _ e)) = externalImpl e

mangleType :: SimpleType -> String
mangleType (SimpleType PointerRep) = "p"
mangleType (SimpleType (StructRep σs)) = "s" ++ (σs >>= mangleType) ++ "e"
mangleType (SimpleType (WordRep Byte)) = "b"
mangleType (SimpleType (WordRep Short)) = "s"
mangleType (SimpleType (WordRep Int)) = "i"
mangleType (SimpleType (WordRep Long)) = "l"
mangleType (SimpleType (WordRep Native)) = "n"

convertKindImpl :: KindInfer -> SimpleType
convertKindImpl (KindCore (KindRuntime PointerRep)) = SimpleType $ PointerRep
convertKindImpl (KindCore (KindRuntime (StructRep ρs))) = SimpleType $ StructRep (convertKindImpl <$> ρs)
convertKindImpl (KindCore (KindRuntime (WordRep (KindCore (KindSize Byte))))) = SimpleType $ WordRep Byte
convertKindImpl (KindCore (KindRuntime (WordRep (KindCore (KindSize Short))))) = SimpleType $ WordRep Short
convertKindImpl (KindCore (KindRuntime (WordRep (KindCore (KindSize Int))))) = SimpleType $ WordRep Int
convertKindImpl (KindCore (KindRuntime (WordRep (KindCore (KindSize Long))))) = SimpleType $ WordRep Long
convertKindImpl (KindCore (KindRuntime (WordRep (KindCore (KindSize Native))))) = SimpleType $ WordRep Native
convertKindImpl _ = simpleFailType

simpleFailType = error "illegal simple type"

convertKind :: KindInfer -> SimpleType
convertKind (KindCore (Pretype κ)) = convertKindImpl κ
convertKind _ = simpleFailType

reconstruct :: Monad m => TypeInfer -> ReaderT (Map TypeIdentifier KindInfer) m KindInfer
reconstruct (TypeCore σ) = reconstructTypeF todo index absurd todo KindCore checkRuntime reconstruct σ
  where
    todo = error "todo fix when type variable are allowed inside runtime types"
    index x = do
      map <- ask
      pure $ map ! x
    checkRuntime (KindCore (Pretype κ)) f = f κ
    checkRuntime _ _ = error $ "reconstruction of pair didn't return pretype"

convertType σ = convertKind <$> reconstruct σ

convertTermPattern :: Monad m => TermRuntimePatternInfer p -> ReaderT (Map TypeIdentifier KindInfer) m (SimplePattern p)
convertTermPattern (TermRuntimePatternCore p (RuntimePatternVariable x σ)) = do
  σ' <- convertType σ
  pure $ SimplePattern p $ RuntimePatternVariable x σ'
convertTermPattern (TermRuntimePatternCore p (RuntimePatternTuple pms)) = do
  pms <- traverse convertTermPattern pms
  pure $ SimplePattern p $ RuntimePatternTuple pms

simpleFailPattern = error "illegal simple pattern"

convertTerm :: Monad m => TermInfer p -> ReaderT (Map TypeIdentifier KindInfer) m (SimpleTerm p)
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
      KindCore (KindSignedness Signed) -> Signed
      KindCore (KindSignedness Unsigned) -> Unsigned
      _ -> error "bad sign"
convertTerm (TermCore p (TermRuntime (Relational o e1 e2 σ κ))) = do
  e1' <- convertTerm e1
  e2' <- convertTerm e2
  σ <- convertType σ
  pure $ SimpleTerm p $ Relational o e1' e2' σ s
  where
    s = case κ of
      KindCore (KindSignedness Signed) -> Signed
      KindCore (KindSignedness Unsigned) -> Unsigned
      _ -> error "bad sign"
convertTerm (TermCore p (TermRuntime (BooleanLiteral b))) = pure $ SimpleTerm p $ BooleanLiteral b
convertTerm (TermCore p (TermRuntime (If eb et ef))) = do
  eb <- convertTerm eb
  et <- convertTerm et
  ef <- convertTerm ef
  pure $ SimpleTerm p $ If eb et ef
convertTerm (TermCore _ (TypeAbstraction _ _ _)) = simpleFailTerm
convertTerm (TermCore _ (TypeApplication _ _ _)) = simpleFailPattern
convertTerm (TermCore _ (InlineAbstraction _)) = simpleFailTerm
convertTerm (TermCore _ (InlineApplication _ _ _)) = simpleFailTerm
convertTerm (TermCore _ (OfCourseIntroduction _)) = simpleFailTerm
convertTerm (TermCore _ (Bind _ _)) = simpleFailTerm
convertTerm (TermCore _ (FunctionLiteral _)) = simpleFailTerm
convertTerm (TermCore _ (TypeAnnotation _ _ invalid)) = absurd invalid
convertTerm (TermCore _ (PretypeAnnotation _ _ invalid)) = absurd invalid

simpleFailTerm = error "illegal simple term"

convertFunctionType :: Monad m => TypeSchemeInfer -> ReaderT (Map TypeIdentifier KindInfer) m SimpleFunctionType
convertFunctionType (TypeSchemeCore (ImplicitForall (Bound (TypePatternCore x κ) σ) _ _)) = withReaderT (Map.insert x κ) $ convertFunctionType σ
convertFunctionType (TypeSchemeCore (MonoType (TypeCore (FunctionLiteralType σ _ τ)))) = do
  σ' <- convertType σ
  τ' <- convertType τ
  pure $ SimpleFunctionType σ' τ'
convertFunctionType _ = error "failed to convert function type"

convertFunction :: Monad m => TermSchemeInfer p -> ReaderT (Map TypeIdentifier KindInfer) m (SimpleFunction p)
convertFunction (TermSchemeCore _ (ImplicitTypeAbstraction (Bound (TypePatternCore x κ) e) _ _)) = withReaderT (Map.insert x κ) $ convertFunction e
convertFunction (TermSchemeCore _ (MonoTerm (TermCore p (FunctionLiteral (Bound pm e))))) = do
  pm' <- convertTermPattern pm
  e' <- convertTerm e
  pure $ SimpleFunction p $ Bound pm' e'
convertFunction _ = error "failed to convert function"

simplePatternType :: SimplePattern p -> SimpleType
simplePatternType (SimplePattern _ (RuntimePatternVariable _ σ)) = σ
simplePatternType (SimplePattern _ (RuntimePatternTuple pms)) = SimpleType $ StructRep $ map simplePatternType pms

simpleFunction :: TermSchemeInfer p -> SimpleFunction p
simpleFunction e = runReader (convertFunction e) Map.empty

simpleFunctionType :: TypeSchemeInfer -> SimpleFunctionType
simpleFunctionType σ = runReader (convertFunctionType σ) Map.empty
