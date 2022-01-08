module Simple where

import Ast.Common
import Ast.Kind
import Ast.Term
import Ast.Type
import Control.Monad.Reader (ReaderT, ask, withReaderT)
import Data.Set (Set, singleton)
import Data.Void (Void, absurd)
import Misc.MonoidMap (Map)
import qualified Misc.MonoidMap as Map
import Misc.Symbol
import TypeCheck.Unify

data SimpleType = SimpleType (KindRuntime KindSize SimpleType)

data SimplePattern p = SimplePattern p (PatternCommon SimpleType (SimplePattern p))

data SimpleTerm p = SimpleTerm p (TermRuntime () KindSignedness () SimpleType (Bound (SimplePattern p) (SimpleTerm p)) () (SimpleTerm p))

data SimpleFunction p = SimpleFunction p (Bound (SimplePattern p) (SimpleTerm p))

data SimpleFunctionType = SimpleFunctionType SimpleType SimpleType

externalImpl :: SimpleTerm p -> Set String
externalImpl (SimpleTerm _ (Variable _ ())) = mempty
externalImpl (SimpleTerm _ (Extern (Symbol sym) _ _ _)) = singleton sym
externalImpl (SimpleTerm _ (Alias e (Bound _ e'))) = externalImpl e <> externalImpl e'
externalImpl (SimpleTerm _ (FunctionApplication e e' _)) = externalImpl e <> externalImpl e'
externalImpl (SimpleTerm _ (PairIntroduction e e')) = externalImpl e <> externalImpl e'
externalImpl (SimpleTerm _ (ReadReference e)) = externalImpl e
externalImpl (SimpleTerm _ (NumberLiteral _)) = mempty
externalImpl (SimpleTerm _ (Arithmatic _ e e' _)) = externalImpl e <> externalImpl e'

external (SimpleFunction _ (Bound _ e)) = externalImpl e

convertKindImpl :: Kind Void p -> SimpleType
convertKindImpl (CoreKind _ (KindRuntime PointerRep)) = SimpleType $ PointerRep
convertKindImpl (CoreKind _ (KindRuntime (StructRep ρs))) = SimpleType $ StructRep (convertKindImpl <$> ρs)
convertKindImpl (CoreKind _ (KindRuntime (WordRep (CoreKind _ (KindSize Byte))))) = SimpleType $ WordRep Byte
convertKindImpl (CoreKind _ (KindRuntime (WordRep (CoreKind _ (KindSize Short))))) = SimpleType $ WordRep Short
convertKindImpl (CoreKind _ (KindRuntime (WordRep (CoreKind _ (KindSize Int))))) = SimpleType $ WordRep Int
convertKindImpl (CoreKind _ (KindRuntime (WordRep (CoreKind _ (KindSize Long))))) = SimpleType $ WordRep Long
convertKindImpl _ = simpleFailType

simpleFailType = error "illegal simple type"

convertKind :: Kind Void p -> SimpleType
convertKind (CoreKind _ (Pretype (CoreKind _ (Real κ)))) = convertKindImpl κ
convertKind _ = simpleFailType

reconstruct :: Monad m => TypeInfer -> ReaderT (Map TypeIdentifier KindInfer) m KindInfer
reconstruct = reconstructType indexVariable absurd augment
  where
    indexVariable x = (Map.! x) <$> ask
    augment (Pattern _ x κ) _ = withReaderT (Map.insert x κ)

convertType σ = convertKind <$> reconstruct σ

convertFunctionType (CoreType _ (ExplicitForall (Bound (Pattern _ x κ) σ) _)) = withReaderT (Map.insert x κ) $ convertFunctionType σ
convertFunctionType (CoreType _ (FunctionLiteralType σ _ τ)) = do
  σ' <- convertType σ
  τ' <- convertType τ
  pure $ SimpleFunctionType σ' τ'
convertFunctionType _ = error "failed to convert function type"

convertTermPattern :: Monad m => TermPattern θ KindInfer TypeInfer p -> ReaderT (Map TypeIdentifier KindInfer) m (SimplePattern p)
convertTermPattern (CoreTermPattern p (PatternCommon (PatternVariable x σ))) = do
  σ' <- convertType σ
  pure $ SimplePattern p $ PatternVariable x σ'
convertTermPattern (CoreTermPattern p (PatternCommon (PatternPair pm1 pm2))) = do
  pm1' <- convertTermPattern pm1
  pm2' <- convertTermPattern pm2
  pure $ SimplePattern p $ PatternPair pm1' pm2'
convertTermPattern (CoreTermPattern _ (PatternOfCourse pm)) = convertTermPattern pm

simpleFailPattern = error "illegal simple pattern"

convertTerm :: Monad m => Term θ KindInfer TypeInfer p -> ReaderT (Map TypeIdentifier KindInfer) m (SimpleTerm p)
convertTerm (CoreTerm p (TermRuntime (Variable x _))) = pure $ SimpleTerm p (Variable x ())
convertTerm (CoreTerm p (TermRuntime (Extern sym σ _ τ))) = do
  σ' <- convertType σ
  τ' <- convertType τ
  pure $ SimpleTerm p $ Extern sym σ' () τ'
convertTerm (CoreTerm p (TermRuntime (FunctionApplication e1 e2 σ))) = do
  e1' <- convertTerm e1
  e2' <- convertTerm e2
  σ' <- convertType σ
  pure $ SimpleTerm p $ FunctionApplication e1' e2' σ'
convertTerm (CoreTerm p (TermRuntime (Alias e1 (Bound pm e2)))) = do
  e1' <- convertTerm e1
  pm' <- convertTermPattern pm
  e2' <- convertTerm e2
  pure $ SimpleTerm p $ Alias e1' (Bound pm' e2')
convertTerm (CoreTerm p (TermRuntime (PairIntroduction e1 e2))) = do
  e1' <- convertTerm e1
  e2' <- convertTerm e2
  pure $ SimpleTerm p $ PairIntroduction e1' e2'
convertTerm (CoreTerm p (TermRuntime (ReadReference e))) = do
  e' <- convertTerm e
  pure $ SimpleTerm p $ ReadReference e'
convertTerm (CoreTerm p (TermRuntime (NumberLiteral n))) = do
  pure $ SimpleTerm p $ NumberLiteral n
convertTerm (CoreTerm p (TermRuntime (Arithmatic o e1 e2 κ))) = do
  e1' <- convertTerm e1
  e2' <- convertTerm e2
  pure $ SimpleTerm p $ Arithmatic o e1' e2' s
  where
    s = case κ of
      CoreKind Internal (KindSignedness Signed) -> Signed
      CoreKind Internal (KindSignedness Unsigned) -> Unsigned
      _ -> error "bad sign"
convertTerm (CoreTerm _ (TypeAbstraction (Bound (Pattern _ x κ) e) _)) = withReaderT (Map.insert x κ) $ convertTerm e
convertTerm (CoreTerm _ (TypeApplication e _ _ _)) = convertTerm e
convertTerm (CoreTerm _ (MacroAbstraction _)) = simpleFailTerm
convertTerm (CoreTerm _ (MacroApplication _ _ _)) = simpleFailTerm
convertTerm (CoreTerm _ (OfCourseIntroduction _)) = simpleFailTerm
convertTerm (CoreTerm _ (Bind _ _)) = simpleFailTerm
convertTerm (CoreTerm _ (FunctionLiteral _)) = simpleFailTerm

simpleFailTerm = error "illegal simple term"

convertFunction (CoreTerm _ (TypeAbstraction (Bound (Pattern _ x κ) e) _)) = withReaderT (Map.insert x κ) $ convertFunction e
convertFunction (CoreTerm p (FunctionLiteral (Bound pm e))) = do
  pm' <- convertTermPattern pm
  e' <- convertTerm e
  pure $ SimpleFunction p $ Bound pm' e'
convertFunction _ = error "failed to convert function"

convertTermAnnotate :: Monad m => Term θ KindInfer TypeInfer p -> TypeSchemeInfer -> ReaderT (Map TypeIdentifier KindInfer) m (SimpleFunction p, SimpleFunctionType)
convertTermAnnotate e (CoreTypeScheme _ (MonoType σ)) = do
  e' <- convertFunction e
  σ' <- convertFunctionType σ
  pure (e', σ')
convertTermAnnotate e (CoreTypeScheme _ (Forall (Bound (Pattern _ x κ) σ) _)) = withReaderT (Map.insert x κ) $ convertTermAnnotate e σ
convertTermAnnotate _ (CoreTypeScheme _ (KindForall _)) = error "kind forall in simple term"

simplePatternType :: SimplePattern p -> SimpleType
simplePatternType (SimplePattern _ (PatternVariable _ σ)) = σ
simplePatternType (SimplePattern _ (PatternPair pm pm')) = SimpleType $ StructRep [simplePatternType pm, simplePatternType pm']
