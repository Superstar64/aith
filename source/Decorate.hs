module Decorate where

import Control.Monad.Reader (ReaderT, ask, withReaderT)
import Data.Set (Set, singleton)
import Data.Void (Void)
import Language.Ast.Common
import Language.Ast.Kind
import Language.Ast.Term
import Language.Ast.Type
import Language.TypeCheck
import Misc.MonoidMap (Map, (!))
import qualified Misc.MonoidMap as Map
import Misc.Symbol

data TypeDecorated = TypeDecorated (KindRuntime KindSize TypeDecorated)

data PatternDecorated p = PatternDecorated p (PatternCommon TypeDecorated (PatternDecorated p))

instance Functor PatternDecorated where
  fmap f (PatternDecorated p pm) = PatternDecorated (f p) $ case pm of
    PatternVariable x σ -> PatternVariable x σ
    RuntimePatternPair pm1 pm2 -> RuntimePatternPair (f <$> pm1) (f <$> pm2)

data TermDecerated p = TermDecerated p (TermRuntime () KindSignedness TypeDecorated (Bound (PatternDecorated p) (TermDecerated p)) () (TermDecerated p))

instance Functor TermDecerated where
  fmap f (TermDecerated p e) = TermDecerated (f p) $ case e of
    Variable x () -> Variable x ()
    Alias e1 (Bound pm e2) -> Alias (f <$> e1) (Bound (f <$> pm) (f <$> e2))
    Extern sm σ τ -> Extern sm σ τ
    RuntimePairIntroduction e1 e2 -> RuntimePairIntroduction (f <$> e1) (f <$> e2)
    FunctionApplication e1 e2 σ -> FunctionApplication (f <$> e1) (f <$> e2) σ
    ReadReference () e σ -> ReadReference () (f <$> e) σ
    FunctionLiteral (Bound pm e) -> FunctionLiteral (Bound (f <$> pm) (f <$> e))
    NumberLiteral n σ -> NumberLiteral n σ
    Arithmatic o e e' s -> Arithmatic o (fmap f e) (fmap f e') s

external :: TermDecerated p -> Set String
external (TermDecerated _ (Variable _ ())) = mempty
external (TermDecerated _ (Extern (Symbol sym) _ _)) = singleton sym
external (TermDecerated _ (Alias e (Bound _ e'))) = external e <> external e'
external (TermDecerated _ (FunctionApplication e e' _)) = external e <> external e'
external (TermDecerated _ (RuntimePairIntroduction e e')) = external e <> external e'
external (TermDecerated _ (FunctionLiteral (Bound _ e))) = external e
external (TermDecerated _ (ReadReference _ e _)) = external e
external (TermDecerated _ (NumberLiteral _ _)) = mempty
external (TermDecerated _ (Arithmatic _ e e' _)) = external e <> external e'

decorateImpl :: Kind Void p -> TypeDecorated
decorateImpl (CoreKind _ (KindRuntime PointerRep)) = TypeDecorated $ PointerRep
decorateImpl (CoreKind _ (KindRuntime (StructRep ρs))) = TypeDecorated $ StructRep (decorateImpl <$> ρs)
decorateImpl (CoreKind _ (KindRuntime (WordRep (CoreKind _ (KindSize Byte))))) = TypeDecorated $ WordRep Byte
decorateImpl (CoreKind _ (KindRuntime (WordRep (CoreKind _ (KindSize Short))))) = TypeDecorated $ WordRep Short
decorateImpl (CoreKind _ (KindRuntime (WordRep (CoreKind _ (KindSize Int))))) = TypeDecorated $ WordRep Int
decorateImpl (CoreKind _ (KindRuntime (WordRep (CoreKind _ (KindSize Long))))) = TypeDecorated $ WordRep Long
decorateImpl _ = error "unable to decorate kind"

decoration (CoreKind _ (Type (CoreKind _ (Runtime _ (CoreKind _ (Real κ)))))) = decorateImpl κ
decoration _ = error "unable to decorate kind"

decorateTermPattern :: Monad m => TermPattern θ KindInfer TypeInfer p -> ReaderT (Map TypeIdentifier KindInfer) m (PatternDecorated p)
decorateTermPattern (CoreTermPattern p (PatternCommon (PatternVariable x σ))) = do
  σ' <- decoration <$> reconstruct σ
  pure $ PatternDecorated p $ PatternVariable x σ'
decorateTermPattern (CoreTermPattern p (PatternCommon (RuntimePatternPair pm1 pm2))) = do
  pm1' <- decorateTermPattern pm1
  pm2' <- decorateTermPattern pm2
  pure $ PatternDecorated p $ RuntimePatternPair pm1' pm2'
decorateTermPattern (CoreTermPattern _ (PatternCopy _ pm)) = decorateTermPattern pm
decorateTermPattern _ = error "unable to decerate pattern"

decorateTerm :: Monad m => Term θ KindInfer TypeInfer p -> ReaderT (Map TypeIdentifier KindInfer) m (TermDecerated p)
decorateTerm (CoreTerm p (TermRuntime (Variable x _))) = pure $ TermDecerated p (Variable x ())
decorateTerm (CoreTerm p (TermRuntime (Extern sym σ τ))) = do
  σ' <- decoration <$> reconstruct σ
  τ' <- decoration <$> reconstruct τ
  pure $ TermDecerated p $ Extern sym σ' τ'
decorateTerm (CoreTerm p (TermRuntime (FunctionApplication e1 e2 σ))) = do
  e1' <- decorateTerm e1
  e2' <- decorateTerm e2
  σ' <- decoration <$> reconstruct σ
  pure $ TermDecerated p $ FunctionApplication e1' e2' σ'
decorateTerm (CoreTerm p (TermRuntime (Alias e1 (Bound pm e2)))) = do
  e1' <- decorateTerm e1
  pm' <- decorateTermPattern pm
  e2' <- decorateTerm e2
  pure $ TermDecerated p $ Alias e1' (Bound pm' e2')
decorateTerm (CoreTerm p (TermRuntime (RuntimePairIntroduction e1 e2))) = do
  e1' <- decorateTerm e1
  e2' <- decorateTerm e2
  pure $ TermDecerated p $ RuntimePairIntroduction e1' e2'
decorateTerm (CoreTerm p (TermRuntime (FunctionLiteral (Bound pm e)))) = do
  pm' <- decorateTermPattern pm
  e' <- decorateTerm e
  pure $ TermDecerated p $ FunctionLiteral $ Bound pm' e'
decorateTerm (CoreTerm p (TermRuntime (ReadReference _ e σ))) = do
  e' <- decorateTerm e
  σ' <- decoration <$> reconstruct σ
  pure $ TermDecerated p $ ReadReference () e' σ'
decorateTerm (CoreTerm p (TermRuntime (NumberLiteral n σ))) = do
  σ' <- decoration <$> reconstruct σ
  pure $ TermDecerated p $ NumberLiteral n σ'
decorateTerm (CoreTerm p (TermRuntime (Arithmatic o e1 e2 κ))) = do
  e1' <- decorateTerm e1
  e2' <- decorateTerm e2
  pure $ TermDecerated p $ Arithmatic o e1' e2' s
  where
    s = case κ of
      CoreKind Internal (KindSignedness Signed) -> Signed
      CoreKind Internal (KindSignedness Unsigned) -> Unsigned
      _ -> error "bad sign"
decorateTerm (CoreTerm _ (PureRegionTransformer e)) = decorateTerm e
decorateTerm (CoreTerm p (DoRegionTransformer e (Bound pm e'))) =
  decorateTerm (CoreTerm p $ TermRuntime $ Alias e (Bound pm e'))
decorateTerm (CoreTerm _ (ImplicationAbstraction (Bound _ e))) = decorateTerm e
decorateTerm (CoreTerm _ (ImplicationApplication _ e)) = decorateTerm e
decorateTerm _ = error "decorate illegal term"

decorateTermAnnotate :: Monad m => Term θ KindInfer TypeInfer p -> TypeSchemeInfer -> ReaderT (Map TypeIdentifier KindInfer) m (TermDecerated p)
decorateTermAnnotate e (CoreTypeScheme _ (MonoType _)) = decorateTerm e
decorateTermAnnotate e (CoreTypeScheme _ (Forall (Bound (Pattern _ x κ) σ))) = withReaderT (Map.insert x κ) $ decorateTermAnnotate e σ
decorateTermAnnotate _ (CoreTypeScheme _ (KindForall _)) = error "kind forall in decorated term"

decorateAugment (PatternDecorated _ (PatternVariable x σ)) e = withReaderT (Map.insert x σ) e
decorateAugment (PatternDecorated _ (RuntimePatternPair pm pm')) e = decorateAugment pm (decorateAugment pm' e)

decorateTypeCheck :: Monad m => TermDecerated p -> ReaderT (Map TermIdentifier TypeDecorated) m (TermDecerated (p, TypeDecorated))
decorateTypeCheck (TermDecerated p (Variable x ())) = do
  σΓ <- ask
  pure $ TermDecerated (p, σΓ ! x) (Variable x ())
decorateTypeCheck (TermDecerated p (Extern sm σ τ)) = pure $ TermDecerated (p, TypeDecorated PointerRep) (Extern sm σ τ)
decorateTypeCheck (TermDecerated p (FunctionApplication e1 e2 σ)) = do
  e1' <- decorateTypeCheck e1
  e2' <- decorateTypeCheck e2
  pure $ TermDecerated (p, σ) (FunctionApplication e1' e2' σ)
decorateTypeCheck (TermDecerated p (Alias e1 (Bound pm e2))) = do
  e1' <- decorateTypeCheck e1
  e2'@(TermDecerated (_, σ) _) <- decorateAugment pm $ decorateTypeCheck e2
  let pm' = decorateTypeCheckPattern pm
  pure $ TermDecerated (p, σ) (Alias e1' (Bound pm' e2'))
decorateTypeCheck (TermDecerated p (RuntimePairIntroduction e1 e2)) = do
  e1'@(TermDecerated (_, σ1) _) <- decorateTypeCheck e1
  e2'@(TermDecerated (_, σ2) _) <- decorateTypeCheck e2
  pure $ TermDecerated (p, TypeDecorated $ StructRep [σ1, σ2]) (RuntimePairIntroduction e1' e2')
decorateTypeCheck (TermDecerated p (ReadReference () e σ)) = do
  e' <- decorateTypeCheck e
  pure $ TermDecerated (p, σ) (ReadReference () e' σ)
decorateTypeCheck (TermDecerated p (FunctionLiteral (Bound pm e))) = do
  e' <- decorateAugment pm $ decorateTypeCheck e
  let pm' = decorateTypeCheckPattern pm
  pure $ TermDecerated (p, error "type of function") (FunctionLiteral (Bound pm' e'))
decorateTypeCheck (TermDecerated p (NumberLiteral n σ)) = do
  pure $ TermDecerated (p, σ) (NumberLiteral n σ)
decorateTypeCheck (TermDecerated p (Arithmatic o e1 e2 s)) = do
  e1'@(TermDecerated (_, σ) _) <- decorateTypeCheck e1
  e2' <- decorateTypeCheck e2
  pure $ TermDecerated (p, σ) (Arithmatic o e1' e2' s)

decorateTypeCheckPattern :: PatternDecorated p -> PatternDecorated (p, TypeDecorated)
decorateTypeCheckPattern (PatternDecorated p (PatternVariable x σ)) = PatternDecorated (p, σ) (PatternVariable x σ)
decorateTypeCheckPattern (PatternDecorated p (RuntimePatternPair pm1 pm2)) = PatternDecorated (p, TypeDecorated $ StructRep [σ, τ]) (RuntimePatternPair pm1' pm2')
  where
    pm1'@(PatternDecorated (_, σ) _) = decorateTypeCheckPattern pm1
    pm2'@(PatternDecorated (_, τ) _) = decorateTypeCheckPattern pm2
