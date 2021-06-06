module Decorate where

import qualified C.Ast as C
import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.RuntimePattern
import Core.Ast.Term
import Core.TypeCheck
import Data.Functor.Identity
import qualified Data.Map as Map

data PatternDecorated p = PatternDecorated (C.Representation C.RepresentationFix) p (PatternCommon () (PatternDecorated p))

data TermDecerated p = TermDecerated p (TermCommon (C.Representation C.RepresentationFix) () (PatternDecorated p) (TermDecerated p))

decorateImpl (CoreKind _ PointerRep) = C.Pointer
decorateImpl (CoreKind _ (StructRep ρs)) = C.Struct $ C.RepresentationFix $ decorateImpl <$> ρs
decorateImpl _ = error "unable to decorate kind"

decoration (CoreKind _ (Type (CoreKind _ (Runtime κ)))) = decorateImpl κ
decoration _ = error "unable to decorate kind"

augmentVariable p x σ e = modifyTypeEnvironment (Map.insert x (p, Unrestricted, σ)) e

augmentPattern (CoreRuntimePattern p (PatternCommon (RuntimePatternVariable x σ))) e = augmentVariable p x σ e
augmentPattern (CoreRuntimePattern _ (PatternCommon (RuntimePatternPair pm pm'))) e = augmentPattern pm (augmentPattern pm' e)

decoratePattern (CoreRuntimePattern p (PatternCommon (RuntimePatternVariable x σ))) = do
  dσ <- decoration <$> typeCheck σ
  pure $ PatternDecorated dσ p (RuntimePatternVariable x ())
decoratePattern (CoreRuntimePattern p (PatternCommon (RuntimePatternPair pm1 pm2))) = do
  pm1'@(PatternDecorated d1 _ _) <- decoratePattern pm1
  pm2'@(PatternDecorated d2 _ _) <- decoratePattern pm2
  pure $ PatternDecorated (C.Struct $ C.RepresentationFix [d1, d2]) p (RuntimePatternPair pm1' pm2')

decorateTerm (CoreTerm p (TermCommon (Variable x))) = pure $ TermDecerated p (Variable x)
decorateTerm (CoreTerm p (TermCommon (Extern _ _ sm σ τ))) = do
  dσ <- decoration <$> typeCheck σ
  dτ <- decoration <$> typeCheck τ
  pure $ TermDecerated p (Extern dσ dτ sm () ())
decorateTerm e@(CoreTerm p (TermCommon (FunctionApplication _ _ e1 e2))) = do
  dσ <- decoration <$> (typeCheck =<< typeCheck e)
  dτ <- decoration <$> (typeCheck =<< typeCheck e2)
  e1' <- decorateTerm e1
  e2' <- decorateTerm e2
  pure $ TermDecerated p (FunctionApplication dσ dτ e1' e2')
decorateTerm (CoreTerm _ (TypeAbstraction (Bound pmσ e))) = augment pmσ $ decorateTerm e
decorateTerm (CoreTerm _ (TypeApplication e _)) = decorateTerm e
decorateTerm (CoreTerm p (TermCommon (FunctionLiteral () (Bound pm e)))) = do
  dpm <- decoratePattern pm
  e' <- augmentPattern pm (decorateTerm e)
  dτ <- decoration <$> augmentPattern pm (typeCheck =<< typeCheck e)
  pure $ TermDecerated p $ FunctionLiteral dτ (Bound dpm e')
decorateTerm (CoreTerm _ (ErasedQualifiedAssume _ e)) = decorateTerm e
decorateTerm (CoreTerm _ (ErasedQualifiedCheck e)) = decorateTerm e
decorateTerm (CoreTerm p (TermCommon (Alias e1 (Bound pm e2)))) = do
  pm' <- decoratePattern pm
  e1' <- decorateTerm e1
  e2' <- augmentPattern pm (decorateTerm e2)
  pure $ TermDecerated p (Alias e1' (Bound pm' e2'))
decorateTerm (CoreTerm p (TermCommon (RuntimePairIntroduction () e1 e2))) = do
  e1' <- decorateTerm e1
  e2' <- decorateTerm e2
  de1 <- decoration <$> (typeCheck =<< typeCheck e1)
  de2 <- decoration <$> (typeCheck =<< typeCheck e2)
  let dσ = C.Struct $ C.RepresentationFix [de1, de2]
  pure (TermDecerated p (RuntimePairIntroduction dσ e1' e2'))
decorateTerm (CoreTerm _ (Pack _ e)) = decorateTerm e
decorateTerm (CoreTerm _ (Unpack e)) = decorateTerm e
decorateTerm _ = error "unable to decorate term"

runDecorate :: Core.TypeCheck.Core Internal Identity a -> a
runDecorate e = runIdentity $ runCore e emptyState
