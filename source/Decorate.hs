module Decorate where

import qualified C.Ast as C
import Control.Monad ((<=<))
import Control.Monad.Trans.State (get, put)
import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.RuntimePattern
import Core.Ast.Term
import Core.TypeCheck
import Data.Functor.Identity
import qualified Data.Map as Map
import Misc.Silent

newtype Decorate f = Decorate (f (C.Representation C.RepresentationFix))

decorateImpl (CoreKind _ PointerRep) = C.Pointer
decorateImpl (CoreKind _ (StructRep ρs)) = C.Struct $ C.RepresentationFix $ decorateImpl <$> ρs
decorateImpl _ = error "unable to decorate kind"

decoration (CoreKind _ (Type (CoreKind _ (Runtime κ)))) = decorateImpl κ
decoration _ = error "unable to decorate kind"

augmentVariable p x σ e = do
  env <- Core get
  let σΓ = typeEnvironment env
  Core $ put env {typeEnvironment = Map.insert x (p, Unrestricted, σ) σΓ}
  e' <- e
  Core $ put env
  pure e'

augmentPattern (CoreRuntimePattern Silent p (RuntimePatternVariable x σ)) e = augmentVariable p x σ e
augmentPattern (CoreRuntimePattern Silent _ (RuntimePatternPair pm pm')) e = augmentPattern pm (augmentPattern pm' e)

decoratePattern (CoreRuntimePattern Silent p (RuntimePatternVariable x σ)) = do
  dσ <- decoration <$> typeCheck σ
  pure $ CoreRuntimePattern (Decorate (Identity dσ)) p (RuntimePatternVariable x σ)
decoratePattern (CoreRuntimePattern _ p (RuntimePatternPair pm1 pm2)) = do
  pm1'@(CoreRuntimePattern (Decorate (Identity d1)) _ _) <- decoratePattern pm1
  pm2'@(CoreRuntimePattern (Decorate (Identity d2)) _ _) <- decoratePattern pm2
  pure $ CoreRuntimePattern (Decorate (Identity (C.Struct $ C.RepresentationFix [d1, d2]))) p (RuntimePatternPair pm1' pm2')

decorateTerm e@(CoreTerm p (Variable Silent x)) = do
  dσ <- Identity <$> decoration <$> (typeCheck =<< typeCheck e)
  pure $ CoreTerm p (Variable (Decorate dσ) x)
decorateTerm (CoreTerm p (Extern _ _ sm σ τs)) = do
  dσ <- Identity <$> decoration <$> typeCheck σ
  dτs <- (fmap decoration) <$> traverse typeCheck τs
  pure $ CoreTerm p (Extern (Decorate dσ) (Decorate dτs) sm σ τs)
decorateTerm e@(CoreTerm p (FunctionApplication _ _ e1 e2s)) = do
  dσ <- Identity <$> decoration <$> (typeCheck =<< typeCheck e)
  dτs <- (fmap decoration) <$> traverse (typeCheck <=< typeCheck) e2s
  e1' <- decorateTerm e1
  e2s' <- traverse decorateTerm e2s
  pure $ CoreTerm p (FunctionApplication (Decorate dσ) (Decorate dτs) e1' e2s')
decorateTerm (CoreTerm _ (TypeAbstraction _ (Bound pmσ e))) = augment pmσ $ decorateTerm e
decorateTerm (CoreTerm _ (TypeApplication _ e _)) = decorateTerm e
decorateTerm (CoreTerm p (FunctionLiteral _ (Bound pms e))) = do
  dpms <- traverse decoratePattern pms
  e' <- foldr augmentPattern (decorateTerm e) pms
  dτ <- Identity <$> decoration <$> foldr augmentPattern (typeCheck =<< typeCheck e) pms
  pure $ CoreTerm p $ FunctionLiteral (Decorate dτ) (Bound dpms e')
decorateTerm (CoreTerm _ (ErasedQualifiedAssume _ _ e)) = decorateTerm e
decorateTerm (CoreTerm _ (ErasedQualifiedCheck _ e)) = decorateTerm e
decorateTerm (CoreTerm p (Alias e1 (Bound pm e2))) = do
  pm' <- decoratePattern pm
  e1' <- decorateTerm e1
  e2' <- augmentPattern pm (decorateTerm e2)
  pure $ CoreTerm p (Alias e1' (Bound pm' e2'))
decorateTerm (CoreTerm p (RuntimePairIntroduction _ e1 e2)) = do
  e1' <- decorateTerm e1
  e2' <- decorateTerm e2
  de1 <- decoration <$> (typeCheck =<< typeCheck e1)
  de2 <- decoration <$> (typeCheck =<< typeCheck e2)
  let dσ = Decorate (Identity $ C.Struct $ C.RepresentationFix [de1, de2])
  pure (CoreTerm p (RuntimePairIntroduction dσ e1' e2'))
decorateTerm (CoreTerm _ (Pack _ _ e)) = decorateTerm e
decorateTerm (CoreTerm _ (Unpack _ e)) = decorateTerm e
decorateTerm _ = error "unable to decorate term"

runDecorate :: Core.TypeCheck.Core Internal Identity a -> a
runDecorate e = runIdentity $ runCore e emptyState
