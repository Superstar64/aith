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

newtype Decorate f = Decorate (f C.Representation)

decoration (CoreKind _ (Type (CoreKind _ (Runtime (CoreKind _ PointerRep))))) = C.Pointer
decoration _ = error "unable to decorate kind"

augmentVariable p x σ e = do
  env <- Core get
  let σΓ = typeEnvironment env
  Core $ put env {typeEnvironment = Map.insert x (p, Unrestricted, σ) σΓ}
  e' <- e
  Core $ put env
  pure e'

augmentPattern (CoreRuntimePattern Silent p (RuntimePatternVariable x σ)) e = augmentVariable p x σ e

decoratePattern (CoreRuntimePattern Silent p (RuntimePatternVariable x σ)) = do
  dσ <- decoration <$> typeCheck σ
  pure $ CoreRuntimePattern (Decorate (Identity dσ)) p (RuntimePatternVariable x σ)

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
decorateTerm (CoreTerm p (FunctionLiteral _ τ (Bound pms e))) = do
  dτ <- Identity <$> decoration <$> (typeCheck τ)
  dpms <- traverse decoratePattern pms
  e' <- foldr augmentPattern (decorateTerm e) pms
  pure $ CoreTerm p $ FunctionLiteral (Decorate dτ) τ (Bound dpms e')
decorateTerm (CoreTerm _ (ErasedQualifiedAssume _ _ e)) = decorateTerm e
decorateTerm (CoreTerm _ (ErasedQualifiedCheck _ e)) = decorateTerm e
decorateTerm _ = error "unable to decorate term"

runDecorate :: Core.TypeCheck.Core Internal Identity a -> a
runDecorate e = runIdentity $ runCore e emptyState
