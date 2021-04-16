module Core.Ast.FunctionLiteral where

import Core.Ast.Common
import Core.Ast.Pattern
import Core.Ast.Term
import Core.Ast.Type
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import Data.Functor.Identity (Identity)
import Misc.Isomorph
import qualified Misc.Variables as Variables

data FunctionLiteral d p = FunctionLiteral (d Identity) (d []) p [TypePattern p p] (Type p) [Pattern p p] (Term d p)

deriving instance (Show p, Show (d Identity), Show (d []), Show (d Erased)) => Show (FunctionLiteral d p)

functionLiteral = Isomorph (uncurry $ uncurry $ uncurry $ uncurry $ FunctionLiteral Silent Silent) unpack
  where
    unpack (FunctionLiteral _ _ p pmσs σ pms e) = ((((p, pmσs), σ), pms), e)

instance Functor (FunctionLiteral d) where
  fmap f (FunctionLiteral dσ dpms p pmσs σ pms e) = FunctionLiteral dσ dpms (f p) (fmap (bimap f f) pmσs) (fmap f σ) (fmap (bimap f f) pms) (fmap f e)

consPattern pm (FunctionLiteral dσ dpms p pmσs σ pms e) = FunctionLiteral dσ dpms p pmσs σ (pm : pms) e

consTypePattern pm (FunctionLiteral dσ dpms p pmσs σ pms e) = FunctionLiteral dσ dpms p (pm : pmσs) σ pms e

instance Semigroup p => Algebra (Term d p) p (FunctionLiteral d p) where
  freeVariables (FunctionLiteral _ _ _ _ _ [] e) = freeVariables @(Term d p) e
  freeVariables (FunctionLiteral dσ dpms p pmσs σ (pm : pms) e) = removeBinds (freeVariables @(Term d p) (FunctionLiteral dσ dpms p pmσs σ pms e)) (bindings pm)
  substitute ux x (FunctionLiteral dσ dpms p [] σ [] e) = FunctionLiteral dσ dpms p [] σ [] (substitute ux x e)
  substitute _ x λ@(FunctionLiteral _ _ _ [] _ (pm : _) _) | x `Variables.member` bindings pm = λ
  substitute ux x (FunctionLiteral dσ dpms p [] σ (pm : pms) e) = consPattern pm' $ substitute ux x λ
    where
      Bound pm' λ = avoidCaptureTerm @d ux (Bound pm $ FunctionLiteral dσ dpms p [] σ pms e)
  substitute ux x (FunctionLiteral dσ dpms p (pmσ : pmσs) σ pms e) = consTypePattern pmσ' $ substitute ux x λ
    where
      Bound pmσ' λ = avoidCaptureType ux (Bound pmσ $ FunctionLiteral dσ dpms p pmσs σ pms e)
  convert ix x (FunctionLiteral dσ dpms p [] σ [] e) = FunctionLiteral dσ dpms p [] σ [] (convert @(Term d p) ix x e)
  convert _ x λ@(FunctionLiteral _ _ _ [] _ (pm : _) _) | x `Variables.member` bindings pm = λ
  convert ix x (FunctionLiteral dσ dpms p [] σ (pm : pms) e) = consPattern pm' $ convert @(Term d p) ix x λ
    where
      Bound pm' λ = avoidCaptureTermConvert @d ix (Bound pm $ FunctionLiteral dσ dpms p [] σ pms e)
  convert ix x (FunctionLiteral dσ dpms p (pmσ : pmσs) σ pms e) = consTypePattern pmσ $ convert @(Term d p) ix x $ FunctionLiteral dσ dpms p pmσs σ pms e

instance Semigroup p => Algebra (Type p) p (FunctionLiteral d p) where
  freeVariables (FunctionLiteral _ _ _ [] σ pms e) = freeVariables @(Type p) σ <> foldMap (freeVariables @(Type p)) pms <> freeVariables @(Type p) e
  freeVariables (FunctionLiteral dσ dpms p (pmσ : pmσs) σ pms e) = removeBinds (freeVariables @(Type p) (FunctionLiteral dσ dpms p pmσs σ pms e)) (bindings pmσ)
  substitute ux x (FunctionLiteral dσ dpms p [] σ pms e) = FunctionLiteral dσ dpms p [] (substitute ux x σ) (substitute ux x <$> pms) (substitute ux x e)
  substitute _ x λ@(FunctionLiteral _ _ _ (pmσ : _) _ _ _) | x `Variables.member` bindings pmσ = λ
  substitute ux x (FunctionLiteral dσ dpms p (pmσ : pmσs) σ pms e) = consTypePattern pmσ' (substitute ux x λ)
    where
      Bound pmσ' λ = avoidCaptureType ux (Bound pmσ $ FunctionLiteral dσ dpms p pmσs σ pms e)

  convert ix x (FunctionLiteral dσ dpms p [] σ pms e) = FunctionLiteral dσ dpms p [] (convert @(Type p) ix x σ) (convert @(Type p) ix x <$> pms) (convert @(Type p) ix x e)
  convert _ x λ@(FunctionLiteral _ _ _ (pmσ : _) _ _ _) | x `Variables.member` bindings pmσ = λ
  convert ix x (FunctionLiteral dσ dpms p (pmσ : pmσs) σ pms e) = consTypePattern pmσ' (convert @(Type p) ix x λ)
    where
      Bound pmσ' λ = avoidCaptureTypeConvert ix (Bound pmσ $ FunctionLiteral dσ dpms p pmσs σ pms e)

instance Semigroup p => Reduce (FunctionLiteral Silent p) where
  reduce (FunctionLiteral dσ dpms p pmσs σ pms e) = FunctionLiteral dσ dpms p (reduce pmσs) (reduce σ) (reduce pms) (reduce e)
