module Core.Ast.FunctionLiteral where

import Core.Ast.Common
import Core.Ast.Pattern
import Core.Ast.Term
import Core.Ast.Type
import Core.Ast.TypePattern
import Data.Bifunctor (bimap)
import Misc.Isomorph
import qualified Misc.Variables as Variables

data FunctionLiteral p = FunctionLiteral p [TypePattern p p] (Type p) [Pattern p p] (Term p) deriving (Show)

functionLiteral :: Isomorph ((((p, [TypePattern p p]), Type p), [Pattern p p]), Term p) (FunctionLiteral p)
functionLiteral = Isomorph (uncurry $ uncurry $ uncurry $ uncurry FunctionLiteral) $ \(FunctionLiteral p pmσs σ pms e) -> ((((p, pmσs), σ), pms), e)

instance Functor FunctionLiteral where
  fmap f (FunctionLiteral p pmσs σ pms e) = FunctionLiteral (f p) (fmap (bimap f f) pmσs) (fmap f σ) (fmap (bimap f f) pms) (fmap f e)

type FunctionLiteralInternal = FunctionLiteral Internal

consPattern pm (FunctionLiteral p pmσs σ pms e) = FunctionLiteral p pmσs σ (pm : pms) e

consTypePattern pm (FunctionLiteral p pmσs σ pms e) = FunctionLiteral p (pm : pmσs) σ pms e

instance Semigroup p => FreeVariables (Term p) p (FunctionLiteral p) where
  freeVariables (FunctionLiteral _ _ _ [] e) = freeVariables @(Term p) e
  freeVariables (FunctionLiteral p pmσs σ (pm : pms) e) = removeBinds (freeVariables @(Term p) (FunctionLiteral p pmσs σ pms e)) (bindings @p pm)

instance Substitute TermInternal FunctionLiteralInternal where
  substitute ux x (FunctionLiteral p [] σ [] e) = FunctionLiteral p [] σ [] (substitute ux x e)
  substitute _ x λ@(FunctionLiteral _ [] _ (pm : _) _) | x `Variables.member` bindingsInternal pm = λ
  substitute ux x (FunctionLiteral p [] σ (pm : pms) e) = consPattern pm' $ substitute ux x λ
    where
      Bound pm' λ = avoidCaptureTerm ux (Bound pm $ FunctionLiteral p [] σ pms e)
  substitute ux x (FunctionLiteral p (pmσ : pmσs) σ pms e) = consTypePattern pmσ' $ substitute ux x λ
    where
      Bound pmσ' λ = avoidCaptureType ux (Bound pmσ $ FunctionLiteral p pmσs σ pms e)

instance Substitute TypeInternal FunctionLiteralInternal where
  substitute ux x (FunctionLiteral p [] σ pms e) = FunctionLiteral p [] (substitute ux x σ) (substitute ux x pms) (substitute ux x e)
  substitute _ x λ@(FunctionLiteral _ (pmσ : _) _ _ _) | x `Variables.member` bindingsInternal pmσ = λ
  substitute ux x (FunctionLiteral p (pmσ : pmσs) σ pms e) = consTypePattern pmσ' (substitute ux x λ)
    where
      Bound pmσ' λ = avoidCaptureType ux (Bound pmσ $ FunctionLiteral p pmσs σ pms e)

instance Reduce FunctionLiteralInternal where
  reduce (FunctionLiteral p pmσs σ pms e) = FunctionLiteral p (reduce pmσs) (reduce σ) (reduce pms) (reduce e)
