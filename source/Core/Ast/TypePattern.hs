module Core.Ast.TypePattern where

import Core.Ast.Common
import Core.Ast.Kind
import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import qualified Misc.Variables as Variables

data TypePatternF p' p = TypePatternVariable Identifier (Kind p') deriving (Functor, Show)

typePatternVariable = Isomorph (uncurry TypePatternVariable) $ \(TypePatternVariable x κ) -> (x, κ)

instance Bifunctor TypePatternF where
  bimap f _ (TypePatternVariable x κ) = TypePatternVariable x (fmap f κ)

data TypePattern p' p = CoreTypePattern p (TypePatternF p' p) deriving (Functor, Show)

coreTypePattern = Isomorph (uncurry CoreTypePattern) $ \(CoreTypePattern p pm) -> (p, pm)

type TypePatternInternal = TypePattern Internal Internal

instance Bifunctor TypePattern where
  bimap f g (CoreTypePattern p pm) = CoreTypePattern (g p) (bimap f g pm)

instance Semigroup p => Binder p (TypePattern p p) where
  bindings (CoreTypePattern p (TypePatternVariable x _)) = Variables.singleton x p
  rename ux x (CoreTypePattern p (TypePatternVariable x' κ)) | x == x' = (CoreTypePattern p (TypePatternVariable ux κ))
  rename _ _ pm = pm

instance Algebra u p (Kind p) => Algebra u p (TypePattern p p) where
  freeVariables (CoreTypePattern _ (TypePatternVariable _ κ)) = freeVariables @u κ
  substitute ux x (CoreTypePattern p (TypePatternVariable x' κ)) = CoreTypePattern p $ (TypePatternVariable x' (substitute ux x κ))
  convert ix x (CoreTypePattern p (TypePatternVariable x' κ)) = CoreTypePattern p $ (TypePatternVariable x' (convert @u ix x κ))

instance Algebra (Kind p) p u => Algebra (Kind p) p (Bound (TypePattern p p) u) where
  freeVariables (Bound pm σ) = freeVariables @(Kind p) pm <> freeVariables @(Kind p) σ
  substitute = substituteHigher substitute substitute
  convert = substituteHigher (convert @(Kind p)) (convert @(Kind p))

instance Reduce (TypePattern p p) where
  reduce (CoreTypePattern p (TypePatternVariable x κ)) = CoreTypePattern p $ (TypePatternVariable x (reduce κ))
