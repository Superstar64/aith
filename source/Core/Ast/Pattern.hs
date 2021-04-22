module Core.Ast.Pattern where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Type
import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import Misc.Prism
import qualified Misc.Variables as Variables

data PatternF p' p
  = PatternVariable Identifier (Type p')
  | PatternOfCourse (Pattern p' p)
  deriving (Show)

patternVariable = Prism (uncurry PatternVariable) $ \case
  (PatternVariable x σ) -> Just (x, σ)
  _ -> Nothing

patternOfCourse = Prism PatternOfCourse $ \case
  (PatternOfCourse pm) -> Just pm
  _ -> Nothing

instance Bifunctor PatternF where
  bimap f _ (PatternVariable x σ) = PatternVariable x (fmap f σ)
  bimap f g (PatternOfCourse pm) = PatternOfCourse (bimap f g pm)

data Pattern p' p = CorePattern p (PatternF p' p) deriving (Show)

corePattern = Isomorph (uncurry CorePattern) $ \(CorePattern p pm) -> (p, pm)

instance Bifunctor Pattern where
  bimap f g (CorePattern p pm) = CorePattern (g p) (bimap f g pm)

type PatternInternal = Pattern Internal Internal

instance Semigroup p => Binder p (Pattern p p) where
  bindings (CorePattern p (PatternVariable x _)) = Variables.singleton x p
  bindings (CorePattern _ (PatternOfCourse pm)) = bindings pm
  rename ux x (CorePattern p (PatternVariable x' σ)) | x == x' = CorePattern p (PatternVariable ux σ)
  rename _ _ x@(CorePattern _ (PatternVariable _ _)) = x
  rename ux x (CorePattern p (PatternOfCourse pm)) = CorePattern p (PatternOfCourse $ rename ux x pm)

instance Algebra u p (Type p) => Algebra u p (Pattern p p) where
  freeVariables (CorePattern _ (PatternVariable _ σ)) = freeVariables @u σ
  freeVariables (CorePattern _ (PatternOfCourse pm)) = freeVariables @u pm
  convert ix x (CorePattern p (PatternVariable x' σ)) = CorePattern p $ PatternVariable x' (convert @u ix x σ)
  convert ix x (CorePattern p (PatternOfCourse pm)) = CorePattern p $ PatternOfCourse $ convert @u ix x pm
  substitute ux x (CorePattern p (PatternVariable x' σ)) = CorePattern p $ PatternVariable x' (substitute ux x σ)
  substitute ux x (CorePattern p (PatternOfCourse pm)) = CorePattern p $ PatternOfCourse $ substitute ux x pm

instance Algebra (Type p) p u => Algebra (Type p) p (Bound (Pattern p p) u) where
  freeVariables (Bound pm e) = freeVariables @(Type p) pm <> freeVariables @(Type p) e
  substitute ux x (Bound pm σ) = Bound (substitute ux x pm) (substitute ux x σ)
  convert = substituteHigher (convert @(Type p)) (convert @(Type p))

instance Algebra (Kind p) p u => Algebra (Kind p) p (Bound (Pattern p p) u) where
  freeVariables (Bound pm e) = freeVariables @(Kind p) pm <> freeVariables @(Kind p) e
  substitute ux x (Bound pm σ) = Bound (substitute ux x pm) (substitute ux x σ)
  convert = substituteHigher (convert @(Kind p)) (convert @(Kind p))

instance Algebra (Type p) p (e p) => AlgebraBound (Type p) p e (Pattern p p)

instance Algebra (Kind p) p (e p) => AlgebraBound (Kind p) p e (Pattern p p)

instance Semigroup p => Reduce (Pattern p p) where
  reduce (CorePattern p (PatternVariable x σ)) = CorePattern p $ (PatternVariable x (reduce σ))
  reduce (CorePattern p (PatternOfCourse pm)) = CorePattern p (PatternOfCourse (reduce pm))
