module Core.Ast.Pattern where

import Core.Ast.Common
import Core.Ast.Type
import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import Misc.Prism
import Misc.Variables (Variables)
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

instance Bindings p (Pattern p p) where
  bindings (CorePattern p (PatternVariable x _)) = Variables.singleton x p
  bindings (CorePattern _ (PatternOfCourse pm)) = bindings pm

instance Rename PatternInternal where
  rename ux x (CorePattern p (PatternVariable x' κ)) | x == x' = CorePattern p (PatternVariable ux κ)
  rename _ _ (CorePattern p (PatternVariable x κ)) = CorePattern p (PatternVariable x κ)
  rename ux x (CorePattern p (PatternOfCourse pm)) = CorePattern p (PatternOfCourse $ rename ux x pm)

freeVariablesPatternImpl :: forall u p. (Semigroup p, FreeVariables u p (Type p)) => PatternF p p -> Variables p
freeVariablesPatternImpl (PatternVariable _ σ) = freeVariables @u σ
freeVariablesPatternImpl (PatternOfCourse pm) = freeVariables @u pm

instance (Semigroup p, FreeVariables u p (Type p)) => FreeVariables u p (Pattern p p) where
  freeVariables (CorePattern _ pm) = freeVariablesPatternImpl @u pm

substitutePatternImpl ux x (PatternVariable x' σ) = PatternVariable x' (substitute ux x σ)
substitutePatternImpl ux x (PatternOfCourse pm) = PatternOfCourse (substitute ux x pm)

instance Substitute u TypeInternal => Substitute u PatternInternal where
  substitute ux x (CorePattern Internal pm) = CorePattern Internal (substitutePatternImpl ux x pm)

instance Reduce PatternInternal where
  reduce (CorePattern Internal (PatternVariable x κ)) = CorePattern Internal $ (PatternVariable x (reduce κ))
  reduce (CorePattern Internal (PatternOfCourse pm)) = CorePattern Internal (PatternOfCourse (reduce pm))
