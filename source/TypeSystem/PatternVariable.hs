module TypeSystem.PatternVariable where

import qualified Data.Set as Set
import Misc.Identifier
import TypeSystem.Methods
import TypeSystem.Variable

data PatternVariable κ σ = PatternVariable Identifier σ

class EmbedPatternVariable σ pm where
  patternVariable :: Identifier -> σ -> pm

instance (Monad m, TypeCheckInstantiate κ σ m σ') => TypeCheckImpl m p (PatternVariable κ σ') σ where
  typeCheckImpl _ (PatternVariable _ σ) = instantiate @κ σ

instance
  ( σ ~ σ',
    Monad m,
    AugmentEnvironmentLinear m p l σ lΓ
  ) =>
  AugmentEnvironmentPatternImpl m p (PatternVariable κ σ') l σ lΓ
  where
  augmentEnvironmentPatternImpl p (PatternVariable x σ) l _ e = do
    augmentEnvironmentLinear p x l σ e

instance (FreeVariables σ u) => FreeVariables (PatternVariable κ σ) u where
  freeVariables' (PatternVariable _ σ) = freeVariables @u σ

instance (EmbedPatternVariable σ pm, Substitute u σ) => SubstituteImpl (PatternVariable κ σ) u pm where
  substituteImpl ux x (PatternVariable x' σ) = patternVariable x' (substitute ux x σ)

instance RemoveBindings (PatternVariable κ σ) where
  removeBindings (PatternVariable x _) = Set.delete x

instance
  ( EmbedPatternVariable σ pm,
    EmbedVariable e,
    FreeVariables u e,
    SubstituteSame e
  ) =>
  AvoidCapturePatternImpl (PatternVariable κ σ) u pm e
  where
  avoidCapturePatternImpl u (PatternVariable x σ, e) = (patternVariable x' σ, e')
    where
      (x', e') = avoidCaptureImpl substituteSame u (x, e)

instance (SubstituteSame e, Reduce e) => ReducePattern (PatternVariable κ σ) e where
  reducePattern (PatternVariable x _) e1 e2 = reduce $ substituteSame e1 x e2
