module TypeSystem.PatternVariable where

import qualified Data.Set as Set
import Misc.Identifier
import TypeSystem.Methods
import TypeSystem.Pattern
import TypeSystem.Type
import TypeSystem.Variable

data PatternVariable s κ σ = PatternVariable Identifier σ

class EmbedPatternVariable σ pm where
  patternVariable :: Identifier -> σ -> pm

instance
  ( Monad m,
    Positioned σ p,
    EmbedPattern pms,
    CheckType s κ m p,
    TypeCheck κ m σ
  ) =>
  TypeCheckImpl m p (PatternVariable s κ σ) pms
  where
  typeCheckImpl _ (PatternVariable _ σ) = do
    Type _ <- checkType @s (location σ) =<< typeCheck @κ σ
    pure pattern

instance (σ ~ σ') => InternalType (PatternVariable s κ σ') σ where
  internalType (PatternVariable _ σ) = σ

instance
  ( Monad m,
    AugmentEnvironmentLinear m p l σ lΓ
  ) =>
  AugmentEnvironmentPatternLinearImpl m p (PatternVariable s κ σ) l lΓ
  where
  augmentEnvironmentPatternLinearImpl p (PatternVariable x σ) l e = do
    augmentEnvironmentLinear p x l σ e

instance (FreeVariables σ u) => FreeVariables (PatternVariable s κ σ) u where
  freeVariables' (PatternVariable _ σ) = freeVariables @u σ

instance (EmbedPatternVariable σ pm, Substitute u σ) => SubstituteImpl (PatternVariable s κ σ) u pm where
  substituteImpl ux x (PatternVariable x' σ) = patternVariable x' (substitute ux x σ)

instance RemoveBindings (PatternVariable s κ σ) where
  removeBindings (PatternVariable x _) = Set.delete x

instance
  ( EmbedPatternVariable σ pm,
    EmbedVariable e,
    FreeVariables u e,
    SubstituteSame e
  ) =>
  AvoidCapturePatternImpl (PatternVariable s κ σ) u pm e
  where
  avoidCapturePatternImpl u (PatternVariable x σ, e) = (patternVariable x' σ, e')
    where
      (x', e') = avoidCaptureImpl substituteSame u (x, e)

instance (EmbedPatternVariable σ pm, Reduce σ) => ReduceImpl (PatternVariable s κ σ) pm where
  reduceImpl (PatternVariable x σ) = patternVariable x (reduce σ)

instance (SubstituteSame e, Reduce e) => ReducePattern (PatternVariable s κ σ) e where
  reducePattern (PatternVariable x _) e1 e2 = reduce $ substituteSame e1 x e2
