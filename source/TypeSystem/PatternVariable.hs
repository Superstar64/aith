module TypeSystem.PatternVariable where

import qualified Data.Set as Set
import Misc.Identifier (Identifier)
import TypeSystem.Methods
import TypeSystem.Pattern
import TypeSystem.Type

data PatternVariable s κ σ = PatternVariable Identifier σ

class EmbedPatternVariable σ pm where
  patternVariable :: Identifier -> σ -> pm

class AugmentVariableLinear m p l σ lΓ where
  augmentVariableLinear :: p -> Identifier -> l -> σ -> m (a, lΓ) -> m (a, lΓ)

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

instance InternalType (PatternVariable s κ σ) σ where
  internalType (PatternVariable _ σ) = σ

instance
  ( Monad m,
    AugmentVariableLinear m p l σ lΓ
  ) =>
  AugmentLinearImpl m p (PatternVariable s κ σ) l lΓ
  where
  augmentLinearImpl p (PatternVariable x σ) l e = do
    augmentVariableLinear p x l σ e

instance (FreeVariables u p σ) => FreeVariablesImpl u p (PatternVariable s κ σ) where
  freeVariablesImpl _ (PatternVariable _ σ) = freeVariables @u σ

instance Bindings (PatternVariable s κ σ) where
  bindings (PatternVariable x _) = Set.singleton x

instance (EmbedPatternVariable σ pm, Substitute u σ) => SubstituteImpl (PatternVariable s κ σ) u pm where
  substituteImpl ux x (PatternVariable x' σ) = patternVariable x' (substitute ux x σ)

instance EmbedPatternVariable σ pm => ConvertPattern pm (PatternVariable s κ σ) where
  convertPattern ix x (PatternVariable x' σ) | x == x' = patternVariable ix σ
  convertPattern _ _ (PatternVariable x σ) = patternVariable x σ

instance (EmbedPatternVariable σ pm, Reduce σ) => ReduceImpl (PatternVariable s κ σ) pm where
  reduceImpl (PatternVariable x σ) = patternVariable x (reduce σ)

instance (Substitute σ e, Reduce e) => ReducePattern (PatternVariable s κ σ') σ e where
  reducePattern (PatternVariable x _) σ e = reduce $ substitute σ x e
