module TypeSystem.Methods where

import Data.Set (Set)
import Misc.Identifier

class TypeCheckInstantiate κ σ m σ' where
  typeCheckInstantiate :: σ' -> m (κ, σ)

class TypeCheck σ m e where
  typeCheck :: e -> m σ

-- typeCheck = fmap fst . typeCheckInstantiate

class Instantiate σ m σ' where
  instantiate :: σ' -> m σ

-- instantiate = fmap snd . typeCheckInstantiate

class Strip pm pm' where
  strip :: pm -> pm'

class InternalType pm σ where
  internalType :: pm -> σ

class TypeCheckLinear σ m e lΓ where
  typeCheckLinear :: e -> m (σ, lΓ)

class FreeVariables e u where
  freeVariables' :: e -> Set Identifier

freeVariables :: forall u e. FreeVariables e u => e -> Set Identifier
freeVariables e = freeVariables' @e @u e

class RemoveBindings pm where
  removeBindings :: pm -> Set Identifier -> Set Identifier

class Substitute u e where
  substitute :: u -> Identifier -> e -> e

class AvoidCapturePattern u pm e where
  avoidCapturePattern :: u -> (pm, e) -> (pm, e)

class Substitute e e => SubstituteSame e where
  substituteSame :: e -> Identifier -> e -> e
  substituteSame = substitute

-- Applicative Order Reduction
-- see https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf
class Reduce e where
  reduce :: e -> e

class ReducePattern pm e where
  reducePattern :: pm -> e -> e -> e

class ReduceMatchAbstraction u e where
  reduceMatchAbstraction :: e -> Maybe (u -> e)

class SameType m p σ where
  sameType :: p -> σ -> σ -> m ()

class Capture m p l lΓ where
  capture :: p -> l -> lΓ -> m ()

class ReadEnvironmentLinear m p σ lΓ where
  readEnvironmentLinear :: p -> Identifier -> m (σ, lΓ)

class AugmentEnvironmentLinear m p l σ lΓ where
  augmentEnvironmentLinear :: p -> Identifier -> l -> σ -> m (a, lΓ) -> m (a, lΓ)

class AugmentEnvironmentPatternLinear m pm l lΓ where
  augmentEnvironmentPatternLinear :: pm -> l -> m (a, lΓ) -> m (a, lΓ)

class ReadEnvironment m p κ where
  readEnvironment :: p -> Identifier -> m κ

class AugmentEnvironment m p κ where
  augmentEnvironment :: p -> Identifier -> κ -> m a -> m a

class AugmentEnvironmentPattern m pm where
  augmentEnvironmentPattern :: pm -> m a -> m a

class Positioned e p | e -> p where
  location :: e -> p

instance Positioned (p, e) p where
  location (p, _) = p

class TypeCheckLinearImpl m p e σ lΓ where
  typeCheckLinearImpl :: p -> e -> m (σ, lΓ)

instance (TypeCheckLinearImpl m p a σ lΓ, TypeCheckLinearImpl m p b σ lΓ) => TypeCheckLinearImpl m p (Either a b) σ lΓ where
  typeCheckLinearImpl p (Left e) = typeCheckLinearImpl p e
  typeCheckLinearImpl p (Right e) = typeCheckLinearImpl p e

class TypeCheckImpl m p e σ where
  typeCheckImpl :: p -> e -> m σ

instance (TypeCheckImpl m p a σ, TypeCheckImpl m p b σ) => TypeCheckImpl m p (Either a b) σ where
  typeCheckImpl p (Left e) = typeCheckImpl p e
  typeCheckImpl p (Right e) = typeCheckImpl p e

instance (InternalType a σ, InternalType b σ) => InternalType (Either a b) σ where
  internalType (Left pm) = internalType pm
  internalType (Right pm) = internalType pm

instance (FreeVariables a u, FreeVariables b u) => FreeVariables (Either a b) u where
  freeVariables' (Left σ) = freeVariables @u σ
  freeVariables' (Right σ) = freeVariables @u σ

instance (RemoveBindings a, RemoveBindings b) => RemoveBindings (Either a b) where
  removeBindings (Left pm) = removeBindings pm
  removeBindings (Right pm) = removeBindings pm

class SubstituteImpl e' u e where
  substituteImpl :: u -> Identifier -> e' -> e

instance (SubstituteImpl a u e, SubstituteImpl b u e) => SubstituteImpl (Either a b) u e where
  substituteImpl ux x (Left e) = substituteImpl ux x e
  substituteImpl ux x (Right e) = substituteImpl ux x e

class AvoidCapturePatternImpl pm' u pm e where
  avoidCapturePatternImpl :: u -> (pm', e) -> (pm, e)

instance
  ( AvoidCapturePatternImpl a u pm e,
    AvoidCapturePatternImpl b u pm e
  ) =>
  AvoidCapturePatternImpl (Either a b) u pm e
  where
  avoidCapturePatternImpl u (Left pm, e) = avoidCapturePatternImpl u (pm, e)
  avoidCapturePatternImpl u (Right pm, e) = avoidCapturePatternImpl u (pm, e)

class ReduceImpl e' e where
  reduceImpl :: e' -> e

instance (ReduceImpl a e, ReduceImpl b e) => ReduceImpl (Either a b) e where
  reduceImpl (Left e) = reduceImpl e
  reduceImpl (Right e) = reduceImpl e

instance (ReducePattern a e, ReducePattern b e) => ReducePattern (Either a b) e where
  reducePattern (Left pm) = reducePattern pm
  reducePattern (Right pm) = reducePattern pm

class AugmentEnvironmentPatternImpl m p pm where
  augmentEnvironmentPatternImpl :: p -> pm -> m a -> m a

instance
  ( AugmentEnvironmentPatternImpl m p a,
    AugmentEnvironmentPatternImpl m p b
  ) =>
  AugmentEnvironmentPatternImpl m p (Either a b)
  where
  augmentEnvironmentPatternImpl p (Left pm) = augmentEnvironmentPatternImpl p pm
  augmentEnvironmentPatternImpl p (Right pm) = augmentEnvironmentPatternImpl p pm

class AugmentEnvironmentPatternLinearImpl m p pm l lΓ where
  augmentEnvironmentPatternLinearImpl :: p -> pm -> l -> m (a, lΓ) -> m (a, lΓ)

instance
  ( AugmentEnvironmentPatternLinearImpl m p a l lΓ,
    AugmentEnvironmentPatternLinearImpl m p b l lΓ
  ) =>
  AugmentEnvironmentPatternLinearImpl m p (Either a b) l lΓ
  where
  augmentEnvironmentPatternLinearImpl p (Left pm) = augmentEnvironmentPatternLinearImpl p pm
  augmentEnvironmentPatternLinearImpl p (Right pm) = augmentEnvironmentPatternLinearImpl p pm
