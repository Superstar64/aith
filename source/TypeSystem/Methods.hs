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

class Bindings pm where
  bindings :: pm -> Set Identifier

class ModifyVariables u pm where
  modifyVariables :: pm -> Set Identifier -> Set Identifier

class Substitute u e where
  substitute :: u -> Identifier -> e -> e

class AvoidCapture u pm e where
  avoidCapture :: u -> (pm, e) -> (pm, e)

class Substitute e e => SubstituteSame e

substituteSame :: SubstituteSame e => e -> Identifier -> e -> e
substituteSame = substitute

class ConvertPattern pm pm' where
  convertPattern :: Identifier -> Identifier -> pm' -> pm

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

class AugmentLinear m pm l lΓ where
  augmentLinear :: pm -> l -> m (a, lΓ) -> m (a, lΓ)

class ReadEnvironment m p κ where
  readEnvironment :: p -> Identifier -> m κ

class Augment m pm where
  augment :: pm -> m a -> m a

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

instance (Bindings a, Bindings b) => Bindings (Either a b) where
  bindings (Left pm) = bindings pm
  bindings (Right pm) = bindings pm

class SubstituteImpl e' u e where
  substituteImpl :: u -> Identifier -> e' -> e

instance (SubstituteImpl a u e, SubstituteImpl b u e) => SubstituteImpl (Either a b) u e where
  substituteImpl ux x (Left e) = substituteImpl ux x e
  substituteImpl ux x (Right e) = substituteImpl ux x e

instance (ConvertPattern pm a, ConvertPattern pm b) => ConvertPattern pm (Either a b) where
  convertPattern ix x (Left pm) = convertPattern ix x pm
  convertPattern ix x (Right pm) = convertPattern ix x pm

class ReduceImpl e' e where
  reduceImpl :: e' -> e

instance (ReduceImpl a e, ReduceImpl b e) => ReduceImpl (Either a b) e where
  reduceImpl (Left e) = reduceImpl e
  reduceImpl (Right e) = reduceImpl e

instance (ReducePattern a e, ReducePattern b e) => ReducePattern (Either a b) e where
  reducePattern (Left pm) = reducePattern pm
  reducePattern (Right pm) = reducePattern pm

class AugmentImpl m p pm where
  augmentImpl :: p -> pm -> m a -> m a

instance
  ( AugmentImpl m p a,
    AugmentImpl m p b
  ) =>
  AugmentImpl m p (Either a b)
  where
  augmentImpl p (Left pm) = augmentImpl p pm
  augmentImpl p (Right pm) = augmentImpl p pm

class AugmentLinearImpl m p pm l lΓ where
  augmentLinearImpl :: p -> pm -> l -> m (a, lΓ) -> m (a, lΓ)

instance
  ( AugmentLinearImpl m p a l lΓ,
    AugmentLinearImpl m p b l lΓ
  ) =>
  AugmentLinearImpl m p (Either a b) l lΓ
  where
  augmentLinearImpl p (Left pm) = augmentLinearImpl p pm
  augmentLinearImpl p (Right pm) = augmentLinearImpl p pm
