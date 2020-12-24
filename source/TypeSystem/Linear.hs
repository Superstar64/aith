module TypeSystem.Linear where

import qualified Data.Set as Set
import TypeSystem.Methods
import TypeSystem.Multiplicity

data Linear = Linear

class EmbedLinear l where
  linear :: l

instance (Monad m, EmbedMultiplicity ls) => TypeCheckImpl m p Linear ls where
  typeCheckImpl _ Linear = pure $ multiplicity

instance FreeVariables Linear l where
  freeVariables' Linear = Set.empty

instance EmbedLinear l => SubstituteImpl Linear u l where
  substituteImpl _ _ Linear = linear
