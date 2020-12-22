module TypeSystem.Linear where

import qualified Data.Set as Set
import TypeSystem.Linearity
import TypeSystem.Methods

data Linear = Linear

class EmbedLinear l where
  linear :: l

instance (Monad m, EmbedLinearity ls) => TypeCheckImpl m p Linear ls where
  typeCheckImpl _ Linear = pure $ linearity

instance FreeVariables Linear l where
  freeVariables' Linear = Set.empty

instance EmbedLinear l => SubstituteImpl Linear u l where
  substituteImpl _ _ Linear = linear
