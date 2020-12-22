module TypeSystem.Unrestricted where

import qualified Data.Set as Set
import TypeSystem.Linearity
import TypeSystem.Methods

data Unrestricted = Unrestricted

class EmbedUnrestricted l where
  unrestricted :: l

instance (Monad m, EmbedLinearity ls) => TypeCheckImpl m p Unrestricted ls where
  typeCheckImpl _ Unrestricted = pure $ linearity

instance FreeVariables Unrestricted l where
  freeVariables' Unrestricted = Set.empty

instance EmbedUnrestricted l => SubstituteImpl Unrestricted u l where
  substituteImpl _ _ Unrestricted = unrestricted
