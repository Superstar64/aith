module TypeSystem.Unrestricted where

import qualified Data.Set as Set
import TypeSystem.Multiplicity
import TypeSystem.Methods

data Unrestricted = Unrestricted

class EmbedUnrestricted l where
  unrestricted :: l

instance (Monad m, EmbedMultiplicity ls) => TypeCheckImpl m p Unrestricted ls where
  typeCheckImpl _ Unrestricted = pure $ multiplicity

instance FreeVariables Unrestricted l where
  freeVariables' Unrestricted = Set.empty

instance EmbedUnrestricted l => SubstituteImpl Unrestricted u l where
  substituteImpl _ _ Unrestricted = unrestricted
