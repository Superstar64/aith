module Core.Ast.Multiplicity where

import Core.Ast.Common
import qualified TypeSystem.Linear as TypeSystem
import qualified TypeSystem.Unrestricted as TypeSystem

data MultiplicityF = Linear | Unrestricted deriving (Show)

data Multiplicity p = CoreMultiplicity p MultiplicityF deriving (Show, Functor, Foldable, Traversable)

type MultiplicityInternal = Multiplicity Internal

instance TypeSystem.EmbedLinear MultiplicityInternal where
  linear = CoreMultiplicity Internal Linear

instance TypeSystem.EmbedUnrestricted MultiplicityInternal where
  unrestricted = CoreMultiplicity Internal Unrestricted
