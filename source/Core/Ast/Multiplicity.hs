module Core.Ast.Multiplicity where

import Core.Ast.Common
import qualified TypeSystem.Linear as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.Multiplicity as TypeSystem
import qualified TypeSystem.Unrestricted as TypeSystem

data MultiplicityF = Linear | Unrestricted deriving (Show)

data Multiplicity p = CoreMultiplicity p MultiplicityF deriving (Show, Functor, Foldable, Traversable)

type MultiplicityInternal = Multiplicity Internal

projectMultiplicity :: MultiplicityF -> (Either TypeSystem.Linear TypeSystem.Unrestricted)
projectMultiplicity Linear = Left $ TypeSystem.Linear
projectMultiplicity Unrestricted = Right $ TypeSystem.Unrestricted

instance TypeSystem.EmbedLinear MultiplicityInternal where
  linear = CoreMultiplicity Internal Linear

instance TypeSystem.EmbedUnrestricted MultiplicityInternal where
  unrestricted = CoreMultiplicity Internal Unrestricted

data MultiplicitySort = Multiplicity deriving (Show)

instance TypeSystem.EmbedMultiplicity MultiplicitySort where
  multiplicity = Multiplicity

instance FreeVariables MultiplicityInternal MultiplicityInternal where
  freeVariables' (CoreMultiplicity Internal l) = freeVariables @MultiplicityInternal $ projectMultiplicity l

instance Substitute MultiplicityInternal MultiplicityInternal where
  substitute lx x (CoreMultiplicity Internal l) = substituteImpl lx x $ projectMultiplicity l

instance SubstituteSame MultiplicityInternal
