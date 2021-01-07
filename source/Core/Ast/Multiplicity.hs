module Core.Ast.Multiplicity where

import Core.Ast.Common
import Data.Type.Equality ((:~:) (..))
import Misc.Util (Same, same)
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

instance (i ~ Internal) => TypeSystem.EmbedLinear (Multiplicity i) where
  linear = CoreMultiplicity Internal Linear

instance (i ~ Internal) => TypeSystem.EmbedUnrestricted (Multiplicity i) where
  unrestricted = CoreMultiplicity Internal Unrestricted

data MultiplicitySort = Multiplicity deriving (Show)

instance TypeSystem.EmbedMultiplicity MultiplicitySort where
  multiplicity = Multiplicity

instance (i ~ Internal, i' ~ Internal) => Same (Multiplicity i) (Multiplicity i') where
  same = Just Refl

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Multiplicity i) (Multiplicity i') where
  freeVariables' (CoreMultiplicity Internal l) = freeVariables @MultiplicityInternal $ projectMultiplicity l

instance (i ~ Internal, i' ~ Internal) => Substitute (Multiplicity i) (Multiplicity i') where
  substitute lx x (CoreMultiplicity Internal l) = substituteImpl lx x $ projectMultiplicity l

instance (i ~ Internal) => SubstituteSame (Multiplicity i)
