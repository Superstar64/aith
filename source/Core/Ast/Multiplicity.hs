module Core.Ast.Multiplicity where

import Core.Ast.Common
import Misc.Isomorph
import Misc.Prism
import qualified TypeSystem.Linear as TypeSystem
import qualified TypeSystem.Unrestricted as TypeSystem

data MultiplicityF = Linear | Unrestricted deriving (Show)

linear :: Prism () MultiplicityF
linear = Prism (const Linear) $ \case
  Linear -> Just ()
  _ -> Nothing

unrestricted = Prism (const Unrestricted) $ \case
  Unrestricted -> Just ()
  _ -> Nothing

data Multiplicity p = CoreMultiplicity p MultiplicityF deriving (Show, Functor, Foldable, Traversable)

coreMultiplicity :: Isomorph (p, MultiplicityF) (Multiplicity p)
coreMultiplicity = Isomorph (uncurry CoreMultiplicity) $ \(CoreMultiplicity p l) -> (p, l)

type MultiplicityInternal = Multiplicity Internal

instance TypeSystem.EmbedLinear MultiplicityInternal where
  linear = CoreMultiplicity Internal Linear

instance TypeSystem.EmbedUnrestricted MultiplicityInternal where
  unrestricted = CoreMultiplicity Internal Unrestricted
