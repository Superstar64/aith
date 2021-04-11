module Core.Ast.Multiplicity where

import Core.Ast.Common
import Misc.Isomorph
import Misc.Prism

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
