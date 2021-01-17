module TypeSystem.Variable where

import Misc.Identifier
import TypeSystem.Methods

data Variable e = Variable Identifier deriving (Show)

class EmbedVariable e where
  variable :: Identifier -> e

instance ReadEnvironmentLinear m p σ lΓ => TypeCheckLinearImpl m p (Variable e) σ lΓ where
  typeCheckLinearImpl p (Variable x) = readEnvironmentLinear p x

instance ReadEnvironment m p κ => TypeCheckImpl m p (Variable e) κ where
  typeCheckImpl p (Variable x) = readEnvironment p x

instance EmbedVariable e => ReduceImpl (Variable e') e where
  reduceImpl (Variable x) = variable x
