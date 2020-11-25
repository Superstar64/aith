module TypeSystem.Variable where

import Data.Proxy (Proxy (..), asProxyTypeOf)
import Data.Set as Set
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same, same')
import TypeSystem.Methods

avoidCapture :: (Substitute u b, EmbedVariable u) => Proxy u -> Set Identifier -> (Identifier, b) -> (Identifier, b)
avoidCapture p disallow (x, σ) = (x', σ')
  where
    x' = fresh disallow x
    σ' = case x == x' of
      True -> σ
      False -> substitute (asProxyTypeOf (variable x') p) x σ

data Variable e = Variable Identifier deriving (Show)

class EmbedVariable e where
  variable' :: Variable e' -> e

variable x = variable' (Variable x)

instance ReadEnvironmentLinear m p σ lΓ => TypeCheckLinearImpl m p (Variable e) σ lΓ where
  typeCheckLinearImpl p (Variable x) = readEnvironmentLinear p x

instance ReadEnvironment m p κ => TypeCheckImpl m p (Variable e) κ where
  typeCheckImpl p (Variable x) = readEnvironment p x

phony :: Variable e -> Proxy e
phony _ = Proxy

instance (Same u e) => FreeVariables (Variable e) u where
  freeVariables u f@(Variable x) = case same' u (phony f) of
    Just Refl -> Set.singleton x
    Nothing -> Set.empty

instance (EmbedVariable e, Same u e) => SubstituteImpl (Variable e') u e where
  substituteImpl ux x (Variable x') | x == x' = pick ux (variable x) same
    where
      pick :: u -> e -> Maybe (u :~: e) -> e
      pick ex _ (Just Refl) = ex
      pick _ e Nothing = e
  substituteImpl _ _ (Variable x) = variable x

instance EmbedVariable e => ReduceImpl (Variable e') e where
  reduceImpl (Variable x) = variable x
