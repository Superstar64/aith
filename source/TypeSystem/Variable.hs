module TypeSystem.Variable where

import qualified Data.Set as Set
import Data.Type.Equality ((:~:) (..))
import Misc.Identifier
import Misc.Util (Same, same)
import TypeSystem.Methods

avoidCapture :: forall σ e u. (EmbedVariable σ, FreeVariables u σ, Substitute σ e) => u -> (Identifier, e) -> (Identifier, e)
avoidCapture = avoidCaptureImpl @σ substitute

avoidCaptureImpl :: forall σ e u. (EmbedVariable σ, FreeVariables u σ) => (σ -> Identifier -> e -> e) -> u -> (Identifier, e) -> (Identifier, e)
avoidCaptureImpl substitute ux (x, e) = (x', e')
  where
    x' = fresh (freeVariables @σ ux) x
    e' = case x == x' of
      True -> e
      False -> substitute (variable @σ x') x e

data Variable e = Variable Identifier deriving (Show)

class EmbedVariable e where
  variable :: Identifier -> e

instance ReadEnvironmentLinear m p σ lΓ => TypeCheckLinearImpl m p (Variable e) σ lΓ where
  typeCheckLinearImpl p (Variable x) = readEnvironmentLinear p x

instance ReadEnvironment m p κ => TypeCheckImpl m p (Variable e) κ where
  typeCheckImpl p (Variable x) = readEnvironment p x

instance (Same u e) => FreeVariables (Variable e) u where
  freeVariables' (Variable x) = case same @u @e of
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
