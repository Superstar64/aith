module TypeSystem.Runtime where

import TypeSystem.Methods
import TypeSystem.Stage

data Runtime r = Runtime r

class EmbedRuntime s r where
  runtime :: r -> s

instance (Monad m, EmbedStage ss) => TypeCheckImpl m p (Runtime r) ss where
  typeCheckImpl _ (Runtime _) = pure stage

instance FreeVariables u r => FreeVariables u (Runtime r) where
  freeVariables (Runtime r) = freeVariables @u r

instance (EmbedRuntime s r, Substitute u r) => SubstituteImpl (Runtime r) u s where
  substituteImpl ux x (Runtime r) = runtime (substitute ux x r)
