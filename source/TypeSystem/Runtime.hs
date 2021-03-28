module TypeSystem.Runtime where

import TypeSystem.Methods
import TypeSystem.Representation
import TypeSystem.Stage

data Runtime μr r = Runtime r

class EmbedRuntime s r where
  runtime :: r -> s

instance
  ( Monad m,
    EmbedStage μs,
    TypeCheck μr m r,
    CheckRepresentation μr p m
  ) =>
  TypeCheckImpl m p (Runtime μr r) μs
  where
  typeCheckImpl p (Runtime r) = do
    Representation <- checkRepresentation p =<< typeCheck @μr r
    pure stage

instance FreeVariables u p r => FreeVariablesImpl u p (Runtime μr r) where
  freeVariablesImpl _ (Runtime r) = freeVariables @u r

instance (EmbedRuntime s r, Substitute u r) => SubstituteImpl (Runtime μr r) u s where
  substituteImpl ux x (Runtime r) = runtime (substitute ux x r)
