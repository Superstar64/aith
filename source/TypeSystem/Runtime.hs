module TypeSystem.Runtime where

import TypeSystem.Methods
import TypeSystem.Representation
import TypeSystem.Stage

data Runtime μρ ρ = Runtime ρ

class EmbedRuntime s ρ where
  runtime :: ρ -> s

class CheckRuntime ρ s m p where
  checkRuntime :: p -> ρ -> m (Runtime μs s)

instance
  ( Monad m,
    EmbedStage μs,
    TypeCheck μρ m ρ,
    CheckRepresentation μρ p m
  ) =>
  TypeCheckImpl m p (Runtime μρ ρ) μs
  where
  typeCheckImpl p (Runtime ρ) = do
    Representation <- checkRepresentation p =<< typeCheck @μρ ρ
    pure stage

instance FreeVariables u p ρ => FreeVariablesImpl u p (Runtime μρ ρ) where
  freeVariablesImpl _ (Runtime ρ) = freeVariables @u ρ

instance (EmbedRuntime s ρ, Substitute u ρ) => SubstituteImpl (Runtime μρ ρ) u s where
  substituteImpl ux x (Runtime ρ) = runtime (substitute ux x ρ)
