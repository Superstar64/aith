module Core.Ast.Common where

import Misc.Identifier
import Misc.Isomorph
import Misc.Variables (Variables)
import qualified Misc.Variables as Variables

data Internal = Internal deriving (Show)

instance Semigroup Internal where
  Internal <> Internal = Internal

data Bound pm e = Bound pm e deriving (Show)

bound = Isomorph (uncurry Bound) $ \(Bound pm e) -> (pm, e)

class FreeVariables u p e where
  freeVariables :: e -> Variables p

instance (Semigroup p, FreeVariables u p e) => FreeVariables u p [e] where
  freeVariables = foldMap (freeVariables @u)

class Substitute u e where
  substitute :: u -> Identifier -> e -> e

instance Substitute u e => Substitute u [e] where
  substitute ux x es = substitute ux x <$> es

-- Applicative Order Reduction
-- see https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf

class Reduce e where
  reduce :: e -> e

instance Reduce e => Reduce [e] where
  reduce = map reduce

instance (Reduce pm, Reduce e) => Reduce (Bound pm e) where
  reduce (Bound pm e) = Bound (reduce pm) (reduce e)

class Bindings p pm where
  bindings :: pm -> Variables p

class Rename pm where
  rename :: Identifier -> Identifier -> pm -> pm

class Apply pm σ e where
  apply :: pm -> σ -> e

freeVariablesInternal :: forall u e. FreeVariables u Internal e => e -> Variables Internal
freeVariablesInternal = freeVariables @u @Internal

bindingsInternal = bindings @Internal

avoidCapture variable free ux λ@(Bound pm _) = foldr replace λ replacing
  where
    replace x (Bound pm σ) = Bound (rename x' x pm) (substitute (variable x') x σ)
      where
        x' = Variables.fresh disallowed x
    replacing = map fst $ Variables.toList $ bindingsInternal pm
    disallowed = free ux

removeBinds free binds = foldr Variables.delete free (map fst $ Variables.toList $ binds)

class Location f where
  location :: f a -> a
