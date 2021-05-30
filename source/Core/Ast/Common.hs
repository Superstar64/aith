module Core.Ast.Common where

import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier
import Misc.Isomorph
import Misc.Variables (Variables)
import qualified Misc.Variables as Variables

data Internal = Internal deriving (Show)

instance Semigroup Internal where
  Internal <> Internal = Internal

data Bound pm e = Bound pm e deriving (Show)

instance Bifunctor Bound where
  bimap f g (Bound a b) = Bound (f a) (g b)

bound = Isomorph (uncurry Bound) $ \(Bound pm e) -> (pm, e)

class Semigroup p => Algebra u p e | e -> p where
  freeVariables :: e -> Variables p
  convert :: Identifier -> Identifier -> e -> e
  substitute :: u -> Identifier -> e -> e

-- Applicative Order Reduction
-- see https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf

class Reduce e where
  reduce :: e -> e

instance Reduce e => Reduce [e] where
  reduce = map reduce

instance (Reduce pm, Reduce e) => Reduce (Bound pm e) where
  reduce (Bound pm e) = Bound (reduce pm) (reduce e)

class Semigroup p => Binder p pm | pm -> p where
  bindings :: pm -> Variables p
  rename :: Identifier -> Identifier -> pm -> pm

class Apply λ σ e where
  apply :: λ -> σ -> e

internalVariable x = Variables.singleton x Internal

avoidCapture ::
  forall σ p pm e u.
  (Algebra σ p e, Algebra σ p u, Binder p pm) =>
  u ->
  Bound pm e ->
  Bound pm e
avoidCapture = avoidCaptureGeneral (freeVariables @σ @p) (convert @σ)

avoidCaptureGeneral freeVariables convert ux λ@(Bound pm _) = foldr replace λ replacing
  where
    replace x (Bound pm σ) = Bound (rename x' x pm) (convert x' x σ)
      where
        x' = Variables.fresh disallowed x
    replacing = map fst $ Variables.toList $ bindings pm
    disallowed = freeVariables ux

-- term into term pattern bound
substituteSame _ _ _ x λ@(Bound pm _) | x `Variables.member` bindings pm = λ
substituteSame substitute avoidCapture ux x λ = Bound pm (substitute ux x e)
  where
    Bound pm e = avoidCapture ux λ

-- term into type pattern bound
substituteLower substitute avoidCapture ux x λ = Bound pm (substitute ux x e)
  where
    Bound pm e = avoidCapture ux λ

-- type into term pattern bound
substituteHigher substitutepm substitutee ux x (Bound pm e) = Bound (substitutepm ux x pm) (substitutee ux x e)

removeBinds free binds = foldr Variables.delete free (map fst $ Variables.toList $ binds)

class Location f where
  location :: f a -> a
