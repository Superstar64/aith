module Ast.Common where

import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Misc.Isomorph

data Internal = Internal deriving (Show)

data Bound pm e = Bound pm e deriving (Show)

data Pattern i σ p = Pattern p i σ deriving (Show, Functor)

data Variables x p = Variables {runVariables :: Map x p} deriving (Show)

traverseBound ::
  Applicative m =>
  (pm -> m pm') ->
  (e -> m e') ->
  (Bound pm e) ->
  m (Bound pm' e')
traverseBound f g (Bound pm e) = pure Bound <*> f pm <*> g e

mapBound f g = runIdentity . traverseBound (Identity . f) (Identity . g)

foldBound f g = getConst . traverseBound (Const . f) (Const . g)

traversePattern ::
  Applicative m =>
  (i -> m i') ->
  (σ -> m σ') ->
  (p -> m p') ->
  Pattern i σ p ->
  m (Pattern i' σ' p')
traversePattern f g h (Pattern p i σ) = pure Pattern <*> h p <*> f i <*> g σ

mapPattern f g h = runIdentity . traversePattern (Identity . f) (Identity . g) (Identity . h)

bound = Isomorph (uncurry Bound) $ \(Bound pm e) -> (pm, e)

pattern = Isomorph (uncurry $ uncurry Pattern) (\(Pattern p i σ) -> ((p, i), σ))

-- Applicative Order Reduction
-- see https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf

class Reduce e where
  reduce :: e -> e

class Fresh i where
  fresh :: Set i -> i -> i

instance Semigroup Internal where
  Internal <> Internal = Internal

instance Monoid Internal where
  mempty = Internal
  mappend = (<>)

instance (Ord x, Semigroup p) => Semigroup (Variables x p) where
  Variables a <> Variables b = Variables $ Map.unionWith (<>) a b

instance (Ord x, Semigroup p) => Monoid (Variables x p) where
  mappend = (<>)
  mempty = Variables $ Map.empty

instance (Reduce pm, Reduce e) => Reduce (Bound pm e) where
  reduce (Bound pm e) = Bound (reduce pm) (reduce e)

rename' ux x (Pattern p x' σ) | x == x' = Pattern p ux σ
rename' _ _ pm = pm

bindings' (Pattern _ x _) = Set.singleton x

-- type into term pattern bound

freeVariablesHigher' freeVariables freeVariables' (Bound pm e) = freeVariables pm <> freeVariables' e

substituteHigher' substitute substitute' ux x (Bound pm e) = Bound (substitute ux x pm) (substitute' ux x e)

-- term into term pattern bound
freeVariablesSame' freeVariables bindings (Bound pm e) = foldr Set.delete (freeVariables e) (Set.toList $ bindings pm)

freeVariablesSameSource' freeVariables bindings (Bound pm e) = foldr delete (freeVariables e) (Set.toList $ bindings pm)
  where
    delete x (Variables m) = Variables $ Map.delete x m

substituteSame' _ (Avoid bindings _ _ _) _ x λ@(Bound pm _) | x `Set.member` bindings pm = λ
substituteSame' substitute avoid ux x λ = Bound pm (substitute ux x e)
  where
    Bound pm e = avoidCapture' avoid ux λ

-- term into type pattern bound
freeVariablesLower' freeVariables (Bound _ e) = freeVariables e

convertLower' convert ux x (Bound pm e) = Bound pm (convert ux x e)

substituteLower' substitute avoid ux x λ = Bound pm (substitute ux x e)
  where
    Bound pm e = avoidCapture' avoid ux λ

data Avoid pm x σ e = Avoid (pm -> Set x) (x -> x -> pm -> pm) (σ -> Set x) (x -> x -> e -> e)

avoidCapture' (Avoid bindings rename freeVariables convert) ux λ@(Bound pm _) = foldr replace λ replacing
  where
    replace x (Bound pm σ) = Bound (rename x' x pm) (convert x' x σ)
      where
        x' = fresh disallowed x
    replacing = Set.toList $ bindings pm
    disallowed = freeVariables ux

class Location f where
  location :: f a -> a
