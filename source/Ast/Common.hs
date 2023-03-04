module Ast.Common where

import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Misc.Isomorph

newtype Source x y = Source {runSource :: x}
  deriving (Show)

source = Isomorph Source runSource

instance Bifunctor Source where
  bimap f _ (Source x) = Source (f x)

instance Bifoldable Source where
  bifoldMap f _ (Source x) = f x

instance Bitraversable Source where
  bitraverse f _ (Source x) = Source <$> f x

newtype Core x y = Core {runCore :: y}
  deriving (Show)

-- hack for showable types
class IsCore phase where
  core :: typef (phase unit void) v (typescheme phase p v) (typex phase p v) -> typef (Core unit void) v (typescheme Core p v) (typex Core p v)

instance IsCore Core where
  core = id

instance Bifunctor Core where
  bimap _ g (Core x) = Core (g x)

instance Bifoldable Core where
  bifoldMap _ g (Core x) = g x

instance Bitraversable Core where
  bitraverse _ g (Core x) = Core <$> g x

data Bound pm e = Bound pm e deriving (Show)

newtype Variables x p = Variables {runVariables :: Map x p} deriving (Show)

traverseBound ::
  Applicative m =>
  (pm -> m pm') ->
  (e -> m e') ->
  (Bound pm e) ->
  m (Bound pm' e')
traverseBound f g (Bound pm e) = pure Bound <*> f pm <*> g e

mapBound f g = runIdentity . traverseBound (Identity . f) (Identity . g)

foldBound f g = getConst . traverseBound (Const . f) (Const . g)

bound = Isomorph (uncurry Bound) $ \(Bound pm e) -> (pm, e)

class Fresh i where
  fresh :: Set i -> i -> i

instance (Ord x, Semigroup p) => Semigroup (Variables x p) where
  Variables a <> Variables b = Variables $ Map.unionWith (<>) a b

instance (Ord x, Semigroup p) => Monoid (Variables x p) where
  mappend = (<>)
  mempty = Variables $ Map.empty

skip _ _ = False

pass _ _ = id

freeVariablesBound ::
  Ord x =>
  (pm -> Set x) ->
  (pm -> Set x) ->
  (e -> Set x) ->
  Bound pm e ->
  Set x
freeVariablesBound bindings freeVariablespm freeVariables (Bound pm e) =
  foldr Set.delete (freeVariablespm pm <> freeVariables e) (Set.toList $ bindings pm)

freeVariablesBoundSource ::
  (Ord x, Semigroup p) =>
  (pm -> Set x) ->
  (pm -> Variables x p) ->
  (e -> Variables x p) ->
  Bound pm e ->
  Variables x p
freeVariablesBoundSource bindings freeVariablespm freeVariables (Bound pm e) =
  foldr (\b m -> Variables $ Map.delete b $ runVariables $ m) (freeVariablespm pm <> freeVariables e) (Set.toList $ bindings pm)

substituteBound ::
  (x -> pm -> Bool) ->
  (σ -> Bound pm e -> Bound pm e) ->
  (σ -> x -> pm -> pm) ->
  (σ -> x -> e -> e) ->
  σ ->
  x ->
  Bound pm e ->
  Bound pm e
substituteBound guard _ _ _ _ x λ@(Bound pm _) | guard x pm = λ
substituteBound _ avoidCapture substitutepm substitute ux x λ = Bound (substitutepm ux x pm) (substitute ux x e)
  where
    Bound pm e = avoidCapture ux λ

-- term into dependent term bound

substituteDependent ::
  (Ord x, Fresh x) =>
  Avoid pm x σ e ->
  (σ -> x -> pm -> pm) ->
  (σ -> x -> e -> e) ->
  σ ->
  x ->
  Bound pm e ->
  Bound pm e
substituteDependent avoid = substituteBound (\x pm -> x `Set.member` avoidBindings avoid pm) (avoidCapture avoid)

-- type into term pattern bound

freeVariablesHigher ::
  Ord x =>
  (pm -> Set x) ->
  (e -> Set x) ->
  Bound pm e ->
  Set x
freeVariablesHigher = freeVariablesBound mempty

freeVariablesHigherSource = freeVariablesBoundSource mempty

substituteHigher ::
  (σ -> x -> pm -> pm) ->
  (σ -> x -> e -> e) ->
  σ ->
  x ->
  Bound pm e ->
  Bound pm e
substituteHigher = substituteBound skip (const id)

-- term into term pattern bound
freeVariablesSame ::
  Ord x =>
  (pm -> Set x) ->
  (e -> Set x) ->
  Bound pm e ->
  Set x
freeVariablesSame bindings freeVariables = freeVariablesBound bindings mempty freeVariables

freeVariablesSameSource bindings freeVariables = freeVariablesBoundSource bindings mempty freeVariables

substituteSame ::
  (Ord x, Fresh x) =>
  Avoid pm x σ e ->
  (σ -> x -> e -> e) ->
  σ ->
  x ->
  Bound pm e ->
  Bound pm e
substituteSame avoid = substituteBound (\x pm -> x `Set.member` avoidBindings avoid pm) (avoidCapture avoid) pass

-- term into type pattern bound
freeVariablesLower freeVariables (Bound _ e) = freeVariables e

convertLower convert ux x (Bound pm e) = Bound pm (convert ux x e)

substituteLower ::
  Fresh x' =>
  Avoid pm x' σ e ->
  (σ -> x -> e -> e) ->
  σ ->
  x ->
  Bound pm e ->
  Bound pm e
substituteLower avoid = substituteBound skip (avoidCapture avoid) pass

data Avoid pm x σ e = Avoid
  { avoidBindings :: pm -> Set x,
    avoidRename :: x -> x -> pm -> pm,
    avoidFreeVariables :: σ -> Set x,
    avoidConvert :: x -> x -> e -> e
  }

avoidCapture :: Fresh x => Avoid pm x σ e -> σ -> Bound pm e -> Bound pm e
avoidCapture (Avoid bindings rename freeVariables convert) ux λ@(Bound pm _) = foldr replace λ replacing
  where
    replace x (Bound pm σ) = Bound (rename x' x pm) (convert x' x σ)
      where
        x' = fresh disallowed x
    replacing = Set.toList $ bindings pm
    disallowed = freeVariables ux
