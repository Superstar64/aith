module Ast.Common where

import Data.Bifoldable (Bifoldable, bifoldMap)
import Data.Bifunctor (Bifunctor, bimap)
import Data.Bitraversable (Bitraversable, bitraverse)
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.Set (Set)
import qualified Data.Set as Set
import Misc.Isomorph
import Misc.MonoidMap (Map)
import qualified Misc.MonoidMap as Map
import qualified Misc.Util as Util

data Internal = Internal deriving (Show)

data Bound pm e = Bound pm e deriving (Show)

data Pattern i σ p = Pattern p i σ deriving (Show, Functor)

bound = Isomorph (uncurry Bound) $ \(Bound pm e) -> (pm, e)

pattern = Isomorph (uncurry $ uncurry Pattern) (\(Pattern p i σ) -> ((p, i), σ))

mapPattern f g h = runIdentity . traversePattern (Identity . f) (Identity . g) (Identity . h)

traversePattern ::
  Applicative m =>
  (i -> m i') ->
  (σ -> m σ') ->
  (p -> m p') ->
  Pattern i σ p ->
  m (Pattern i' σ' p')
traversePattern f g h (Pattern p i σ) = pure Pattern <*> h p <*> f i <*> g σ

instance Semigroup Internal where
  Internal <> Internal = Internal

instance Bifunctor Bound where
  bimap f g (Bound a b) = Bound (f a) (g b)

instance Bifoldable Bound where
  bifoldMap f g (Bound a b) = f a <> g b

instance Bitraversable Bound where
  bitraverse f g (Bound a b) = pure Bound <*> f a <*> g b

class FreeVariables x p e where
  freeVariables :: e -> Map x p

class FreeVariablesInternal x e where
  freeVariablesInternal :: e -> Map x Internal

class Convert x e where
  convert :: x -> x -> e -> e

class Substitute u x e where
  substitute :: u -> x -> e -> e

class Bindings x p pm where
  bindings :: pm -> Map x p

class BindingsInternal x pm where
  bindingsInternal :: pm -> Map x Internal

class Rename x pm where
  rename :: x -> x -> pm -> pm

class Correct θ e where
  correct :: θ -> e -> e

-- Applicative Order Reduction
-- see https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf

class Reduce e where
  reduce :: e -> e

class Apply λ σ e where
  apply :: λ -> σ -> e

class UnInfer e e' | e -> e' where
  unInfer :: e -> e'

instance (Reduce pm, Reduce e) => Reduce (Bound pm e) where
  reduce (Bound pm e) = Bound (reduce pm) (reduce e)

instance FreeVariables x p σ => FreeVariables x p (Pattern i σ p) where
  freeVariables (Pattern _ _ σ) = freeVariables σ

instance FreeVariablesInternal x σ => FreeVariablesInternal x (Pattern i σ p) where
  freeVariablesInternal (Pattern _ _ σ) = freeVariablesInternal σ

instance Convert x σ => Convert x (Pattern i σ p) where
  convert ux x (Pattern p x' σ) = Pattern p x' (convert ux x σ)

instance Substitute u x σ => Substitute u x (Pattern i σ p) where
  substitute ux x (Pattern p x' σ) = Pattern p x' (substitute ux x σ)

instance Eq i => Rename i (Pattern i σ p) where
  rename ux x (Pattern p x' σ) | x == x' = Pattern p ux σ
  rename _ _ pm = pm

instance Bindings i p (Pattern i σ p) where
  bindings (Pattern p x _) = Map.singleton x p

instance BindingsInternal i (Pattern i σ p) where
  bindingsInternal (Pattern _ x _) = Map.singleton x Internal

instance Reduce σ => Reduce (Pattern i σ p) where
  reduce (Pattern p x σ) = Pattern p x (reduce σ)

instance (Ord x, Semigroup p, FreeVariables x p a, FreeVariables x p b) => FreeVariables x p (a, b) where
  freeVariables (a, b) = freeVariables a <> freeVariables b

instance (Convert x a, Convert x b) => Convert x (a, b) where
  convert ux x (a, b) = (convert ux x a, convert ux x b)

instance (Substitute u x a, Substitute u x b) => Substitute u x (a, b) where
  substitute ux x (a, b) = (substitute ux x a, substitute ux x b)

instance (Bindings x p a, Bindings x p b, Ord x, Semigroup p) => Bindings x p (a, b) where
  bindings (a, b) = bindings a <> bindings b

instance (Rename i a, Rename i b) => Rename i (a, b) where
  rename ux x (a, b) = (rename ux x a, rename ux x b)

instance (Reduce a, Reduce b) => Reduce (a, b) where
  reduce (a, b) = (reduce a, reduce b)

instance (FreeVariables x p a, FreeVariables x p b) => FreeVariables x p (Either a b) where
  freeVariables (Left a) = freeVariables a
  freeVariables (Right b) = freeVariables b

instance (Convert x a, Convert x b) => Convert x (Either a b) where
  convert ux x (Left a) = Left $ convert ux x a
  convert ux x (Right b) = Right $ convert ux x b

instance (Substitute u x a, Substitute u x b) => Substitute u x (Either a b) where
  substitute ux x (Left a) = Left $ substitute ux x a
  substitute ux x (Right b) = Right $ substitute ux x b

instance (Bindings x p a, Bindings x p b) => Bindings x p (Either a b) where
  bindings (Left a) = bindings a
  bindings (Right b) = bindings b

instance (Rename i a, Rename i b) => Rename i (Either a b) where
  rename ux x (Left a) = Left $ rename ux x a
  rename ux x (Right b) = Right $ rename ux x b

instance (Reduce a, Reduce b) => Reduce (Either a b) where
  reduce (Left a) = Left (reduce a)
  reduce (Right b) = Right (reduce b)

instance (Ord x, Semigroup p, FreeVariables x p e) => FreeVariables x p [e] where
  freeVariables = foldMap freeVariables

instance (Ord x, FreeVariablesInternal x e) => FreeVariablesInternal x [e] where
  freeVariablesInternal = foldMap freeVariablesInternal

instance Convert x e => Convert x [e] where
  convert ux x = map (convert ux x)

instance Convert x e => Convert x (Map k e) where
  convert ux x = fmap (convert ux x)

instance Substitute u x e => Substitute u x [e] where
  substitute ux x = map (substitute ux x)

instance Substitute u x e => Substitute u x (Map k e) where
  substitute ux x = fmap (substitute ux x)

instance Reduce e => Reduce [e] where
  reduce = map reduce

instance
  ( Ord x,
    Semigroup p,
    FreeVariables x p e
  ) =>
  FreeVariables x p (Maybe e)
  where
  freeVariables Nothing = mempty
  freeVariables (Just e) = freeVariables e

class Fresh i where
  fresh :: Set i -> i -> i

newtype TermIdentifier = TermIdentifier {runTermIdentifier :: String} deriving (Show, Eq, Ord)

termIdentifier = Isomorph TermIdentifier runTermIdentifier

instance Fresh TermIdentifier where
  fresh c (TermIdentifier x) = TermIdentifier $ Util.fresh (Set.mapMonotonic runTermIdentifier c) x

newtype TypeIdentifier = TypeIdentifier {runTypeIdentifier :: String} deriving (Show, Eq, Ord)

typeIdentifier = Isomorph TypeIdentifier runTypeIdentifier

instance Fresh TypeIdentifier where
  fresh c (TypeIdentifier x) = TypeIdentifier $ Util.fresh (Set.mapMonotonic runTypeIdentifier c) x

newtype KindIdentifier = KindIdentifier {runKindIdentifier :: String} deriving (Show, Eq, Ord)

kindIdentifier = Isomorph KindIdentifier runKindIdentifier

instance Fresh KindIdentifier where
  fresh c (KindIdentifier x) = KindIdentifier $ Util.fresh (Set.mapMonotonic runKindIdentifier c) x

newtype TypeLogicalRaw = TypeLogicalRaw Int deriving (Eq, Ord, Show)

newtype KindLogicalRaw = KindLogicalRaw Int deriving (Eq, Ord, Show)

freeVariablesBound (Bound pm e) = foldr Map.delete (freeVariables e) (map fst $ Map.toList $ bindingsInternal pm)

freeVariablesBoundDependent (Bound pm e) = freeVariables pm <> foldr Map.delete (freeVariables e) (map fst $ Map.toList $ bindingsInternal pm)

substituteDependent _ _ _ _ x λ@(Bound pm _) | x `Map.member` bindingsInternal pm = λ
substituteDependent substitute substitute' avoidCapture ux x λ = Bound (substitute' ux x pm) (substitute ux x e)
  where
    Bound pm e = avoidCapture ux λ

-- term into term pattern bound
substituteSame _ _ _ x λ@(Bound pm _) | x `Map.member` bindingsInternal pm = λ
substituteSame substitute avoidCapture ux x λ = Bound pm (substitute ux x e)
  where
    Bound pm e = avoidCapture ux λ

-- term into type pattern bound
substituteLower substitute avoidCapture ux x λ = Bound pm (substitute ux x e)
  where
    Bound pm e = avoidCapture ux λ

-- type into term pattern bound
substituteHigher substitutepm substitutee ux x (Bound pm e) = Bound (substitutepm ux x pm) (substitutee ux x e)

internalVariable x = Map.singleton x Internal

avoidCapture ::
  forall x u σ e.
  ( Fresh x,
    BindingsInternal x σ,
    Rename x σ,
    Convert x e,
    FreeVariablesInternal x u
  ) =>
  u ->
  Bound σ e ->
  Bound σ e
avoidCapture ux λ@(Bound pm _) = foldr replace λ replacing
  where
    replace x (Bound pm σ) = Bound (rename x' x pm) (convert x' x σ)
      where
        x' = fresh (Map.keysSet disallowed) x
    replacing = map fst $ Map.toList $ bindingsInternal pm
    disallowed = freeVariablesInternal @x ux

avoidCaptureConvert ::
  forall x σ e.
  ( Fresh x,
    BindingsInternal x σ,
    Rename x σ,
    Convert x e
  ) =>
  x ->
  Bound σ e ->
  Bound σ e
avoidCaptureConvert ux λ@(Bound pm _) = foldr replace λ replacing
  where
    replace x (Bound pm σ) = Bound (rename x' x pm) (convert x' x σ)
      where
        x' = fresh (Map.keysSet disallowed) x
    replacing = map fst $ Map.toList $ bindingsInternal pm
    disallowed = internalVariable ux

instance
  ( FreeVariables TermIdentifier p u
  ) =>
  FreeVariables TermIdentifier p (Bound (Pattern TermIdentifier σ p) u)
  where
  freeVariables = freeVariablesBound

instance
  ( Convert TermIdentifier u
  ) =>
  Convert TermIdentifier (Bound (Pattern TermIdentifier σ p) u)
  where
  convert = substituteSame convert (avoidCaptureConvert @TermIdentifier)

instance
  ( Convert TermIdentifier u,
    FreeVariablesInternal TermIdentifier e,
    Substitute e TermIdentifier u
  ) =>
  Substitute e TermIdentifier (Bound (Pattern TermIdentifier σ p) u)
  where
  substitute = substituteSame substitute (avoidCapture @TermIdentifier)

instance
  ( FreeVariables TermIdentifier p u
  ) =>
  FreeVariables TermIdentifier p (Bound (Pattern TypeIdentifier κ p) u)
  where
  freeVariables (Bound _ e) = freeVariables e

instance
  ( Convert TermIdentifier u
  ) =>
  Convert TermIdentifier (Bound (Pattern TypeIdentifier κ p) u)
  where
  convert = substituteLower convert (const id)

instance
  ( FreeVariablesInternal TypeIdentifier e,
    Substitute e TermIdentifier u,
    Convert TypeIdentifier u
  ) =>
  Substitute e TermIdentifier (Bound (Pattern TypeIdentifier κ p) u)
  where
  substitute = substituteLower substitute (avoidCapture @TypeIdentifier)

instance
  ( Semigroup p,
    FreeVariables TypeIdentifier p σ,
    FreeVariables TypeIdentifier p u
  ) =>
  FreeVariables TypeIdentifier p (Bound (Pattern TermIdentifier σ p) u)
  where
  freeVariables (Bound pm e) = freeVariables pm <> freeVariables e

instance
  ( Substitute σ TypeIdentifier u,
    Substitute σ TypeIdentifier σ'
  ) =>
  Substitute σ TypeIdentifier (Bound (Pattern TermIdentifier σ' p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  (FreeVariables TypeIdentifier p u) =>
  FreeVariables TypeIdentifier p (Bound (Pattern TypeIdentifier κ p) u)
  where
  freeVariables = freeVariablesBound

instance
  ( Convert TypeIdentifier u
  ) =>
  Convert TypeIdentifier (Bound (Pattern TypeIdentifier κ p) u)
  where
  convert = substituteSame convert (avoidCaptureConvert @TypeIdentifier)

instance
  ( Substitute σ TypeIdentifier u,
    Convert TypeIdentifier u,
    FreeVariablesInternal TypeIdentifier σ
  ) =>
  Substitute σ TypeIdentifier (Bound (Pattern TypeIdentifier κ p) u)
  where
  substitute = substituteSame substitute (avoidCapture @TypeIdentifier)

instance
  (FreeVariables TypeIdentifier p u) =>
  FreeVariables TypeIdentifier p (Bound (Pattern KindIdentifier μ p) u)
  where
  freeVariables (Bound _ e) = freeVariables e

instance
  ( Convert TypeIdentifier u
  ) =>
  Convert TypeIdentifier (Bound (Pattern KindIdentifier μ p) u)
  where
  convert = substituteLower convert (const id)

instance
  ( Substitute σ TypeIdentifier u,
    Convert KindIdentifier u,
    FreeVariablesInternal KindIdentifier σ
  ) =>
  Substitute σ TypeIdentifier (Bound (Pattern KindIdentifier μ p) u)
  where
  substitute = substituteLower substitute (avoidCapture @KindIdentifier)

instance
  ( Semigroup p,
    FreeVariables KindIdentifier p u,
    FreeVariables KindIdentifier p κ
  ) =>
  FreeVariables KindIdentifier p (Bound (Pattern TypeIdentifier κ p) u)
  where
  freeVariables (Bound κ e) = freeVariables κ <> freeVariables e

instance
  ( Substitute κ KindIdentifier u,
    Substitute κ KindIdentifier σ
  ) =>
  Substitute κ KindIdentifier (Bound (Pattern TermIdentifier σ p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  ( Convert KindIdentifier u,
    Convert KindIdentifier κ
  ) =>
  Convert KindIdentifier (Bound (Pattern TypeIdentifier κ p) u)
  where
  convert = substituteHigher convert convert

instance
  ( Substitute κ KindIdentifier u,
    Substitute κ KindIdentifier κ'
  ) =>
  Substitute κ KindIdentifier (Bound (Pattern TypeIdentifier κ' p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  ( Convert KindIdentifier u
  ) =>
  Convert KindIdentifier (Bound (Pattern KindIdentifier μ p) u)
  where
  convert = substituteSame convert (avoidCaptureConvert @KindIdentifier)

instance
  ( Substitute κ KindIdentifier u,
    Convert KindIdentifier u,
    FreeVariablesInternal KindIdentifier κ
  ) =>
  Substitute κ KindIdentifier (Bound (Pattern KindIdentifier μ p) u)
  where
  substitute = substituteSame substitute (avoidCapture @KindIdentifier)

instance
  ( FreeVariables KindLogicalRaw p u,
    Semigroup p,
    FreeVariables KindLogicalRaw p κ
  ) =>
  FreeVariables KindLogicalRaw p (Bound (Pattern TypeIdentifier κ p) u)
  where
  freeVariables (Bound pm e) = freeVariables pm <> freeVariables e

instance
  ( Substitute κ KindLogicalRaw u,
    Substitute κ KindLogicalRaw κ
  ) =>
  Substitute κ KindLogicalRaw (Bound (Pattern TypeIdentifier κ p) u)
  where
  substitute = substituteHigher substitute substitute

instance
  ( FreeVariables TypeLogicalRaw p u
  ) =>
  FreeVariables TypeLogicalRaw p (Bound (Pattern TypeIdentifier κ p) u)
  where
  freeVariables = freeVariablesBound

instance
  ( Convert TypeIdentifier u,
    FreeVariablesInternal TypeIdentifier σ,
    Substitute σ TypeLogicalRaw u
  ) =>
  Substitute σ TypeLogicalRaw (Bound (Pattern TypeIdentifier κ p) u)
  where
  substitute = substituteLower substitute (avoidCapture @TypeIdentifier)

instance BindingsInternal TypeLogicalRaw (Pattern TypeIdentifier κ p) where
  bindingsInternal = mempty

class Location f where
  location :: f a -> a
