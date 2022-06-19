module Ast.Kind where

import Ast.Common
import Ast.Sort
import Control.Category ((.))
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
import Misc.Explode
import Misc.Isomorph
import Misc.Prism
import qualified Misc.Util as Util
import Prelude hiding ((.))

newtype KindIdentifier = KindIdentifier {runKindIdentifier :: String} deriving (Show, Eq, Ord)

newtype KindLogical = KindLogicalRaw Int deriving (Eq, Ord, Show)

data KindSize
  = Byte
  | Short
  | Int
  | Long
  | Native
  deriving (Show, Eq, Ord)

data KindSignedness
  = Signed
  | Unsigned
  deriving (Show, Eq, Ord)

data KindRuntime s κ
  = PointerRep
  | StructRep [κ]
  | WordRep s
  deriving (Show, Eq, Ord)

data KindF v κ
  = KindVariable KindIdentifier
  | KindLogical v
  | Type
  | Region
  | Pretype κ
  | Boxed
  | Length
  | KindRuntime (KindRuntime κ κ)
  | KindSize (KindSize)
  | KindSignedness (KindSignedness)
  deriving (Show, Eq, Ord)

traverseKindF ::
  Applicative m =>
  (v -> m v') ->
  (κ -> m κ') ->
  KindF v κ ->
  m (KindF v' κ')
traverseKindF f g κ = case κ of
  KindVariable x -> pure KindVariable <*> pure x
  KindLogical v -> pure KindLogical <*> f v
  Type -> pure Type
  Region -> pure Region
  Pretype κ -> pure Pretype <*> g κ
  Boxed -> pure Boxed
  Length -> pure Length
  KindRuntime PointerRep -> KindRuntime <$> (pure PointerRep)
  KindRuntime (StructRep κs) -> KindRuntime <$> (pure StructRep <*> traverse g κs)
  KindRuntime (WordRep κ) -> KindRuntime <$> (pure WordRep <*> g κ)
  (KindSize κ) -> pure (KindSize κ)
  (KindSignedness κ) -> pure (KindSignedness κ)

foldKindF f g = getConst . traverseKindF (Const . f) (Const . g)

mapKindF f g = runIdentity . traverseKindF (Identity . f) (Identity . g)

data KindSource p = KindSource p (KindF Void (KindSource p)) deriving (Show)

type KindAuto p = Maybe (KindSource p)

data Kind v = KindCore (KindF v (Kind v)) deriving (Show)

type KindUnify = Kind KindLogical

type KindInfer = Kind Void

data KindPatternSource p = KindPatternSource p KindIdentifier Sort deriving (Show, Functor)

data KindPatternIntermediate p = KindPatternIntermediate p KindIdentifier Sort deriving (Show)

data KindPattern = KindPattern KindIdentifier Sort deriving (Show)

instance Functor KindSource where
  fmap f (KindSource p κ) = KindSource (f p) $ mapKindF id (fmap f) κ

kindIdentifier = Isomorph KindIdentifier runKindIdentifier

kindSource = Isomorph (uncurry KindSource) $ \(KindSource p κ) -> (p, κ)

kindRuntime = Prism KindRuntime $ \case
  (KindRuntime κ) -> Just κ
  _ -> Nothing

kindSize = Prism KindSize $ \case
  (KindSize κ) -> Just κ
  _ -> Nothing

kindSignedness = Prism KindSignedness $ \case
  (KindSignedness κ) -> Just κ
  _ -> Nothing

kindVariable = Prism KindVariable $ \case
  (KindVariable x) -> Just x
  _ -> Nothing

kindExtra = Prism KindLogical $ \case
  (KindLogical v) -> Just v
  _ -> Nothing

typex = Prism (const Type) $ \case
  Type -> Just ()
  _ -> Nothing

region = Prism (const Region) $ \case
  Region -> Just ()
  _ -> Nothing

pretype = Prism Pretype $ \case
  Pretype κ -> Just κ
  _ -> Nothing

boxed = Prism (const Boxed) $ \case
  Boxed -> pure ()
  _ -> Nothing

capacity = Prism (const Length) $ \case
  Length -> pure ()
  _ -> Nothing

pointerRep = (kindRuntime .) $
  Prism (const PointerRep) $ \case
    PointerRep -> Just ()
    _ -> Nothing

structRep = (kindRuntime .) $
  Prism StructRep $ \case
    (StructRep ρs) -> Just ρs
    _ -> Nothing

wordRep = (kindRuntime .) $
  Prism WordRep $ \case
    (WordRep κ) -> Just κ
    _ -> Nothing

byte = (kindSize .) $
  Prism (const Byte) $ \case
    Byte -> Just ()
    _ -> Nothing

short = (kindSize .) $
  Prism (const Short) $ \case
    Short -> Just ()
    _ -> Nothing

int = (kindSize .) $
  Prism (const Int) $ \case
    Int -> Just ()
    _ -> Nothing

long = (kindSize .) $
  Prism (const Long) $ \case
    Long -> Just ()
    _ -> Nothing

native = (kindSize .) $
  Prism (const Native) $ \case
    Native -> Just ()
    _ -> Nothing

signed = (kindSignedness .) $
  Prism (const Signed) $ \case
    Signed -> Just ()
    _ -> Nothing

unsigned = (kindSignedness .) $
  Prism (const Unsigned) $ \case
    Unsigned -> Just ()
    _ -> Nothing

kindPatternSource = Isomorph (uncurry $ uncurry KindPatternSource) $ \(KindPatternSource p x μ) -> ((p, x), μ)

-- use explode for rather then order because sorting with logic variables isn't dangerous
instance Explode v => Eq (Kind v) where
  KindCore κ == KindCore κ' = κ == κ'

instance Explode v => Ord (Kind v) where
  KindCore κ <= KindCore κ' = κ <= κ'

class FreeVariablesKind u where
  freeVariablesKind :: u -> Set KindIdentifier

class ConvertKind u where
  convertKind :: KindIdentifier -> KindIdentifier -> u -> u

class SubstituteKind u where
  substituteKind :: Kind v -> KindIdentifier -> u v -> u v

-- traverse and monadic bind
class ZonkKind u where
  zonkKind :: Applicative m => (v -> m (Kind v')) -> u v -> m (u v')

class BindingsKind u where
  bindingsKind :: u -> Set KindIdentifier

class RenameKind u where
  renameKind :: KindIdentifier -> KindIdentifier -> u -> u

freeVariablesHigherKind = freeVariablesHigher freeVariablesKind freeVariablesKind

convertHigherKind = substituteHigher convertKind convertKind

substituteHigherKind = substituteHigher substituteKind substituteKind

freeVariablesSameKind = freeVariablesSame bindingsKind freeVariablesKind

convertSameKind = substituteSame avoidKindConvert convertKind

substituteSameKind = substituteSame avoidKind substituteKind

convertSameKindSource = substituteSame avoidKindConvert convertKind

freeVariablesRgnForKind = freeVariablesHigher freeVariablesKind freeVariablesHigherKind

convertRgnForKind = substituteHigher convertKind convertHigherKind

substituteRgnForKind = substituteHigher substituteKind substituteHigherKind

avoidKindConvert = avoidKindConvert' convertKind

avoidKindConvert' = Avoid bindingsKind renameKind Set.singleton

avoidKind = avoidKind' convertKind

avoidKind' = Avoid bindingsKind renameKind freeVariablesKind

toKindPattern (KindPatternIntermediate _ x μ) = KindPattern x μ

instance Fresh KindIdentifier where
  fresh c (KindIdentifier x) = KindIdentifier $ Util.fresh (Set.mapMonotonic runKindIdentifier c) x

instance BindingsKind KindPattern where
  bindingsKind (KindPattern x _) = Set.singleton x

instance RenameKind KindPattern where
  renameKind ux x (KindPattern x' κ) | x == x' = KindPattern ux κ
  renameKind _ _ λ@(KindPattern _ _) = λ

instance BindingsKind (KindPatternSource p) where
  bindingsKind (KindPatternSource _ x _) = Set.singleton x

instance RenameKind (KindPatternSource p) where
  renameKind ux x (KindPatternSource p x' κ) | x == x' = KindPatternSource p ux κ
  renameKind _ _ λ@(KindPatternSource _ _ _) = λ

instance FreeVariablesKind (Kind v) where
  freeVariablesKind (KindCore (KindVariable x)) = Set.singleton x
  freeVariablesKind (KindCore κ) = foldKindF mempty go κ
    where
      go = freeVariablesKind

instance ConvertKind (KindSource p) where
  convertKind ux x (KindSource p (KindVariable x')) | x == x' = KindSource p (KindVariable ux)
  convertKind ux x (KindSource p κ) = KindSource p $ mapKindF id go κ
    where
      go = convertKind ux x

instance ConvertKind (Kind v) where
  convertKind ux x (KindCore (KindVariable x')) | x == x' = KindCore (KindVariable ux)
  convertKind ux x (KindCore κ) = KindCore $ mapKindF id go κ
    where
      go = convertKind ux x

instance SubstituteKind Kind where
  substituteKind ux x (KindCore (KindVariable x')) | x == x' = ux
  substituteKind ux x (KindCore κ) = KindCore $ mapKindF id go κ
    where
      go = substituteKind ux x

instance ZonkKind Kind where
  zonkKind f (KindCore (KindLogical v)) = f v
  zonkKind f (KindCore κ) =
    pure KindCore
      <*> traverseKindF (error "handled manually") (zonkKind f) κ

instance Reduce (Kind v) where
  reduce = id

instance Reduce (KindPattern) where
  reduce = id

instance Location KindSource where
  location (KindSource p _) = p

freeKindLogical = getConst . zonkKind (Const . Set.singleton)

sourceKind (KindCore κ) = KindSource mempty $ mapKindF id sourceKind κ

sourceKindAuto = Just . sourceKind

sourceKindPattern (KindPattern x μ) = KindPatternSource mempty x μ

flexibleKind = runIdentity . zonkKind absurd
