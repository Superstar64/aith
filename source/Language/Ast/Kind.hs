module Language.Ast.Kind where

import Control.Category ((.))
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.Void (Void, absurd)
import Language.Ast.Common
import Misc.Isomorph
import qualified Misc.MonoidMap as Map
import Misc.Prism
import Prelude hiding ((.))

data KindSize
  = Byte
  | Short
  | Int
  | Long
  deriving (Show)

data KindSignedness
  = Signed
  | Unsigned
  deriving (Show)

data KindRuntime s κ
  = PointerRep
  | StructRep [κ]
  | WordRep s
  deriving (Show)

data KindF v κ
  = KindVariable KindIdentifier
  | KindExtra v
  | Type κ
  | Evidence
  | Region
  | Runtime κ κ
  | Code
  | Data
  | Imaginary
  | Real κ
  | Meta
  | Text
  | KindRuntime (KindRuntime κ κ)
  | KindSize (KindSize)
  | KindSignedness (KindSignedness)
  deriving (Show)

data Kind v p = CoreKind p (KindF v (Kind v p)) deriving (Show)

type KindAuto p = Maybe (Kind Void p)

type KindInfer = Kind Void Internal

instance UnInfer KindInfer (KindAuto Internal) where
  unInfer = Just . mapKind absurd id

coreKind = Isomorph (uncurry CoreKind) $ \(CoreKind p κ) -> (p, κ)

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

kindExtra = Prism KindExtra $ \case
  (KindExtra v) -> Just v
  _ -> Nothing

typex = Prism Type $ \case
  (Type κ) -> Just κ
  _ -> Nothing

evidence = Prism (const Evidence) $ \case
  Evidence -> Just ()
  _ -> Nothing

region = Prism (const Region) $ \case
  Region -> Just ()
  _ -> Nothing

runtime = Prism (uncurry Runtime) $ \case
  (Runtime κ κ') -> Just (κ, κ')
  _ -> Nothing

code = Prism (const Code) $ \case
  Code -> Just ()
  _ -> Nothing

datax = Prism (const Data) $ \case
  Data -> Just ()
  _ -> Nothing

imaginary = Prism (const Imaginary) $ \case
  Imaginary -> Just ()
  _ -> Nothing

real = Prism Real $ \case
  (Real κ) -> Just κ
  _ -> Nothing

meta = Prism (const Meta) $ \case
  Meta -> Just ()
  _ -> Nothing

text = Prism (const Text) $ \case
  Text -> Just ()
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

signed = (kindSignedness .) $
  Prism (const Signed) $ \case
    Signed -> Just ()
    _ -> Nothing

unsigend = (kindSignedness .) $
  Prism (const Unsigned) $ \case
    Unsigned -> Just ()
    _ -> Nothing

traverseKindF ::
  Applicative m =>
  (v -> m v') ->
  (κ -> m κ') ->
  KindF v κ ->
  m (KindF v' κ')
traverseKindF f g κ = case κ of
  KindVariable x -> pure KindVariable <*> pure x
  KindExtra v -> pure KindExtra <*> f v
  Type κ -> pure Type <*> g κ
  Evidence -> pure Evidence
  Region -> pure Region
  Runtime κ κ' -> pure Runtime <*> g κ <*> g κ'
  Code -> pure Code
  Data -> pure Data
  Imaginary -> pure Imaginary
  Real κ -> pure Real <*> g κ
  Meta -> pure Meta
  Text -> pure Text
  KindRuntime PointerRep -> KindRuntime <$> (pure PointerRep)
  KindRuntime (StructRep κs) -> KindRuntime <$> (pure StructRep <*> traverse g κs)
  KindRuntime (WordRep κ) -> KindRuntime <$> (pure WordRep <*> g κ)
  (KindSize κ) -> pure (KindSize κ)
  (KindSignedness κ) -> pure (KindSignedness κ)

foldKindF f g = getConst . traverseKindF (Const . f) (Const . g)

mapKindF f g = runIdentity . traverseKindF (Identity . f) (Identity . g)

traverseKind :: Applicative m => (v -> m v') -> (p -> m p') -> Kind v p -> m (Kind v' p')
traverseKind f g (CoreKind p κ) =
  pure CoreKind <*> g p <*> traverseKindF f (traverseKind f g) κ

mapKind f g = runIdentity . traverseKind (Identity . f) (Identity . g)

instance Functor (Kind v) where
  fmap f = runIdentity . traverseKind pure (Identity . f)

instance Semigroup p => FreeVariables KindIdentifier p (Kind vκ p) where
  freeVariables (CoreKind p (KindVariable x)) = Map.singleton x p
  freeVariables (CoreKind _ κ) = foldKindF mempty freeVariables κ

instance Convert KindIdentifier (Kind v p) where
  convert ux x (CoreKind p (KindVariable x')) | x == x' = CoreKind p (KindVariable ux)
  convert ux x (CoreKind p κ) = CoreKind p $ mapKindF id go κ
    where
      go = convert ux x

instance Substitute (Kind v p) KindIdentifier (Kind v p) where
  substitute ux x (CoreKind _ (KindVariable x')) | x == x' = ux
  substitute ux x (CoreKind p κ) = CoreKind p $ mapKindF id go κ
    where
      go = substitute ux x

instance FreeVariablesInternal KindIdentifier (Kind v p) where
  freeVariablesInternal = freeVariables . fmap (const Internal)

instance Reduce (Kind v p) where
  reduce = id

instance Location (Kind v) where
  location (CoreKind p _) = p
