module Core.Ast.Kind where

import Core.Ast.Common
import Core.Ast.KindPattern
import Data.Bifunctor (bimap)
import Data.Functor.Identity (Identity (..), runIdentity)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import Misc.Prism
import Misc.Variables as Variables

data KindF p
  = KindVariable Identifier
  | Type (Kind p)
  | Higher (Kind p) (Kind p)
  | Poly (Bound (KindPattern p) (Kind p))
  | Constraint
  | Region
  | Runtime (Kind p) (Kind p)
  | Code
  | Data
  | Imaginary
  | Real (Kind p)
  | Meta
  | Text
  | PointerRep
  | StructRep [Kind p]
  deriving (Show)

kindp =
  assumeIsomorph $
    kindVariable
      `branch` typex
      `branch` higher
      `branch` poly
      `branch` constraint
      `branch` region
      `branch` runtime
      `branch` code
      `branch` datax
      `branch` imaginary
      `branch` real
      `branch` meta
      `branch` text
      `branch` pointerRep
      `branch` structRep

instance Functor KindF where
  fmap f = runIdentity . traverseKindF (Identity . fmap f) (Identity . bimap (fmap f) (fmap f))
    where
      traverseKindF kind bound = go
        where
          go (KindVariable x) = pure KindVariable <*> pure x
          go (Type κ) = pure Type <*> kind κ
          go (Higher κ κ') = pure Higher <*> kind κ <*> kind κ'
          go (Poly λ) = pure Poly <*> bound λ
          go Constraint = pure Constraint
          go Region = pure Region
          go (Runtime κ κ') = pure Runtime <*> kind κ <*> kind κ'
          go Code = pure Code
          go Data = pure Data
          go Imaginary = pure Imaginary
          go (Real κ) = pure Real <*> kind κ
          go Meta = pure Meta
          go Text = pure Text
          go PointerRep = pure PointerRep
          go (StructRep ρs) = pure StructRep <*> traverse kind ρs

mapKind f (CoreKind p κ) = CoreKind p (to $ f $ from κ)
  where
    (Isomorph to from) = kindp

foldKind f (CoreKind _ κ) = f $ from κ
  where
    (Isomorph _ from) = kindp

kindVariable = Prism KindVariable $ \case
  (KindVariable x) -> Just x
  _ -> Nothing

typex = Prism Type $ \case
  (Type κ) -> Just κ
  _ -> Nothing

higher = Prism (uncurry Higher) $ \case
  (Higher κ κ') -> Just (κ, κ')
  _ -> Nothing

poly = Prism Poly $ \case
  (Poly λ) -> Just λ
  _ -> Nothing

constraint = Prism (const Constraint) $ \case
  Constraint -> Just ()
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

pointerRep = Prism (const PointerRep) $ \case
  PointerRep -> Just ()
  _ -> Nothing

structRep = Prism StructRep $ \case
  (StructRep ρs) -> Just ρs
  _ -> Nothing

data Kind p = CoreKind p (KindF p) deriving (Show, Functor)

coreKind = Isomorph (uncurry CoreKind) $ \(CoreKind p κ) -> (p, κ)

type KindInternal = Kind Internal

avoidCaptureKind ::
  forall p pm e u.
  (Algebra (Kind p) p e, Algebra (Kind p) p u, Binder p pm) =>
  u ->
  Bound pm e ->
  Bound pm e
avoidCaptureKind = avoidCapture @(Kind p)

avoidCaptureKindConvert ::
  forall p pm e.
  (Algebra (Kind p) p e, Binder p pm) =>
  Identifier ->
  Bound pm e ->
  Bound pm e
avoidCaptureKindConvert = avoidCaptureGeneral internalVariable (convert @(Kind p))

instance Semigroup p => Algebra (Kind p) p (Kind p) where
  freeVariables (CoreKind p (KindVariable x)) = Variables.singleton x p
  freeVariables κ = foldKind (freeVariables @(Kind p)) κ
  substitute ux x (CoreKind _ (KindVariable x')) | x == x' = ux
  substitute ux x κ = mapKind (substitute ux x) κ
  convert ix x (CoreKind p (KindVariable x')) | x == x' = CoreKind p (KindVariable ix)
  convert ix x κ = mapKind (convert @(Kind p) ix x) κ

instance Algebra (Kind p) p u => Algebra (Kind p) p (Bound (KindPattern p) u) where
  freeVariables (Bound pm σ) = removeBinds (freeVariables @(Kind p) σ) (bindings pm)
  substitute = substituteSame substitute avoidCaptureKind
  convert = substituteSame (convert @(Kind p)) (avoidCaptureKindConvert)

instance Reduce (Kind p) where
  reduce = id

instance Apply (Bound KindPatternInternal KindInternal) KindInternal KindInternal where
  apply (Bound (CoreKindPattern _ (KindPatternVariable x _)) κ) κ' = reduce $ substitute κ' x κ

instance Location Kind where
  location (CoreKind p _) = p
