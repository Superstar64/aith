module Core.Ast.Kind where

import Core.Ast.Common
import Core.Ast.KindPattern
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import Misc.Prism
import Misc.Variables as Variables

data KindF p
  = KindVariable Identifier
  | Type (Kind p)
  | Higher (Kind p) (Kind p)
  | Runtime (Kind p)
  | Meta
  | Text
  | PointerRep
  deriving (Show, Functor)

traverseKind kind = go
  where
    go (KindVariable x) = pure KindVariable <*> pure x
    go (Type κ) = pure Type <*> kind κ
    go (Higher κ κ') = pure Higher <*> kind κ <*> kind κ'
    go (Runtime κ) = pure Runtime <*> kind κ
    go Meta = pure Meta
    go Text = pure Text
    go PointerRep = pure PointerRep

mapKind kind κ = runIdentity $ traverseKind (Identity . kind) κ

foldKind kind κ = getConst $ traverseKind (Const . kind) κ

kindVariable = Prism KindVariable $ \case
  (KindVariable x) -> Just x
  _ -> Nothing

typex = Prism Type $ \case
  (Type κ) -> Just κ
  _ -> Nothing

higher = Prism (uncurry Higher) $ \case
  (Higher κ κ') -> Just (κ, κ')
  _ -> Nothing

runtime = Prism Runtime $ \case
  (Runtime κ) -> Just κ
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
  freeVariables (CoreKind _ κ) = foldKind (freeVariables @(Kind p)) κ
  substitute ux x (CoreKind _ (KindVariable x')) | x == x' = ux
  substitute ux x (CoreKind p κ) = CoreKind p $ mapKind (substitute ux x) κ
  convert ix x (CoreKind p (KindVariable x')) | x == x' = CoreKind p (KindVariable ix)
  convert ix x (CoreKind p κ) = CoreKind p $ mapKind (convert @(Kind p) ix x) κ

instance Algebra (Kind p) p u => Algebra (Kind p) p (Bound (KindPattern p) u) where
  freeVariables (Bound pm σ) = removeBinds (freeVariables @(Kind p) σ) (bindings pm)
  substitute = substituteSame substitute avoidCaptureKind
  convert = substituteSame (convert @(Kind p)) (avoidCaptureKindConvert)

instance Reduce (Kind p) where
  reduce = id

instance Location Kind where
  location (CoreKind p _) = p
