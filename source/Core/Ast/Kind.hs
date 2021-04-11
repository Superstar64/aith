module Core.Ast.Kind where

import Core.Ast.Common
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
  | PointerRep
  | FunctionRep
  deriving (Show, Functor)

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

pointerRep = Prism (const PointerRep) $ \case
  PointerRep -> Just ()
  _ -> Nothing

functionRep = Prism (const FunctionRep) $ \case
  FunctionRep -> Just ()
  _ -> Nothing

data Kind p = CoreKind p (KindF p) deriving (Show, Functor)

coreKind = Isomorph (uncurry CoreKind) $ \(CoreKind p κ) -> (p, κ)

type KindInternal = Kind Internal

freeVariablesKindImpl :: forall u p. (Semigroup p, FreeVariables u p (Kind p)) => KindF p -> Variables p
freeVariablesKindImpl (KindVariable _) = mempty
freeVariablesKindImpl (Type κ) = freeVariables @u κ
freeVariablesKindImpl (Higher κ κ') = freeVariables @u κ <> freeVariables @u κ'
freeVariablesKindImpl (Runtime κ) = freeVariables @u κ
freeVariablesKindImpl Meta = mempty
freeVariablesKindImpl PointerRep = mempty
freeVariablesKindImpl FunctionRep = mempty

instance Semigroup p => FreeVariables (Kind p) p (Kind p) where
  freeVariables (CoreKind p (KindVariable x)) = Variables.singleton x p
  freeVariables (CoreKind _ κ) = freeVariablesKindImpl @(Kind p) κ

substituteKindImpl :: Substitute u KindInternal => u -> Identifier -> KindF Internal -> KindF Internal
substituteKindImpl _ _ (KindVariable x) = KindVariable x
substituteKindImpl ux x (Type κ) = Type (substitute ux x κ)
substituteKindImpl ux x (Higher κ κ') = Higher (substitute ux x κ) (substitute ux x κ')
substituteKindImpl ux x (Runtime κ) = Runtime (substitute ux x κ)
substituteKindImpl _ _ Meta = Meta
substituteKindImpl _ _ PointerRep = PointerRep
substituteKindImpl _ _ FunctionRep = FunctionRep

instance Substitute KindInternal KindInternal where
  substitute ux x (CoreKind Internal κ) = CoreKind Internal $ substituteKindImpl ux x κ

avoidCaptureKind = avoidCapture (CoreKind Internal . KindVariable) (freeVariablesInternal @KindInternal)

instance Reduce KindInternal where
  reduce = id

instance Location Kind where
  location (CoreKind p _) = p
