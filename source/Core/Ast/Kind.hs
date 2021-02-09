module Core.Ast.Kind where

import Core.Ast.Common
import Core.Ast.KindPattern
import Core.Ast.Sort
import qualified Data.Set as Set
import Misc.Identifier
import qualified TypeSystem.Function as TypeSystem
import qualified TypeSystem.Meta as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.Runtime as TypeSystem
import qualified TypeSystem.Type as TypeSystem
import qualified TypeSystem.Variable as TypeSystem

data Representation = FunctionRep | PointerRep deriving (Show)

data KindF p
  = KindVariable Identifier
  | Type (Kind p)
  | Higher (Kind p) (Kind p)
  | Runtime (Kind p)
  | Meta
  | RepresentationLiteral Representation
  deriving (Show, Functor)

data Kind p = CoreKind p (KindF p) deriving (Show, Functor)

type KindInternal = Kind Internal

projectKind ::
  KindF p ->
  Either
    (TypeSystem.Variable (Kind p))
    ( Either
        (TypeSystem.Type Sort (Kind p))
        ( Either
            (TypeSystem.Function () (Kind p))
            ( Either
                (TypeSystem.Runtime Sort (Kind p))
                ( Either TypeSystem.Meta Representation
                )
            )
        )
    )
projectKind (KindVariable x) = Left $ TypeSystem.Variable x
projectKind (Type s) = Right $ Left $ TypeSystem.Type s
projectKind (Higher κ κ') = Right $ Right $ Left $ TypeSystem.Function κ κ'
projectKind (Runtime κ) = Right $ Right $ Right $ Left $ TypeSystem.Runtime κ
projectKind Meta = Right $ Right $ Right $ Right $ Left $ TypeSystem.Meta
projectKind (RepresentationLiteral ρ) = Right $ Right $ Right $ Right $ Right $ ρ

instance TypeSystem.EmbedVariable KindInternal where
  variable x = CoreKind Internal $ KindVariable x

instance TypeSystem.EmbedType KindInternal KindInternal where
  typex s = CoreKind Internal $ Type s

instance TypeSystem.EmbedFunction KindInternal where
  function κ κ' = CoreKind Internal $ Higher κ κ'

instance TypeSystem.EmbedRuntime KindInternal KindInternal where
  runtime κ = CoreKind Internal $ Runtime κ

instance TypeSystem.EmbedMeta KindInternal where
  meta = CoreKind Internal $ Meta

instance FreeVariables KindInternal KindInternal where
  freeVariables (CoreKind Internal κ) = freeVariables @KindInternal $ projectKind κ

instance FreeVariables KindInternal (TypeSystem.Variable KindInternal) where
  freeVariables (TypeSystem.Variable x) = Set.singleton x

instance FreeVariables KindInternal Representation where
  freeVariables _ = Set.empty

instance Substitute KindInternal KindInternal where
  substitute κx x (CoreKind Internal κ) = substituteImpl κx x $ projectKind κ

instance SubstituteImpl (TypeSystem.Variable KindInternal) KindInternal KindInternal where
  substituteImpl κx x (TypeSystem.Variable x') | x == x' = κx
  substituteImpl _ _ (TypeSystem.Variable x) = CoreKind Internal $ KindVariable x

instance SubstituteImpl Representation KindInternal KindInternal where
  substituteImpl _ _ ρ = CoreKind Internal $ RepresentationLiteral ρ

instance Substitute KindInternal KindPatternInternal where
  substitute _ _ pm = pm

instance ModifyVariables KindInternal KindPatternInternal where
  modifyVariables (CoreKindPattern Internal pm) free = foldr Set.delete free $ bindings (projectKindPattern pm)

instance Reduce KindInternal where
  reduce = id

instance Positioned (Kind p) p where
  location (CoreKind p _) = p
