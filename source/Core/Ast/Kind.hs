module Core.Ast.Kind where

import Core.Ast.Common
import Core.Ast.Sort
import Core.Ast.Stage
import qualified TypeSystem.Function as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.Type as TypeSystem

data KindF p = Type (Stage p) | Higher (Kind p) (Kind p) deriving (Show, Functor)

data Kind p = CoreKind p (KindF p) deriving (Show, Functor)

type KindInternal = Kind Internal

projectKind :: KindF p -> Either (TypeSystem.Type StageSort (Stage p)) (TypeSystem.Function () (Kind p))
projectKind (Type s) = Left $ TypeSystem.Type s
projectKind (Higher κ κ') = Right $ TypeSystem.Function κ κ'

instance TypeSystem.EmbedType KindInternal StageInternal where
  typex s = CoreKind Internal $ Type s

instance TypeSystem.EmbedFunction KindInternal where
  function κ κ' = CoreKind Internal $ Higher κ κ'

instance FreeVariables StageInternal KindInternal where
  freeVariables (CoreKind Internal κ) = freeVariables @StageInternal $ projectKind κ

instance Substitute StageInternal KindInternal where
  substitute sx x (CoreKind Internal κ) = substituteImpl sx x $ projectKind κ

instance Reduce KindInternal where
  reduce = id

instance Positioned (Kind p) p where
  location (CoreKind p _) = p
