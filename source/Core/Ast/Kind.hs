module Core.Ast.Kind where

import Core.Ast.Common
import Core.Ast.Multiplicity
import Core.Ast.Stage
import qualified Data.Set as Set
import qualified TypeSystem.Function as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.Type as TypeSystem

data KindF p = Type (Stage p) | Higher (Kind p) (Kind p) deriving (Show, Functor)

data Kind p = CoreKind p (KindF p) deriving (Show, Functor)

type KindInternal = Kind Internal

data KindSort = Kind deriving (Show)

instance TypeSystem.EmbedType KindInternal StageInternal where
  typex s = CoreKind Internal $ Type s

instance TypeSystem.EmbedFunction KindInternal where
  function κ κ' = CoreKind Internal $ Higher κ κ'

instance FreeVariables KindInternal MultiplicityInternal where
  freeVariables' _ = Set.empty

instance Substitute MultiplicityInternal KindInternal where
  substitute _ _ κ = κ

instance Reduce KindInternal where
  reduce = id

instance Positioned (Kind p) p where
  location (CoreKind p _) = p
