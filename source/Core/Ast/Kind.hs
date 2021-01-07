module Core.Ast.Kind where

import Core.Ast.Common
import Core.Ast.Multiplicity
import Core.Ast.Stage
import qualified Data.Set as Set
import qualified TypeSystem.Function as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.Type as TypeSystem

data KindF p = Type Stage | Higher (Kind p) (Kind p) deriving (Show, Functor)

data Kind p = CoreKind p (KindF p) deriving (Show, Functor)

type KindInternal = Kind Internal

data KindSort = Kind deriving (Show)

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedType (Kind i) Stage where
  typex s = CoreKind Internal $ Type s

instance (i ~ Internal) => TypeSystem.EmbedFunction (Kind i) where
  function κ κ' = CoreKind Internal $ Higher κ κ'

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Kind i) (Multiplicity i') where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => Substitute (Multiplicity i) (Kind i) where
  substitute _ _ κ = κ

instance (i ~ Internal) => Reduce (Kind i) where
  reduce = id

instance Positioned (Kind p) p where
  location (CoreKind p _) = p
