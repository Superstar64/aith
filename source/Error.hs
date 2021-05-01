module Error where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Sort
import Core.Ast.Type
import Data.Functor.Identity (Identity)
import Misc.Identifier (Identifier)
import Misc.Path
import System.Exit (die)

data LookupError p
  = IllegalPath p Path
  | IncompletePath p Path
  | IndexingGlobal p Path
  | Cycle p Path
  deriving (Show)

data Error p
  = UnknownIdentfier p Identifier
  | ExpectedMacro p TypeInternal
  | ExpectedFunctionPointer p Int TypeInternal
  | ExpectedForall p TypeInternal
  | ExpectedKindForall p TypeInternal
  | ExpectedErasedQualified p TypeInternal
  | ExpectedOfCourse p TypeInternal
  | ExpectedRecursive p TypeInternal
  | ExpectedType p KindInternal
  | ExpectedHigher p KindInternal
  | ExpectedPoly p KindInternal
  | ExpectedConstraint p KindInternal
  | ExpectedText p KindInternal
  | ExpectedRuntime p KindInternal
  | ExpectedKind p Sort
  | ExpectedStage p Sort
  | ExpectedRepresentation p Sort
  | IncompatibleType p TypeInternal TypeInternal
  | IncompatibleKind p KindInternal KindInternal
  | IncompatibleSort p Sort Sort
  | CaptureLinear p Identifier
  | InvalidUsage p Identifier
  | NoProof p TypeInternal
  deriving (Show)

class (Monad m, Semigroup p) => Base p m where
  quit :: Error p -> m a
  moduleQuit :: LookupError p -> m a

instance (Semigroup p, Show p) => Base p IO where
  quit error = die $ "Error:" ++ show error
  moduleQuit error = die $ "Module Error:" ++ show error

instance Base Internal Identity where
  quit e = error $ "" ++ show e
  moduleQuit e = error $ "" ++ show e

instance Base Internal Maybe where
  quit _ = Nothing
  moduleQuit _ = Nothing
