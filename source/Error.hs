module Error where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (StateT)
import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Sort
import Core.Ast.Type
import Data.Functor.Identity (Identity)
import Misc.Identifier (Identifier)
import Misc.Path

data LookupError p
  = IllegalPath p Path
  | IncompletePath p Path
  | IndexingGlobal p Path
  | Cycle p Path
  deriving (Show)

data Error p
  = UnknownIdentfier p Identifier
  | ExpectedMacro p TypeInternal
  | ExpectedFunctionPointer p TypeInternal
  | ExpectedForall p TypeInternal
  | ExpectedKindForall p TypeInternal
  | ExpectedQualified p TypeInternal
  | ExpectedOfCourse p TypeInternal
  | ExpectedRecursive p TypeInternal
  | ExpectedRegionTransformer p TypeInternal
  | ExpectedRegionReference p TypeInternal
  | ExpectedType p KindInternal
  | ExpectedHigher p KindInternal
  | ExpectedPoly p KindInternal
  | ExpectedConstraint p KindInternal
  | ExpectedRegion p KindInternal
  | ExpectedText p KindInternal
  | ExpectedRuntime p KindInternal
  | ExpectedData p KindInternal
  | ExpectedReal p KindInternal
  | ExpectedKind p Sort
  | ExpectedStage p Sort
  | ExpectedImpact p Sort
  | ExpectedExistance p Sort
  | ExpectedRepresentation p Sort
  | EscapingTypeVariable p Identifier TypeInternal
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

instance Base p m => Base p (StateT s m) where
  quit error = lift (quit error)
  moduleQuit error = lift (moduleQuit error)

instance Base Internal Identity where
  quit e = error $ "" ++ show e
  moduleQuit e = error $ "" ++ show e

instance Base Internal Maybe where
  quit _ = Nothing
  moduleQuit _ = Nothing
