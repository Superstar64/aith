module Error where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.Sort
import Core.Ast.Type
import Data.Functor.Identity (Identity)
import Misc.Identifier (Identifier)
import Misc.Path
import System.Exit (ExitCode (..), exitWith)

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
  | ExpectedOfCourse p TypeInternal
  | ExpectedType p KindInternal
  | ExpectedHigher p KindInternal
  | ExpectedRuntime p KindInternal
  | ExpectedKind p Sort
  | ExpectedStage p Sort
  | ExpectedRepresentation p Sort
  | IncompatibleType p TypeInternal TypeInternal
  | IncompatibleKind p KindInternal KindInternal
  | IncompatibleLinear p MultiplicityInternal MultiplicityInternal
  | IncompatibleSort p Sort Sort
  | CaptureLinear p Identifier
  | InvalidUsage p Identifier
  deriving (Show)

class (Monad m, Semigroup p) => Base p m where
  quit :: Error p -> m a
  moduleQuit :: LookupError p -> m a

instance (Semigroup p, Show p) => Base p IO where
  quit error = do
    putStrLn "Error:"
    print error
    exitWith (ExitFailure 2)
  moduleQuit error = do
    putStrLn "Module Error:"
    print error
    exitWith (ExitFailure 3)

instance Base Internal Identity where
  quit e = error $ "" ++ show e
  moduleQuit e = error $ "" ++ show e
