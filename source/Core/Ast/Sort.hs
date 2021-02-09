module Core.Ast.Sort where

import qualified TypeSystem.Kind as TypeSystem
import qualified TypeSystem.Pattern as TypeSystem
import qualified TypeSystem.Stage as TypeSystem
import qualified TypeSystem.Type as TypeSystem

data Sort = Kind | Stage | Representation deriving (Show)

instance TypeSystem.EmbedStage Sort where
  stage = Stage

instance TypeSystem.EmbedKind Sort where
  kind = Kind

instance TypeSystem.EmbedType Sort () where
  typex () = Kind

data PatternSort = Pattern

instance TypeSystem.EmbedPattern PatternSort where
  pattern = Pattern

data TypePatternSort = TypePattern

instance TypeSystem.EmbedPattern TypePatternSort where
  pattern = TypePattern
