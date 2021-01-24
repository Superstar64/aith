module Core.Ast.Sort where

import qualified TypeSystem.Kind as TypeSystem
import qualified TypeSystem.Pattern as TypeSystem
import qualified TypeSystem.Stage as TypeSystem
import qualified TypeSystem.Type as TypeSystem

data StageSort = Stage deriving (Show)

instance TypeSystem.EmbedStage StageSort where
  stage = Stage

data KindSort = Kind deriving (Show)

instance TypeSystem.EmbedKind KindSort where
  kind = Kind

instance TypeSystem.EmbedType KindSort () where
  typex () = Kind

data PatternSort = Pattern

instance TypeSystem.EmbedPattern PatternSort where
  pattern = Pattern

data TypePatternSort = TypePattern

instance TypeSystem.EmbedPattern TypePatternSort where
  pattern = TypePattern
