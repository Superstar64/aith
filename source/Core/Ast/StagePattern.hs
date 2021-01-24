module Core.Ast.StagePattern where

import Core.Ast.Common
import Core.Ast.Sort
import Misc.Identifier
import TypeSystem.Methods
import qualified TypeSystem.PatternVariable as TypeSystem

data StagePatternF p = StagePatternVariable Identifier deriving (Show, Functor)

data StagePattern p = CoreStagePattern p (StagePatternF p) deriving (Show, Functor)

type StagePatternInternal = StagePattern Internal

projectStagePattern :: StagePatternF p -> TypeSystem.PatternVariable () () StageSort
projectStagePattern (StagePatternVariable x) = TypeSystem.PatternVariable x Stage

instance Bindings StagePatternInternal where
  bindings (CoreStagePattern Internal pm) = bindings $ projectStagePattern pm

instance TypeSystem.EmbedPatternVariable StageSort StagePatternInternal where
  patternVariable x Stage = CoreStagePattern Internal $ StagePatternVariable x

instance ConvertPattern StagePatternInternal StagePatternInternal where
  convertPattern ix x (CoreStagePattern Internal pm) = convertPattern ix x $ projectStagePattern pm

instance Reduce StagePatternInternal where
  reduce = id

instance Strip (StagePattern p) StagePatternInternal where
  strip pm = Internal <$ pm
