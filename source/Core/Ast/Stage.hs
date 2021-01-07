module Core.Ast.Stage where

import qualified TypeSystem.StageFunction as TypeSystem
import qualified TypeSystem.StageOfCourse as TypeSystem

data Stage = Runtime | StageMacro Stage Stage | StageOfCourse Stage deriving (Show)

instance TypeSystem.EmbedStageFunction Stage where
  stageFunction s s' = StageMacro s s'

instance TypeSystem.EmbedStageOfCourse Stage where
  stageOfCourse s = StageOfCourse s
