module Core.Ast.Stage where

import Core.Ast.Common
import qualified TypeSystem.StageFunction as TypeSystem
import qualified TypeSystem.StageOfCourse as TypeSystem

data StageF p = Runtime | StageMacro (Stage p) (Stage p) | StageOfCourse (Stage p) deriving (Functor, Show)

data Stage p = CoreStage p (StageF p) deriving (Functor, Show)

type StageInternal = Stage Internal

instance TypeSystem.EmbedStageFunction StageInternal where
  stageFunction s s' = CoreStage Internal $ StageMacro s s'

instance TypeSystem.EmbedStageOfCourse StageInternal where
  stageOfCourse s = CoreStage Internal $ StageOfCourse s
