module TypeSystem.StageOfCourse where

class EmbedStageOfCourse s where
  stageOfCourse :: s -> s
