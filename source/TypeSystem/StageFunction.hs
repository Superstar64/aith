module TypeSystem.StageFunction where

class EmbedStageFunction s where
  stageFunction :: s -> s -> s
