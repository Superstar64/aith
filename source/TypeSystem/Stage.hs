module TypeSystem.Stage where

data Stage = Stage

class EmbedStage μs where
  stage :: μs

class CheckStage μs p m where
  checkStage :: p -> μs -> m Stage
