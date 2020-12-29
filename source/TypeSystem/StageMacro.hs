module TypeSystem.StageMacro where

class EmbedStageMacro s where
  stageMacro :: s -> s -> s
