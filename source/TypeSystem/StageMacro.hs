module TypeSystem.StageMacro where

data StageMacro s = StageMacro s s deriving (Show, Functor, Foldable, Traversable)

class EmbedStageMacro s where
  stageMacro' :: StageMacro s -> s

stageMacro s s' = stageMacro' $ StageMacro s s'
