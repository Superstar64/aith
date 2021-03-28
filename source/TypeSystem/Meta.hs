module TypeSystem.Meta where

import TypeSystem.Methods
import TypeSystem.Stage

data Meta = Meta

class EmbedMeta s where
  meta :: s

instance EmbedMeta () where
  meta = ()

instance (Monad m, EmbedStage ss) => TypeCheckImpl m p Meta ss where
  typeCheckImpl _ Meta = pure $ stage

instance Semigroup p => FreeVariablesImpl u p Meta where
  freeVariablesImpl _ Meta = mempty

instance EmbedMeta s => SubstituteImpl Meta u s where
  substituteImpl _ _ Meta = meta
