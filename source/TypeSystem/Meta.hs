module TypeSystem.Meta where

import qualified Data.Set as Set
import TypeSystem.Methods
import TypeSystem.Stage

data Meta = Meta

class EmbedMeta s where
  meta :: s

instance EmbedMeta () where
  meta = ()

instance (Monad m, EmbedStage ss) => TypeCheckImpl m p Meta ss where
  typeCheckImpl _ Meta = pure $ stage

instance FreeVariables u Meta where
  freeVariables Meta = Set.empty

instance EmbedMeta s => SubstituteImpl Meta u s where
  substituteImpl _ _ Meta = meta
