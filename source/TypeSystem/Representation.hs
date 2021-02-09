module TypeSystem.Representation where

data Representation = Representation

class EmbedRepresentation μr where
  representation :: μr

class CheckRepresentation μr p m where
  checkRepresentation :: p -> μr -> m Representation
