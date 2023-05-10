module Ast.Type.Runtime where

data KindSize
  = Byte
  | Short
  | Int
  | Long
  | Native
  deriving (Show, Eq, Ord)

data KindSignedness
  = Signed
  | Unsigned
  deriving (Show, Eq, Ord)

data KindRuntime s κ
  = PointerRep
  | StructRep [κ]
  | UnionRep [κ]
  | WordRep s
  deriving (Show, Eq, Ord)
