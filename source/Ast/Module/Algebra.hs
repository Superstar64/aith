module Ast.Module.Algebra where

data GlobalF σ ς e
  = Inline e
  | Text e
  | Synonym σ
  | NewType σ
  | ForwardNewType σ
  | ForwardText ς
  deriving (Show)
