module C.Ast where

import Misc.Isomorph
import Misc.Prism

data Representation = Pointer | Function deriving (Show)

pointer = Prism (const Pointer) $ \case
  Pointer -> Just ()
  _ -> Nothing

function = Prism (const Function) $ \case
  Function -> Just ()
  _ -> Nothing

data FunctionDefinition = FunctionDefinition Representation String [(Representation, String)] [Statement] deriving (Show)

functionDefinition = Isomorph (uncurry $ uncurry $ uncurry $ FunctionDefinition) $ f
  where
    f (FunctionDefinition returnType name arguments text) = (((returnType, name), arguments), text)

data Statement = Return (Expression) | ForwardDeclare Representation String [Representation] deriving (Show)

returnx = Prism Return $ \case
  (Return e) -> Just e
  _ -> Nothing

forwardDeclare = Prism (uncurry $ uncurry $ ForwardDeclare) $ \case
  (ForwardDeclare returnType name argumentTypes) -> Just ((returnType, name), argumentTypes)
  _ -> Nothing

data Expression = Variable String | Call Representation [Representation] (Expression) [Expression] deriving (Show)

variable = Prism Variable $ \case
  (Variable x) -> Just x
  _ -> Nothing

call = Prism (uncurry $ uncurry $ uncurry $ Call) $ \case
  (Call returnType argumentTypes function arguments) -> Just (((returnType, argumentTypes), function), arguments)
  _ -> Nothing
