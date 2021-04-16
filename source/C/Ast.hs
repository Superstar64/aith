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

data FunctionDefinition x = FunctionDefinition Representation x [(Representation, x)] [Statement x] deriving (Show)

functionDefinition = Isomorph (uncurry $ uncurry $ uncurry $ FunctionDefinition) $ f
  where
    f (FunctionDefinition returnType name arguments text) = (((returnType, name), arguments), text)

data Statement x = Return (Expression x) | ForwardDeclare Representation x [Representation] deriving (Show)

returnx = Prism Return $ \case
  (Return e) -> Just e
  _ -> Nothing

forwardDeclare = Prism (uncurry $ uncurry $ ForwardDeclare) $ \case
  (ForwardDeclare returnType name argumentTypes) -> Just ((returnType, name), argumentTypes)
  _ -> Nothing

data Expression x = Variable x | Call Representation [Representation] (Expression x) [Expression x] deriving (Show)

variable = Prism Variable $ \case
  (Variable x) -> Just x
  _ -> Nothing

call = Prism (uncurry $ uncurry $ uncurry $ Call) $ \case
  (Call returnType argumentTypes function arguments) -> Just (((returnType, argumentTypes), function), arguments)
  _ -> Nothing
