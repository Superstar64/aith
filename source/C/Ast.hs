module C.Ast where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (evalStateT, get, modify)
import Control.Monad.Trans.Writer.Strict (runWriter, tell)
import qualified Data.Set as Set
import Misc.Prism

data Representation x = Pointer | Struct x | Byte | Short | Int | Long deriving (Show, Eq, Ord)

pointer = Prism (const Pointer) $ \case
  Pointer -> Just ()
  _ -> Nothing

struct = Prism Struct $ \case
  (Struct x) -> Just x
  _ -> Nothing

byte = Prism (const Byte) $ \case
  Byte -> Just ()
  _ -> Nothing

short = Prism (const Short) $ \case
  Short -> Just ()
  _ -> Nothing

int = Prism (const Int) $ \case
  Int -> Just ()
  _ -> Nothing

long = Prism (const Long) $ \case
  Long -> Just ()
  _ -> Nothing

data Sign = Signed | Unsigned deriving (Show)

signed = Prism (const Signed) $ \case
  Signed -> Just ()
  _ -> Nothing

unsigned = Prism (const Unsigned) $ \case
  Unsigned -> Just ()
  _ -> Nothing

data RepresentationFix = RepresentationFix ([Representation RepresentationFix]) deriving (Show, Eq, Ord)

mangleType Pointer = "p"
mangleType (Struct (RepresentationFix items)) = "s" ++ (items >>= mangleType) ++ "e"
mangleType Byte = "b"
mangleType Short = "w"
mangleType Int = "i"
mangleType Long = "l"

fields = map (\x -> '_' : show x) [0 ..]

escapeStruct Pointer = pure Pointer
escapeStruct (Struct (RepresentationFix items)) = do
  let mangling = "s" ++ (items >>= mangleType) ++ "e"
  solved <- get
  if items `Set.notMember` solved
    then do
      modify $ Set.insert items
      items' <- traverse escapeStruct items
      lift $ tell [StructDefinition mangling (zip items' fields)]
    else pure ()
  pure $ Struct $ mangling
escapeStruct Byte = pure Byte
escapeStruct Short = pure Short
escapeStruct Int = pure Int
escapeStruct Long = pure Long

escapeStructs :: [Global (Representation RepresentationFix)] -> ([Global (Representation String)], [Global (Representation String)])
escapeStructs x = runWriter $ evalStateT (traverse (traverse escapeStruct) x) (Set.empty)

data Global x
  = FunctionDefinition x String [(x, String)] [Statement x]
  | StructDefinition String [(x, String)]
  deriving (Show, Functor, Foldable, Traversable)

functionDefinition = Prism (uncurry $ uncurry $ uncurry $ FunctionDefinition) $ \case
  (FunctionDefinition returnType name arguments text) -> Just (((returnType, name), arguments), text)
  _ -> Nothing

structDefinition = Prism (uncurry StructDefinition) $ \case
  (StructDefinition name items) -> Just (name, items)
  _ -> Nothing

data Statement x
  = Return (Expression x)
  | ForwardDeclare x String [x]
  | VariableDeclaration x String (Expression x)
  deriving (Show, Functor, Foldable, Traversable)

returnx = Prism Return $ \case
  (Return e) -> Just e
  _ -> Nothing

forwardDeclare = Prism (uncurry $ uncurry $ ForwardDeclare) $ \case
  (ForwardDeclare returnType name argumentTypes) -> Just ((returnType, name), argumentTypes)
  _ -> Nothing

variableDeclation = Prism (uncurry $ uncurry $ VariableDeclaration) $ \case
  (VariableDeclaration variableType name value) -> Just ((variableType, name), value)
  _ -> Nothing

data Expression x
  = Variable String
  | Call x [x] (Expression x) [Expression x]
  | CompoundLiteral x [Expression x]
  | Member (Expression x) String
  | Dereference x (Expression x)
  | Address (Expression x)
  | IntegerLiteral Integer
  | Addition (Sign, x) (Expression x) (Sign, x) (Expression x)
  | Subtraction (Sign, x) (Expression x) (Sign, x) (Expression x)
  | Multiplication (Sign, x) (Expression x) (Sign, x) (Expression x)
  | Division (Sign, x) (Expression x) (Sign, x) (Expression x)
  deriving (Show, Functor, Foldable, Traversable)

variable = Prism Variable $ \case
  (Variable x) -> Just x
  _ -> Nothing

call = Prism (uncurry $ uncurry $ uncurry $ Call) $ \case
  (Call returnType argumentTypes function arguments) -> Just (((returnType, argumentTypes), function), arguments)
  _ -> Nothing

compoundLiteral = Prism (uncurry $ CompoundLiteral) $ \case
  (CompoundLiteral typex items) -> Just (typex, items)
  _ -> Nothing

member = Prism (uncurry $ Member) $ \case
  (Member value name) -> Just (value, name)
  _ -> Nothing

dereference = Prism (uncurry $ Dereference) $ \case
  (Dereference pointer value) -> Just (pointer, value)
  _ -> Nothing

address = Prism Address $ \case
  (Address value) -> Just value
  _ -> Nothing

integerLiteral = Prism IntegerLiteral $ \case
  (IntegerLiteral n) -> Just n
  _ -> Nothing

addition = Prism (uncurry $ uncurry $ uncurry Addition) $ \case
  Addition x e x' e' -> Just (((x, e), x'), e')
  _ -> Nothing

subtraction = Prism (uncurry $ uncurry $ uncurry Subtraction) $ \case
  Subtraction x e x' e' -> Just (((x, e), x'), e')
  _ -> Nothing

multiplication = Prism (uncurry $ uncurry $ uncurry Multiplication) $ \case
  Multiplication x e x' e' -> Just (((x, e), x'), e')
  _ -> Nothing

division = Prism (uncurry $ uncurry $ uncurry Division) $ \case
  Division x e x' e' -> Just (((x, e), x'), e')
  _ -> Nothing
