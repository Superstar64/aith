module C.Ast where

import Control.Category ((.))
import Data.Bifunctor (first, second)
import Misc.Isomorph
import Misc.Prism
import Prelude hiding (id, (.))

data Base
  = Void
  | Byte
  | Short
  | Int
  | Long
  | PtrDiff
  | UByte
  | UShort
  | UInt
  | ULong
  | Size
  | Struct Struct
  | Union Struct
  deriving (Show)

data Struct
  = Anonymous [Declaration]
  | StructDefinition String [Declaration]
  | StructUse String
  deriving (Show)

data Composite x
  = Pointer x
  | Function x [Declaration]
  deriving (Show)

data Type
  = Base Base
  | Composite (Composite Type)
  deriving (Show)

data Declaration = Declaration Type (Maybe String) deriving (Show)

data Initializer
  = Scalar Expression
  | Brace [Initializer]
  | Designator [(String, Initializer)]
  deriving (Show)

data Definition
  = FunctionBody [Statement]
  | Initializer Initializer
  | Uninitialized
  deriving (Show)

data Statement
  = Return Expression
  | Binding Declaration Definition
  | If Expression [Statement] [Statement]
  | DoWhile [Statement] Expression
  | Expression Expression
  deriving (Show)

data Expression
  = Variable String
  | Call Expression [Expression]
  | Member Expression String
  | Dereference Expression
  | Address Expression
  | IntegerLiteral Integer
  | Addition Expression Expression
  | Subtraction Expression Expression
  | Multiplication Expression Expression
  | Division Expression Expression
  | Equal Expression Expression
  | NotEqual Expression Expression
  | LessThen Expression Expression
  | LessThenEqual Expression Expression
  | GreaterThen Expression Expression
  | GreaterThenEqual Expression Expression
  | Assign Expression Expression
  deriving (Show)

data Declarator
  = Basic (Maybe String)
  | Complex (Composite Declarator)
  deriving (Show)

void = Prism (const Void) $ \case
  Void -> Just ()
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

ptrDiff = Prism (const PtrDiff) $ \case
  PtrDiff -> Just ()
  _ -> Nothing

ubyte = Prism (const UByte) $ \case
  UByte -> Just ()
  _ -> Nothing

ushort = Prism (const UShort) $ \case
  UShort -> Just ()
  _ -> Nothing

uint = Prism (const UInt) $ \case
  UInt -> Just ()
  _ -> Nothing

ulong = Prism (const ULong) $ \case
  ULong -> Just ()
  _ -> Nothing

size = Prism (const Size) $ \case
  Size -> Just ()
  _ -> Nothing

pointer = Prism Pointer $ \case
  Pointer σ -> Just σ
  _ -> Nothing

struct = Prism (Struct) $ \case
  (Struct body) -> Just body
  _ -> Nothing

union = Prism (Union) $ \case
  (Union body) -> Just body
  _ -> Nothing

anonymous = Prism Anonymous $ \case
  Anonymous body -> Just body
  _ -> Nothing

structDefinition = Prism (uncurry StructDefinition) $ \case
  StructDefinition name body -> Just (name, body)
  _ -> Nothing

structUse = Prism StructUse $ \case
  StructUse name -> Just name
  _ -> Nothing

scalar = Prism Scalar $ \case
  Scalar expr -> Just expr
  _ -> Nothing

brace = Prism Brace $ \case
  Brace expr -> Just expr
  _ -> Nothing

designator = Prism Designator $ \case
  Designator expr -> Just expr
  _ -> Nothing

functionBody = Prism FunctionBody $ \case
  FunctionBody body -> Just body
  _ -> Nothing

initializer = Prism Initializer $ \case
  Initializer init -> Just init
  _ -> Nothing

uninitialized = Prism (const Uninitialized) $ \case
  Uninitialized -> Just ()
  _ -> Nothing

function = Prism (uncurry Function) $ \case
  Function e a -> Just (e, a)
  _ -> Nothing

returnx = Prism Return $ \case
  Return e -> Just e
  _ -> Nothing

binding = Prism (uncurry Binding) $ \case
  Binding decl init -> Just (decl, init)
  _ -> Nothing

ifx = Prism (uncurry $ uncurry If) $ \case
  If bool true false -> Just ((bool, true), false)
  _ -> Nothing

doWhile = Prism (uncurry DoWhile) $ \case
  DoWhile run check -> Just (run, check)
  _ -> Nothing

expression = Prism Expression $ \case
  Expression expr -> Just expr
  _ -> Nothing

variable = Prism Variable $ \case
  (Variable x) -> Just x
  _ -> Nothing

call = Prism (uncurry $ Call) $ \case
  (Call function arguments) -> Just (function, arguments)
  _ -> Nothing

member = Prism (uncurry $ Member) $ \case
  (Member value name) -> Just (value, name)
  _ -> Nothing

dereference = Prism Dereference $ \case
  (Dereference pointer) -> Just pointer
  _ -> Nothing

address = Prism Address $ \case
  (Address value) -> Just value
  _ -> Nothing

integerLiteral = Prism IntegerLiteral $ \case
  (IntegerLiteral n) -> Just n
  _ -> Nothing

addition = Prism (uncurry Addition) $ \case
  Addition e e' -> Just (e, e')
  _ -> Nothing

subtraction = Prism (uncurry Subtraction) $ \case
  Subtraction e e' -> Just (e, e')
  _ -> Nothing

multiplication = Prism (uncurry Multiplication) $ \case
  Multiplication e e' -> Just (e, e')
  _ -> Nothing

division = Prism (uncurry Division) $ \case
  Division e e' -> Just (e, e')
  _ -> Nothing

equal = Prism (uncurry Equal) $ \case
  Equal e e' -> Just (e, e')
  _ -> Nothing

notEqual = Prism (uncurry NotEqual) $ \case
  NotEqual e e' -> Just (e, e')
  _ -> Nothing

lessThen = Prism (uncurry LessThen) $ \case
  LessThen e e' -> Just (e, e')
  _ -> Nothing

lessThenEqual = Prism (uncurry LessThenEqual) $ \case
  LessThenEqual e e' -> Just (e, e')
  _ -> Nothing

greaterThen = Prism (uncurry GreaterThen) $ \case
  GreaterThen e e' -> Just (e, e')
  _ -> Nothing

greaterThenEqual = Prism (uncurry GreaterThenEqual) $ \case
  GreaterThenEqual e e' -> Just (e, e')
  _ -> Nothing

assign = Prism (uncurry Assign) $ \case
  Assign e e' -> Just (e, e')
  _ -> Nothing

basic = Prism Basic $ \case
  Basic x -> Just x
  _ -> Nothing

complex = Prism Complex $ \case
  Complex e -> Just e
  _ -> Nothing

declaration :: Isomorph (Base, Declarator) Declaration
declaration = Isomorph join split . secondI (inverse slot . firstI reverseI . slot)
  where
    join (base, Basic name) = Declaration (Base base) name
    join (base, Complex (Pointer decl)) =
      Declaration (Composite $ Pointer typex) name
      where
        Declaration typex name = join (base, decl)
    join (base, Complex (Function decl arguments)) =
      Declaration (Composite $ Function typex arguments) name
      where
        Declaration typex name = join (base, decl)
    split (Declaration (Base typex) name) = (typex, Basic name)
    split (Declaration (Composite (Pointer typex)) name) =
      second (Complex . Pointer) $ split (Declaration typex name)
    split (Declaration (Composite (Function typex arguments)) name) =
      second (Complex . flip Function arguments) $ split (Declaration typex name)

    reverseI = Isomorph reverse reverse

    slot :: Isomorph Declarator ([Composite ()], Maybe String)
    slot = Isomorph split join
      where
        split (Basic name) = ([], name)
        split (Complex (Pointer decl)) =
          first (Pointer () :) $ split decl
        split (Complex (Function decl arguments)) =
          first (Function () arguments :) $ split decl
        join ([], name) = Basic name
        join (Pointer () : decls, name) =
          Complex $ Pointer $ join (decls, name)
        join (Function () arguments : decls, name) =
          Complex $ Function (join (decls, name)) arguments
