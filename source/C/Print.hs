module C.Print where

import qualified C.Ast as C
import Control.Applicative ((<|>))
import Control.Category ((.))
import Control.Monad (liftM2)
import Data.Maybe (fromJust)
import Misc.Isomorph
import Misc.Prism
import Misc.Syntax
import Prelude hiding (id, (.))

newtype Printer a = Printer (a -> Maybe String)

emit (Printer p) a = fromJust $ p a

instance SyntaxBase Printer where
  syntaxmap (Prism _ f) (Printer p) = Printer $ \b -> f b >>= p
  Printer p ⊗ Printer q = Printer $ \(x, y) -> liftM2 (++) (p x) (q y)
  Printer p ∥ Printer q = Printer $ \x -> (p x) <|> (q x)
  never = Printer $ const Nothing
  always = Printer $ \() -> Just $ ""

string op | elem op [";", "{", "}"] = Printer $ \() -> Just $ op ++ "\n"
string op = Printer $ \() -> Just $ op ++ " "

line = Printer $ \() -> Just $ "\n"

identifer = Printer $ \name -> Just $ name ++ " "

integer = Printer $ \n -> Just $ show n

betweenParens = between (string "(") (string ")")

commaSeperatedMany e = seperatedMany e (string ",")

semiMany e = many (e ≪ string ";")

betweenBraces = between (string "{") (string "}")

argumentList e = betweenParens (seperatedMany e (string ","))

preprocess x = line ≫ x ≪ line

-- todo readd this to structs so c files can be monoidal again
once name x = preprocess (string "#ifndef " ≫ name) ⊗ preprocess (string "#define " ≫ name ⊗ string " " ≫ name) ⊗ x ≪ preprocess (string "#endif")

header :: Printer ()
header = preprocess (string "#include <stdint.h>") ≫ preprocess (string "#include <stddef.h>")

variableDeclaration = just ⊣ identifer ∥ nothing ⊣ always

base =
  choice
    [ C.void ⊣ string "void",
      C.byte ⊣ string "int8_t",
      C.short ⊣ string "int16_t",
      C.int ⊣ string "int32_t",
      C.long ⊣ string "int64_t",
      C.ptrDiff ⊣ string "ptrdiff_t",
      C.ubyte ⊣ string "uint8_t",
      C.ushort ⊣ string "uint16_t",
      C.uint ⊣ string "uint32_t",
      C.ulong ⊣ string "uint64_t",
      C.size ⊣ string "size_t",
      C.struct ⊣ string "struct" ≫ struct,
      C.union ⊣ string "union" ≫ struct
    ]

declaration :: Printer C.Declaration
declaration = C.declaration ⊣ base ⊗ declarator

struct :: Printer C.Struct
struct = apply ⊣ (identifer ⊗ (fields ⊕ always)) ⊕ fields
  where
    apply = branch (branchDistribute C.structDefinition (C.structUse . toPrism unit')) C.anonymous
    fields = betweenBraces $ semiMany declaration

declarator :: Printer C.Declarator
declarator = declaratorPointer
  where
    declaratorPointer = foldrP (C.complex . C.pointer . toPrism unit) ⊣ many (string "*") ⊗ declaratorFunction
    declaratorFunction = foldlP apply ⊣ declaratorCore ⊗ many (betweenParens (commaSeperatedMany declaration))
      where
        apply = C.complex . C.function
    declaratorCore = C.basic ⊣ variableDeclaration ∥ betweenParens declarator

definition :: Printer C.Definition
definition =
  choice
    [ C.functionBody ⊣ statements,
      C.initializer ⊣ string "=" ≫ initializer,
      C.uninitialized ⊣ always
    ]

initializer =
  choice
    [ C.scalar ⊣ expression,
      C.brace ⊣ betweenBraces (commaSeperatedMany initializer),
      C.designator ⊣ betweenBraces (commaSeperatedMany (string "." ≫ identifer ≪ string "=" ⊗ initializer))
    ]

statement :: Printer C.Statement
statement =
  choice
    [ C.binding ⊣ declaration ⊗ definition ≪ string ";",
      C.returnx ⊣ string "return" ≫ expression ≪ string ";",
      C.ifx ⊣ string "if" ≫ betweenParens expression ⊗ statements ≪ string "else" ⊗ statements,
      C.doWhile ⊣ string "do" ≫ statements ⊗ string "while" ≫ betweenParens expression ≪ string ";",
      C.expression ⊣ expression ≪ string ";"
    ]

statements = betweenBraces $ many statement

expression :: Printer C.Expression
expression = assignment
  where
    assignment = apply ⊣ and ⊗ (string "=" ≫ assignment ⊕ always)
      where
        apply = C.assign `branchDistribute` unit'
    and = foldlP apply ⊣ equal ⊗ many (string "&&" ≫ equal)
      where
        apply = C.logicalAnd
    equal = foldlP apply ⊣ relational ⊗ many (string "==" ≫ relational ⊕ string "!=" ≫ relational)
      where
        apply = C.equal `branchDistribute` C.notEqual
    relational = foldlP apply ⊣ binaryAdd ⊗ many (r "<" ⊕ r "<=" ⊕ r ">" ⊕ r ">=")
      where
        r op = string op ≫ binaryAdd
        apply = C.lessThen `b` C.lessThenEqual `b` C.greaterThen `b` C.greaterThenEqual
          where
            b = branchDistribute
    binaryAdd = foldlP apply ⊣ binaryMul ⊗ many (add ⊕ sub)
      where
        add = string "+" ≫ binaryMul
        sub = string "-" ≫ binaryMul
        apply = branchDistribute C.addition C.subtraction
    binaryMul = foldlP apply ⊣ prefix ⊗ many (mul ⊕ div ⊕ mod)
      where
        mul = string "*" ≫ prefix
        div = string "/" ≫ prefix
        mod = string "%" ≫ prefix
        apply = C.multiplication `branchDistribute` C.division `branchDistribute` C.modulus
    prefix = ptr ∥ addr ∥ postfix
      where
        ptr = C.dereference ⊣ string "*" ≫ prefix
        addr = C.address ⊣ string "&" ≫ prefix
    postfix = foldlP apply ⊣ core ⊗ many (arguments ⊕ member)
      where
        apply = C.call `branchDistribute` C.member
        arguments = betweenParens $ commaSeperatedMany expression
        member = string "." ≫ identifer
    core = C.variable ⊣ identifer ∥ C.integerLiteral ⊣ integer ∥ betweenParens expression

code = header ≫ many statement
