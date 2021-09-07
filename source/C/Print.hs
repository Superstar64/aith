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

string op = Printer $ \() -> Just $ op ++ " "

line = Printer $ \() -> Just $ "\n"

identifer = Printer $ \name -> Just $ name ++ " "

integer = Printer $ \n -> Just $ show n

betweenParens = between (string "(") (string ")")

betweenBraces = between (string "{") (string "}")

argumentList e = betweenParens (seperatedMany e (string ","))

preprocess x = line ≫ x ≪ line

once name x = preprocess (string "#ifndef " ≫ name) ⊗ preprocess (string "#define " ≫ name ⊗ string " " ≫ name) ⊗ x ≪ preprocess (string "#endif")

header :: Printer ()
header = preprocess (string "#include \"stdint.h\"")

globals = header ≫ many global

typex =
  choice
    [ C.pointer ⊣ string "void*",
      C.struct ⊣ string "struct" ≫ identifer,
      C.byte ⊣ string "int8_t",
      C.short ⊣ string "int16_t",
      C.int ⊣ string "int32_t",
      C.long ⊣ string "int64_t"
    ]

signedType =
  choice
    [ (C.signed ⊣ always) ⊗ (C.byte ⊣ string "int8_t"),
      (C.signed ⊣ always) ⊗ (C.short ⊣ string "int16_t"),
      (C.signed ⊣ always) ⊗ (C.int ⊣ string "int32_t"),
      (C.signed ⊣ always) ⊗ (C.long ⊣ string "int64_t"),
      (C.unsigned ⊣ always) ⊗ (C.byte ⊣ string "uint8_t"),
      (C.unsigned ⊣ always) ⊗ (C.short ⊣ string "uint16_t"),
      (C.unsigned ⊣ always) ⊗ (C.int ⊣ string "uint32_t"),
      (C.unsigned ⊣ always) ⊗ (C.long ⊣ string "uint64_t")
    ]

global = functionDefinition ∥ structDefinition
  where
    functionDefinition = C.functionDefinition ⊣ typex ⊗ identifer ⊗ arguments ⊗ compound
      where
        arguments = argumentList (typex ⊗ identifer)
    structDefinition = C.structDefinition . toPrism ignoreCpp ⊣ once identifer definition
      where
        definition = string "struct" ≫ identifer ⊗ betweenBraces (many declare) ≪ string ";"
          where
            declare = typex ⊗ identifer ≪ string ";"
    ignoreCpp = discardInfo (\(name, _) -> (name, (name, name)))

compound = betweenBraces $ many statement

statement =
  choice
    [ C.returnx ⊣ string "return" ≫ expression ≪ string ";",
      C.forwardDeclare ⊣ typex ⊗ identifer ⊗ argumentList typex ≪ string ";",
      C.variableDeclation ⊣ typex ⊗ identifer ≪ string "=" ⊗ expression ≪ string ";"
    ]

expression = choice options
  where
    options =
      [ C.variable ⊣ identifer,
        C.call ⊣ betweenParens (betweenParens castFunctionPointer ⊗ expression) ⊗ argumentList expression,
        C.compoundLiteral ⊣ betweenParens typex ⊗ betweenBraces (seperatedMany expression (string ",")),
        C.member ⊣ betweenParens expression ≪ string "." ⊗ identifer,
        C.dereference ⊣ betweenParens (string "*" ≫ betweenParens (typex ≪ string "*") ⊗ expression),
        C.address ⊣ betweenParens (betweenParens (string "void*") ≫ string "&" ≫ expression),
        C.integerLiteral ⊣ integer,
        C.addition ⊣ betweenParens signedType ⊗ betweenParens expression ⊗ string "+" ≫ betweenParens signedType ⊗ betweenParens expression,
        C.subtraction ⊣ betweenParens signedType ⊗ betweenParens expression ⊗ string "-" ≫ betweenParens signedType ⊗ betweenParens expression,
        C.multiplication ⊣ betweenParens signedType ⊗ betweenParens expression ⊗ string "*" ≫ betweenParens signedType ⊗ betweenParens expression,
        C.division ⊣ betweenParens signedType ⊗ betweenParens expression ⊗ string "/" ≫ betweenParens signedType ⊗ betweenParens expression
      ]
    castFunctionPointer = typex ≪ string "(*)" ⊗ argumentList typex
