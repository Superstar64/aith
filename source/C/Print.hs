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

betweenParens = between (string "(") (string ")")

betweenBraces = between (string "{") (string "}")

argumentList e = betweenParens (seperatedMany e (string ","))

preprocess x = line ≫ x ≪ line

once name x = preprocess (string "#ifndef " ≫ name) ⊗ preprocess (string "#define " ≫ name ⊗ string " " ≫ name) ⊗ x ≪ preprocess (string "#endif")

header :: Printer ()
header = discardInfo (\() -> ((), ((), ()))) ⊣ once (string "AITH") (string "typedef void* pointer;")

globals = header ≫ many global

pointer = C.pointer ⊣ string "pointer" ∥ C.struct ⊣ string "struct" ≫ identifer

representation = pointer

global = functionDefinition ∥ structDefinition
  where
    functionDefinition = C.functionDefinition ⊣ representation ⊗ identifer ⊗ arguments ⊗ compound
      where
        arguments = argumentList (representation ⊗ identifer)
    structDefinition = C.structDefinition . toPrism ignoreCpp ⊣ once identifer definition
      where
        definition = string "struct" ≫ identifer ⊗ betweenBraces (many declare) ≪ string ";"
          where
            declare = representation ⊗ identifer ≪ string ";"
    ignoreCpp = discardInfo (\(name, _) -> (name, (name, name)))

compound = betweenBraces $ many statement

statement =
  choice
    [ C.returnx ⊣ string "return" ≫ expression ≪ string ";",
      C.forwardDeclare ⊣ representation ⊗ identifer ⊗ argumentList representation ≪ string ";",
      C.variableDeclation ⊣ representation ⊗ identifer ≪ string "=" ⊗ expression ≪ string ";"
    ]

expression = variable ∥ call ∥ compoundLiteral ∥ member ∥ dereference ∥ address
  where
    variable = C.variable ⊣ identifer
    call = C.call ⊣ betweenParens (betweenParens castFunctionPointer ⊗ expression) ⊗ argumentList expression
      where
        castFunctionPointer = representation ≪ string "(*)" ⊗ argumentList representation
    compoundLiteral = C.compoundLiteral ⊣ betweenParens representation ⊗ betweenBraces (seperatedMany expression (string ","))
    member = C.member ⊣ betweenParens expression ≪ string "." ⊗ identifer
    dereference = C.dereference ⊣ betweenParens (string "*" ≫ betweenParens (representation ≪ string "*") ⊗ expression)
    address = C.address ⊣ betweenParens (betweenParens (string "pointer") ≫ string "&" ≫ expression)
