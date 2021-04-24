module C.Print where

import qualified C.Ast as C
import Control.Category ((.))
import Control.Monad.Trans.Writer (tell)
import Misc.Isomorph
import Misc.Prism
import Misc.Syntax
import Prelude hiding (id, (.))

string op = Printer $ \() -> Just $ do
  tell op >> tell " "

line = Printer $ \() -> Just $ tell "\n"

identifer = Printer $ \name -> Just $ tell name >> tell " "

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

expression = variable ∥ call
  where
    variable = C.variable ⊣ identifer
    call = C.call ⊣ betweenParens (betweenParens castFunctionPointer ⊗ expression) ⊗ argumentList expression
      where
        castFunctionPointer = representation ≪ string "(*)" ⊗ argumentList representation
