module C.Print where

import qualified C.Ast as C
import Control.Monad.Trans.Writer (tell)
import Misc.Syntax

string op = Printer $ \() -> Just $ do
  tell op >> tell " "

line = Printer $ \() -> Just $ tell "\n"

identifer = Printer $ \name -> Just $ tell name >> tell " "

betweenParens = between (string "(") (string ")")

betweenBraces = between (string "{") (string "}")

argumentList e = betweenParens (seperatedMany e (string ","))

header =
  foldr
    (≫)
    always
    [ string "#ifndef AITH",
      line,
      string "#define AITH AITH",
      line,
      string "typedef void* pointer;",
      line,
      string "#endif",
      line
    ]

globals = header ≫ many functionDefinition

pointer = C.pointer ⊣ string "pointer"

function = C.function ⊣ string "function"

representation = pointer ∥ function

functionDefinition = C.functionDefinition ⊣ representation ⊗ identifer ⊗ arguments ⊗ compound
  where
    arguments = argumentList (representation ⊗ identifer)

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
