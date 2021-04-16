module Syntax where

import Control.Category (id, (.))
import qualified Control.Monad.Combinators as Combinators
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (get, put)
import Control.Monad.Trans.Writer (tell)
import Core.Ast.Common as Core
import qualified Core.Ast.FunctionLiteral as Core
import qualified Core.Ast.Kind as Core
import qualified Core.Ast.KindPattern as Core
import qualified Core.Ast.Multiplicity as Core
import qualified Core.Ast.Pattern as Core
import qualified Core.Ast.Sort as Core
import qualified Core.Ast.Term as Core
import qualified Core.Ast.Type as Core
import qualified Core.Ast.TypePattern as Core
import Data.Char (isAlphaNum, ord)
import Misc.Identifier
import Misc.Isomorph
import qualified Misc.Path as Path
import Misc.Prism
import qualified Misc.Symbol as Symbol
import Misc.Syntax
import qualified Module as Module
import Text.Megaparsec (SourcePos)
import qualified Text.Megaparsec as Megaparsec
import qualified Text.Megaparsec.Char as Megaparsec
import Prelude hiding (id, (.))

-- https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf

infixl 3 ∥#

class SyntaxBase δ => Syntax δ where
  string :: String -> δ ()
  identifer :: δ Identifier
  stringLiteral :: δ String

  -- pretty printer only methods
  (∥#) :: δ a -> δ a -> δ a -- pretty printer only ∥, parser ignores first argument
  space :: δ ()
  line :: δ ()
  indent :: δ ()
  dedent :: δ ()

class Position δ p where
  position :: δ p

token = string

keyword word = string ('%' : word)

moduleKeyword = string

betweenParens = between (token "(") (token ")")

betweenAngle = between (token "<") (token ">")

betweenBracket = between (token "[") (token "]")

betweenBraces = between (token "{") (token "}")

symbol = Symbol.symbol ⊣ stringLiteral

lambdaCore e = token "=>" ≫ space ≫ e

lambdaOuter e = betweenBraces e ∥ lambdaCore e

lambdaMajor e = betweenBraces (indent ≫ line ≫ e ≪ dedent ≪ line) ∥ lambdaCore e

withInnerPosition core app = toPrism core . secondP app . toPrism (extractInfo $ location . fst)

path = (Path.path . swapNonEmpty) ⊣ identifer ⊗ pathTail
  where
    pathTail = cons ⊣ token "/" ≫ identifer ⊗ pathTail ∥ nil ⊣ always

linear = Core.coreMultiplicity ⊣ position ⊗ core
  where
    core = Core.linear ⊣ keyword "linear" ∥ Core.unrestricted ⊣ keyword "unrestricted"

sort = Core.kind ⊣ keyword "kind" ∥ Core.stage ⊣ keyword "stage" ∥ Core.representation ⊣ keyword "representation"

kindPattern = Core.coreKindPattern ⊣ position ⊗ core
  where
    core = Core.kindPatternVariable ⊣ identifer ⊗ token ":" ≫ sort

kind = kindBottom
  where
    kindBottom = higher `branchDistribute` unit' ⊣ kindCore ⊗ (space ≫ token "->" ≫ space ≫ kindBottom ⊕ always)
      where
        higher = withInnerPosition Core.coreKind Core.higher
    kindCore = Core.coreKind ⊣ position ⊗ core ∥ betweenParens kindBottom
      where
        core =
          choice
            [ Core.kindVariable ⊣ identifer,
              Core.typex ⊣ keyword "type" ≫ space ≫ kindCore,
              Core.runtime ⊣ keyword "runtime" ≫ space ≫ kindCore,
              Core.meta ⊣ keyword "meta",
              Core.functionRep ⊣ keyword "function",
              Core.pointerRep ⊣ keyword "pointer"
            ]

typePattern = Core.coreTypePattern ⊣ position ⊗ core
  where
    core = Core.typePatternVariable ⊣ identifer ⊗ token ":" ≫ kind

typex = typeBottom
  where
    typeLambda lambda =
      Core.coreType ⊣ position
        ⊗ choice
          [ Core.forallx ⊣ Core.bound ⊣ token "∀<" ≫ typePattern ≪ token ">" ≪ space ⊗ lambda (typeBottom),
            Core.kindForall ⊣ Core.bound ⊣ token "∀@" ≫ kindPattern ≪ space ⊗ lambda (typeBottom),
            Core.typeOperator ⊣ Core.bound ⊣ token "λ" ≫ typePattern ≪ space ⊗ lambda (typeBottom)
          ]
    typeBottom = typeLambda lambdaCore ∥# macro `branchDistribute` unit' ⊣ typeCore ⊗ (space ≫ token "->" ≫ space ≫ typeBottom ⊕ always)
      where
        macro = withInnerPosition Core.coreType Core.macro
    typeCore = foldlP (functionPointer `branchDistribute` typeConstruction) ⊣ top ⊗ many postfix
      where
        postfix = token "(*)" ≫ betweenParens (seperatedMany typex (token ",")) ⊕ betweenParens typeBottom
        typeConstruction = withInnerPosition Core.coreType Core.typeConstruction
        functionPointer = withInnerPosition Core.coreType Core.functionPointer
        top = typeLambda lambdaOuter ∥ Core.coreType ⊣ position ⊗ core ∥ betweenParens typeBottom
        core =
          choice
            [ Core.typeVariable ⊣ identifer,
              Core.ofCourse ⊣ token "!" ≫ typeCore
            ]

pattern = patternBottom
  where
    patternBottom = Core.corePattern ⊣ position ⊗ variable ∥ patternCore
      where
        variable = Core.patternVariable ⊣ identifer ⊗ token ":" ≫ typex
    patternCore = Core.corePattern ⊣ position ⊗ patternOfCourse ∥ betweenParens patternBottom
      where
        patternOfCourse = Core.patternOfCourse ⊣ token "!" ≫ patternCore

term = termBottom
  where
    termBottom = foldlP applyPostfix ⊣ termCore ⊗ many postfix
      where
        applyPostfix = functionApplication `branchDistribute` macroApplication `branchDistribute` typeApplication `branchDistribute` kindApplication
        postfix = token "(*)" ≫ betweenParens (seperatedMany termBottom (token ",")) ⊕ betweenParens term ⊕ betweenAngle typex ⊕ token "@" ≫ kind
        functionApplication = withInnerPosition Core.coreTerm Core.functionApplication
        macroApplication = withInnerPosition Core.coreTerm Core.macroApplication
        typeApplication = withInnerPosition Core.coreTerm Core.typeApplication
        kindApplication = withInnerPosition Core.coreTerm Core.kindApplication
    termCore = Core.coreTerm ⊣ position ⊗ core ∥ betweenParens termBottom
      where
        core =
          choice
            [ Core.variable ⊣ identifer,
              Core.macroAbstraction ⊣ Core.bound ⊣ token "λ" ≫ pattern ≪ space ⊗ lambdaMajor termBottom,
              Core.typeAbstraction ⊣ Core.bound ⊣ token "Λ<" ≫ typePattern ≪ token ">" ≪ space ⊗ lambdaMajor termBottom,
              Core.kindAbstraction ⊣ Core.bound ⊣ token "Λ@" ≫ kindPattern ≪ space ⊗ lambdaMajor termBottom,
              Core.ofCourseIntroduction ⊣ token "!" ≫ termBottom,
              Core.bind ⊣ rotateBind ⊣ keyword "let" ≫ space ≫ pattern ≪ space ≪ token "=" ≪ space ⊗ termBottom ≪ token ";" ⊗ line ≫ termBottom,
              Core.extern ⊣ keyword "extern" ≫ space ≫ symbol ≪ space ⊗ betweenParens typex ⊗ betweenParens (seperatedMany typex (token ";"))
            ]
        rotateBind = secondI Core.bound . associate . firstI swap

functionLiteral = Core.functionLiteral ⊣ position ⊗ templateParameters ⊗ return ⊗ arguments ⊗ code
  where
    templateParameters = many (betweenAngle typePattern)
    return = betweenParens typex
    arguments = betweenParens (seperatedMany pattern (token ","))
    code = lambdaMajor term

modulex = Module.coreModule ⊣ orderless ⊣ some item
  where
    itemCore brand inner = moduleKeyword brand ≫ space ≫ identifer ≪ space ≪ token "=" ≪ space ⊗ inner ≪ token ";" ≪ line
    item =
      choice
        [ itemCore "module" (Module.modulex ⊣ lambdaMajor modulex),
          itemCore "inline" (Module.global . Module.inline ⊣ term),
          itemCore "import" (Module.global . Module.importx ⊣ position ⊗ path),
          itemCore "function" (Module.global . Module.text ⊣ functionLiteral)
        ]

withSourcePos :: g (f SourcePos) -> g (f SourcePos)
withSourcePos = id

withInternal :: g (f Internal) -> g (f Internal)
withInternal = id

instance Syntax Parser where
  string op = Parser $ Megaparsec.string op >> Megaparsec.space
  identifer = Parser $ Identifier <$> Combinators.some (Megaparsec.satisfy legalChar Megaparsec.<?> "letter") <* Megaparsec.space
    where
      isGreek x = x >= 0x370 && x <= 0x3ff
      legalChar x = isAlphaNum x && not (isGreek (ord x))
  stringLiteral = Parser $ do
    Megaparsec.string "\""
    Combinators.manyTill (Megaparsec.satisfy (const True)) (Megaparsec.string "\"") <* Megaparsec.space
  _ ∥# q = q
  space = Parser $ pure ()
  line = Parser $ pure ()
  indent = Parser $ pure ()
  dedent = Parser $ pure ()

instance Position Parser SourcePos where
  position = Parser $ Megaparsec.getSourcePos

instance Position Parser Internal where
  position = Parser $ pure Internal

instance Syntax Printer where
  string op = Printer $ \() -> Just $ tell op
  identifer = Printer $ \(Identifier name) -> Just $ tell name
  stringLiteral = Printer $ \str -> Just $ do
    tell "\""
    tell str
    tell "\""
  (∥#) = (∥)
  space = Printer $ \() -> Just $ tell " "
  line = Printer $ \() -> Just $ do
    indention <- lift get
    tell "\n"
    sequence $ replicate indention (tell "\t")
    pure ()
  indent = Printer $ \() -> Just $ do
    indention <- lift get
    lift $ put $ indention + 1
    pure ()
  dedent = Printer $ \() -> Just $ do
    indention <- lift get
    lift $ put $ indention - 1
    pure ()

instance Position Printer Internal where
  position = Printer $ \Internal -> Just $ pure ()
