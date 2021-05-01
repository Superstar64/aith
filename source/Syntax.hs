module Syntax where

import Control.Category (id, (.))
import qualified Control.Monad.Combinators as Combinators
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (get, put)
import Control.Monad.Trans.Writer (tell)
import Core.Ast.Common as Core
import qualified Core.Ast.Kind as Core
import qualified Core.Ast.KindPattern as Core
import qualified Core.Ast.Pattern as Core
import qualified Core.Ast.RuntimePattern as Core
import qualified Core.Ast.Sort as Core
import qualified Core.Ast.Term as Core
import qualified Core.Ast.Type as Core
import qualified Core.Ast.TypePattern as Core
import Data.Char (isAlphaNum)
import Misc.Identifier
import Misc.Isomorph
import qualified Misc.Path as Path
import Misc.Prism
import Misc.Silent
import qualified Misc.Symbol as Symbol
import Misc.Syntax
import qualified Module as Module
import Text.Megaparsec (SourcePos)
import qualified Text.Megaparsec as Megaparsec
import qualified Text.Megaparsec.Char as Megaparsec
import Prelude hiding (id, (.))

-- https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf

infixl 3 ∥#

-- to allow for correct pretty printing right recursion is limited to an equal or higher precedence level

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

keyword word = string ('_' : word)

moduleKeyword = string

betweenParens = between (token "(") (token ")")

betweenTypeParens = between (token "`(") (token ")")

betweenAngle = between (token "<") (token ">")

betweenKindParens = between (token "``(") (token ")")

betweenBraces = between (token "{") (token "}")

symbol = Symbol.symbol ⊣ stringLiteral

lambdaCore e = space ≫ token "=>" ≫ space ≫ e

lambdaInline e = space ≫ betweenBraces e ∥ lambdaCore e

lambdaMajor e = space ≫ betweenBraces (indent ≫ line ≫ e ≪ dedent ≪ line) ∥ lambdaCore e

commaMany e = many (token "," ≫ space ≫ e)

commaSome e = some (token "," ≫ space ≫ e)

commaSeperatedMany e = seperatedMany e (token "," ≫ space)

multiarg core = singleton ∥# keyword "multiarg" ≫ betweenParens (commaSeperatedMany core) ∥ singleton
  where
    singleton = cons ⊣ core ⊗ (nil ⊣ always)

withInnerPosition core app = toPrism core . secondP app . toPrism (extractInfo $ location . fst)

path = (Path.path . swapNonEmpty) ⊣ token "/" ≫ identifer ⊗ pathTail
  where
    pathTail = cons ⊣ token "/" ≫ identifer ⊗ pathTail ∥ nil ⊣ always

semiPath = token "/" ≫ pathTail ∥ nil ⊣ always
  where
    pathTail = cons ⊣ identifer ⊗ (token "/" ≫ pathTail ∥ nil ⊣ always)

sort = Core.kind ⊣ keyword "kind" ∥ Core.stage ⊣ keyword "stage" ∥ Core.representation ⊣ keyword "representation"

kindPattern = Core.coreKindPattern ⊣ position ⊗ core
  where
    core = Core.kindPatternVariable ⊣ identifer ⊗ token ":" ≫ sort

kind = kindBottom
  where
    kindLambda lambda = Core.poly ⊣ Core.bound ⊣ token "`\\/" ≫ kindPattern ⊗ lambda kind
    kindBottom = Core.coreKind ⊣ position ⊗ kindLambda lambdaCore ∥# higher `branchDistribute` unit' ⊣ kindCore ⊗ (space ≫ token "->" ≫ space ≫ kind ⊕ always)
      where
        higher = withInnerPosition Core.coreKind Core.higher
    kindCore = Core.coreKind ⊣ position ⊗ kindLambda lambdaInline ∥ Core.coreKind ⊣ position ⊗ core ∥ betweenParens kind
      where
        core =
          choice
            [ Core.kindVariable ⊣ identifer,
              Core.typex ⊣ keyword "type" ≫ space ≫ kindCore,
              Core.runtime ⊣ keyword "runtime" ≫ space ≫ kindCore,
              Core.constraint ⊣ keyword "constraint",
              Core.meta ⊣ keyword "meta",
              Core.text ⊣ keyword "text",
              Core.pointerRep ⊣ keyword "pointer",
              Core.structRep ⊣ keyword "struct" ≫ betweenParens (commaSeperatedMany kind)
            ]

typePattern = Core.coreTypePattern ⊣ position ⊗ core
  where
    core = Core.typePatternVariable ⊣ identifer ⊗ (pointer ∥# token ":" ≫ kind ∥ pointer)
    pointer = Core.coreKind ⊣ position ⊗ (Core.typex ⊣ Core.coreKind ⊣ position ⊗ (Core.runtime ⊣ Core.coreKind ⊣ position ⊗ (Core.pointerRep ⊣ always)))

typeParens = betweenParens typex

typex = typeBottom
  where
    typeLambda lambda =
      choice
        [ Core.forallx ⊣ Core.bound ⊣ token "`\\/" ≫ typePattern ⊗ lambda typex,
          Core.kindForall ⊣ Core.bound ⊣ token "``\\/" ≫ kindPattern ⊗ lambda typex,
          Core.typeOperator ⊣ Core.bound ⊣ token "\\" ≫ typePattern ⊗ lambda typex,
          Core.polyOperator ⊣ Core.bound ⊣ token "`\\" ≫ kindPattern ⊗ lambda typex,
          Core.recursive ⊣ Core.bound ⊣ keyword "recursive" ≫ space ≫ typePattern ⊗ lambda typex
        ]
    typeBottom = Core.coreType ⊣ position ⊗ typeLambda lambdaCore ∥# applyBinary ⊣ typePostfix ⊗ binary
      where
        binary = space ≫ token "->" ≫ space ≫ typex ⊕ space ≫ token "=>?" ≫ space ≫ typex ⊕ always
        applyBinary = macro `branchDistribute` erasedQualified `branchDistribute` unit'
        macro = withInnerPosition Core.coreType Core.macro
        erasedQualified = withInnerPosition Core.coreType Core.erasedQualified
    typePostfix = foldlP applyPostfix ⊣ typeCore ⊗ many postfix
      where
        applyPostfix = functionLiteralType `branchDistribute` functionPointer `branchDistribute` polyConstruction `branchDistribute` typeConstruction
        postfix = keyword "function" ≫ multiarg typeCore ⊕ token "(*)" ≫ multiarg typeCore ⊕ betweenTypeParens kind ⊕ space ≫ typeCore
        typeConstruction = withInnerPosition Core.coreType Core.typeConstruction
        functionLiteralType = withInnerPosition Core.coreType Core.functionLiteralType
        functionPointer = withInnerPosition Core.coreType Core.functionPointer
        polyConstruction = withInnerPosition Core.coreType Core.polyConstruction
    typeCore = Core.coreType ⊣ position ⊗ typeLambda lambdaInline ∥ Core.coreType ⊣ position ⊗ core ∥ runtimeTuple ∥ typeParens
      where
        core =
          choice
            [ Core.typeVariable ⊣ identifer,
              Core.ofCourse ⊣ token "!" ≫ typeCore,
              Core.copy ⊣ keyword "copy" ≫ space ≫ typeCore
            ]
        runtimeTuple = foldlNonEmptyP runtimePair ⊣ token "#" ≫ betweenParens (typex ⊗ commaSome typex)
          where
            runtimePair = withInnerPosition Core.coreType Core.runtimePair

pattern = patternBottom
  where
    patternBottom = Core.corePattern ⊣ position ⊗ variable ∥ patternCore
      where
        variable = Core.patternVariable ⊣ identifer ⊗ token ":" ≫ typex
    patternCore = Core.corePattern ⊣ position ⊗ patternOfCourse ∥ betweenParens pattern
      where
        patternOfCourse = Core.patternOfCourse ⊣ token "!" ≫ patternCore

runtimePatternParens = foldlP runtimePatternPair ⊣ betweenParens (runtimePattern ⊗ commaMany runtimePattern)
  where
    runtimePatternPair = withInnerPosition Core.coreRuntimePattern Core.runtimePatternPair

runtimePatternMultiarg = multiarg runtimePattern

runtimePattern = patternBottom
  where
    patternBottom = Core.coreRuntimePattern ⊣ position ⊗ variable ∥ runtimePatternParens
      where
        variable = Core.runtimePatternVariable ⊣ identifer ⊗ token ":" ≫ typex

termParens = betweenParens term

term = termBottom
  where
    base =
      choice
        [ Core.bind ⊣ rotateBind ⊣ keyword "let" ≫ space ≫ pattern ≪ space ≪ token "=" ≪ space ⊗ term ≪ token ";" ⊗ line ≫ term,
          Core.alias ⊣ rotateBind ⊣ keyword "alias" ≫ space ≫ runtimePattern ≪ space ≪ token "=" ≪ space ⊗ term ≪ token ";" ⊗ line ≫ term
        ]
      where
        rotateBind = secondI Core.bound . associate . firstI swap
    termLambda lambda =
      choice
        [ Core.typeAbstraction ⊣ Core.bound ⊣ token "`\\" ≫ typePattern ⊗ lambda term,
          Core.kindAbstraction ⊣ Core.bound ⊣ token "``\\" ≫ kindPattern ⊗ lambda term,
          Core.erasedQualifiedAssume ⊣ keyword "when" ≫ space ≫ typex ⊗ lambda term
        ]
    termBottom = Core.coreTerm ⊣ position ⊗ termLambda lambdaCore ∥# Core.coreTerm ⊣ position ⊗ base ∥ foldlP applyPostfix ⊣ termCore ⊗ many postfix
      where
        applyPostfix = functionApplication `branchDistribute` macroApplication `branchDistribute` typeApplication `branchDistribute` kindApplication `branchDistribute` erasedQualifiedCheck
        postfix = space ≫ token "(*)" ≫ multiarg termCore ⊕ space ≫ termCore ⊕ space ≫ betweenTypeParens typex ⊕ space ≫ betweenKindParens kind ⊕ space ≫ token "?"
        functionApplication = withInnerPosition Core.coreTerm Core.functionApplication
        macroApplication = withInnerPosition Core.coreTerm Core.macroApplication
        typeApplication = withInnerPosition Core.coreTerm Core.typeApplication
        kindApplication = withInnerPosition Core.coreTerm Core.kindApplication
        erasedQualifiedCheck = withInnerPosition Core.coreTerm (Core.erasedQualifiedCheck . toPrism unit')
    termCore = keyword "function" ≫ functionCore ∥ Core.coreTerm ⊣ position ⊗ core ∥ Core.coreTerm ⊣ position ⊗ termLambda lambdaInline ∥ runtimeTupleIntroduction ∥ termParens
      where
        core =
          choice
            [ Core.variable ⊣ identifer,
              Core.macroAbstraction ⊣ Core.bound ⊣ token "\\" ≫ pattern ⊗ lambdaMajor term,
              Core.extern ⊣ keyword "extern" ≫ space ≫ symbol ≪ space ⊗ typeParens ⊗ multiarg typeParens,
              Core.pack ⊣ keyword "pack" ≫ space ≫ betweenParens (Core.bound ⊣ typePattern ⊗ lambdaInline typex) ⊗ space ≫ termCore,
              Core.unpack ⊣ keyword "unpack" ≫ space ≫ termCore,
              Core.ofCourseIntroduction ⊣ token "!" ≫ termCore
            ]
        runtimeTupleIntroduction = foldlNonEmptyP runtimePairIntrouction ⊣ token "#" ≫ betweenParens (term ⊗ commaSome term)
          where
            runtimePairIntrouction = withInnerPosition Core.coreTerm Core.runtimePairIntrouction

functionCore = Core.coreTerm ⊣ position ⊗ core
  where
    core = Core.functionLiteral ⊣ Core.bound ⊣ multiarg runtimePattern ⊗ lambdaMajor term

functionLiteral = templateParameters ∥ concepts ∥ functionCore ∥ token "~" ≫ term
  where
    templateParameters = Core.coreTerm ⊣ position ⊗ (Core.typeAbstraction ⊣ Core.bound ⊣ token "`\\" ≫ typePattern ≪ space ⊗ functionLiteral)
    concepts = Core.coreTerm ⊣ position ⊗ (Core.erasedQualifiedAssume ⊣ moduleKeyword "when" ≫ typeParens ≪ space ⊗ functionLiteral)

modulex = Module.coreModule ⊣ orderless ⊣ assumeNonEmpty ⊣ some (item itemCore lambdaMajor)
  where
    itemCore brand inner = moduleKeyword brand ≫ space ≫ identifer ≪ space ≪ token "=" ≪ space ⊗ inner ≪ token ";" ≪ line

item ::
  (Syntax δ, Position δ p) =>
  (String -> δ (Module.Item Silent p) -> δ a) ->
  (δ (Module.Module Silent p) -> δ (Module.Module Silent p)) ->
  δ a
item itemCore lambda =
  choice
    [ itemCore "module" (Module.modulex ⊣ lambda modulex),
      itemCore "inline" (Module.global . Module.inline ⊣ term),
      itemCore "import" (Module.global . Module.importx ⊣ position ⊗ path),
      itemCore "function" (Module.global . Module.text ⊣ functionLiteral),
      itemCore "type" (Module.global . Module.synonym ⊣ typex)
    ]

itemSingleton = item itemCore id
  where
    itemCore brand inner = moduleKeyword brand ≫ token ":" ≫ line ≫ inner

withSourcePos :: g (f SourcePos) -> g (f SourcePos)
withSourcePos = id

withInternal :: g (f Internal) -> g (f Internal)
withInternal = id

instance Syntax Parser where
  string op = Parser $ Megaparsec.string op >> Megaparsec.space
  identifer = Parser $ Identifier <$> Combinators.some (Megaparsec.satisfy legalChar Megaparsec.<?> "letter") <* Megaparsec.space
    where
      legalChar x = isAlphaNum x
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
