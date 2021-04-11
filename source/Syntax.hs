module Syntax where

import Control.Applicative (Alternative, empty, (<|>))
import Control.Category (id, (.))
import Control.Monad (MonadPlus, liftM2)
import qualified Control.Monad.Combinators as Combinators
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (State, get, put, runState)
import Control.Monad.Trans.Writer (WriterT, runWriterT, tell)
import Core.Ast.Common as Core
import qualified Core.Ast.Kind as Core
import qualified Core.Ast.KindPattern as Core
import qualified Core.Ast.Multiplicity as Core
import qualified Core.Ast.Pattern as Core
import qualified Core.Ast.Sort as Core
import qualified Core.Ast.Term as Core
import qualified Core.Ast.Type as Core
import qualified Core.Ast.TypePattern as Core
import Data.Char (isAlphaNum, ord)
import Data.Maybe (fromJust)
import Data.Void (Void)
import Misc.Identifier
import Misc.Isomorph
import qualified Misc.Path as Path
import Misc.Prism
import qualified Misc.Symbol as Symbol
import qualified Module as Module
import Text.Megaparsec (Parsec, SourcePos)
import qualified Text.Megaparsec as Megaparsec
import qualified Text.Megaparsec.Char as Megaparsec
import Prelude hiding (id, (.))

-- https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf

infixr 4 ⊣

infixl 7 ≫

infixl 7 ≪

infixl 5 ⊕

infixl 6 ⊗

infixl 3 ∥

infixl 3 ∥#

class Syntax δ where
  syntaxmap :: Prism a b -> δ a -> δ b
  (⊗) :: δ a -> δ b -> δ (a, b)
  (∥) :: δ a -> δ a -> δ a
  never :: δ a
  always :: δ () -- effictivly 'pure ()'
  string :: String -> δ ()
  identifer :: δ Identifier
  stringLiteral :: δ String

  -- pretty printer only methods
  (∥#) :: δ a -> δ a -> δ a -- pretty printer only ∥, parser ignores first argument
  space :: δ ()
  line :: δ ()
  indent :: δ ()
  dedent :: δ ()

(⊣) :: (Syntax δ, ToPrism f) => f a b -> δ a -> δ b
f ⊣ p = syntaxmap (toPrism f) p

(⊕) :: Syntax δ => δ a -> δ b -> δ (Either a b)
p ⊕ q = left ⊣ p ∥ right ⊣ q

(≫) :: Syntax p => p () -> p a -> p a
p ≫ q = unit ⊣ p ⊗ q

(≪) :: Syntax p => p a -> p () -> p a
p ≪ q = unit' ⊣ p ⊗ q

choice = foldl (∥) never

many p = cons ⊣ p ⊗ (many p) ∥ nil ⊣ always

some p = cons ⊣ p ⊗ (many p)

seperatedMany p c = seperatedSome p c ∥ nil ⊣ always

seperatedSome p c = cons ⊣ p ⊗ (c ≫ seperatedSome p c ∥ nil ⊣ always)

between a b p = a ≫ p ≪ b

betweenParens = between (token "(") (token ")")

betweenAngle = between (token "<") (token ">")

betweenBracket = between (token "[") (token "]")

betweenBraces = between (token "{") (token "}")

class Position δ p where
  position :: δ p

token = string

keyword word = string ('%' : word)

moduleKeyword = string

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

term :: (Syntax δ, Position δ p) => δ (Core.Term p)
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
              Core.extern ⊣ keyword "extern" ≫ space ≫ symbol ≪ space ⊗ betweenBraces typex
            ]
        rotateBind = secondI Core.bound . associate . firstI swap

modulex = Module.coreModule ⊣ orderless ⊣ some item
  where
    itemCore brand inner = associate ⊣ firstI swap ⊣ position ⊗ moduleKeyword brand ≫ space ≫ identifer ≪ space ≪ token "=" ≪ space ⊗ inner ≪ token ";" ≪ line
    item = secondI Module.item ⊣ core
      where
        core =
          choice
            [ itemCore "module" (Module.modulex ⊣ lambdaMajor modulex),
              itemCore "inline" (Module.global . Module.inline ⊣ term),
              itemCore "import" (Module.global . Module.importx ⊣ position ⊗ path)
            ]

newtype Parser a = Parser (Parsec Void String a) deriving (Functor, Applicative, Monad, Alternative, MonadPlus)

withSourcePos :: g (f SourcePos) -> g (f SourcePos)
withSourcePos = id

withInternal :: g (f Internal) -> g (f Internal)
withInternal = id

parseTest (Parser p) = Megaparsec.parseTest p

parse (Parser p) = Megaparsec.parse p

instance Syntax Parser where
  syntaxmap (Prism f _) p = f <$> p
  (⊗) = liftM2 (,)
  (∥) = (<|>)
  never = empty
  always = pure ()
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

newtype Printer a = Printer (a -> Maybe (WriterT String (State Int) ()))

prettyPrint :: Printer a -> a -> IO ()
prettyPrint (Printer p) a = putStrLn $ snd $ fst $ (runState $ runWriterT $ fromJust $ p a) 0

instance Syntax Printer where
  syntaxmap (Prism _ f) (Printer p) = Printer $ \b -> f b >>= p
  Printer p ⊗ Printer q = Printer $ \(x, y) -> liftM2 (>>) (p x) (q y)
  Printer p ∥ Printer q = Printer $ \x -> (p x) <|> (q x)
  never = Printer $ const Nothing
  always = Printer $ \() -> Just $ pure ()
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
