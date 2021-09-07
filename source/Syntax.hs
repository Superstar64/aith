module Syntax where

import Control.Applicative (Alternative, empty, (<|>))
import Control.Category (id, (.))
import Control.Monad (MonadPlus, liftM2)
import qualified Control.Monad.Combinators as Combinators
import Control.Monad.State (State, get, put, runState)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Data.Char (isAlpha, isAlphaNum)
import Data.Maybe (fromJust)
import Data.Void (Void)
import Language.Ast.Common (Internal (..), location)
import qualified Language.Ast.Common as Language
import qualified Language.Ast.Kind as Language
import qualified Language.Ast.Sort as Language
import qualified Language.Ast.Term as Language
import qualified Language.Ast.Type as Language
import Misc.Isomorph
import qualified Misc.Path as Path
import Misc.Prism
import qualified Misc.Symbol as Symbol
import Misc.Syntax
import qualified Module as Module
import Text.Megaparsec (Parsec, SourcePos)
import qualified Text.Megaparsec as Megaparsec
import qualified Text.Megaparsec.Char as Megaparsec
import Prelude hiding (id, (.))

-- https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf

infixl 3 ∥#

-- to allow for correct pretty printing right recursion should be limited to an equal or higher precedence level

class SyntaxBase δ => Syntax δ where
  string :: String -> δ ()
  identifer :: δ String
  stringLiteral :: δ String
  number :: δ Integer

  -- parser only methods
  try :: δ a -> δ a

  -- pretty printer only methods
  pick :: (a -> Bool) -> δ a -> δ a -> δ a -- normal ∥ for parser, left when function is true for printer
  (∥#) :: δ a -> δ a -> δ a -- pretty printer only ∥, parser ignores first argument
  space :: δ ()
  line :: δ ()
  indent :: δ ()
  dedent :: δ ()

class Position δ p where
  position :: δ p

token = string

binaryToken op = space ≫ token op ≫ space

keyword word = string ('_' : word)

prefixKeyword word = keyword word ≫ space

moduleKeyword = string

betweenParens = between (token "(") (token ")")

betweenAngle = between (token "<") (token ">")

betweenBraces = between (token "{") (token "}")

betweenSquares = between (token "[") (token "]")

betweenBangParens = between (token "!(") (token ")")

betweenBangSquares = between (token "![") (token "]")

betweenStarSquares = between (token "*[") (token "]")

symbol = Symbol.symbol ⊣ stringLiteral

lambdaCore e = binaryToken "=>" ≫ e

lambdaInline e = space ≫ betweenBraces e ∥ lambdaCore e

lambdaMajor e = space ≫ betweenBraces (indent ≫ line ≫ e ≪ dedent ≪ line) ∥ lambdaCore e

commaSome e = some (token "," ≫ space ≫ e)

commaSeperatedMany e = seperatedMany e (token "," ≫ space)

commaSeperatedSome e = seperatedSome e (token "," ≫ space)

multiarg core = multiargExclusionary core ∥ singleton ⊣ core

-- excludes single argument multiargs
multiargExclusionary :: Syntax p => p a -> p [a]
multiargExclusionary core = apply ⊣ keyword "multiarg" ≫ betweenParens (core ⊗ token "," ≫ space ≫ commaSeperatedSome core ⊕ always)
  where
    apply = branch (cons . secondP (cons . toPrism (inverse nonEmpty))) nil

withInnerPosition core app = toPrism core . secondP app . toPrism (extractInfo $ location . fst)

withInnerPosition3 core app = toPrism core . secondP app . toPrism (extractInfo $ location . fst . fst)

path = (Path.path . swapNonEmpty) ⊣ token "/" ≫ identifer ⊗ pathTail
  where
    pathTail = cons ⊣ token "/" ≫ identifer ⊗ pathTail ∥ nil ⊣ always

semiPath = token "/" ≫ pathTail ∥ nil ⊣ always
  where
    pathTail = cons ⊣ identifer ⊗ (token "/" ≫ pathTail ∥ nil ⊣ always)

termIdentifier = Language.termIdentifier ⊣ identifer

typeIdentifier = Language.typeIdentifier ⊣ identifer

kindIdentifier = Language.kindIdentifier ⊣ identifer

sort =
  choice
    [ Language.kind ⊣ keyword "kind",
      Language.stage ⊣ keyword "stage",
      Language.impact ⊣ keyword "impact",
      Language.existance ⊣ keyword "existance",
      Language.representation ⊣ keyword "representation",
      Language.size ⊣ keyword "size",
      Language.signedness ⊣ keyword "signedness"
    ]

kindPattern = Language.pattern ⊣ position ⊗ kindIdentifier ⊗ token ":" ≫ sort

kind :: (Position δ p, Syntax δ) => δ (Language.Kind Void p)
kind = kindRuntime
  where
    kindRuntime = applyBinary ⊣ kindPrefix ⊗ (binaryToken "@" ≫ kindRuntime ⊕ always)
      where
        applyBinary = runtime `branchDistribute` unit'
        runtime = withInnerPosition Language.coreKind Language.runtime
    kindPrefix = Language.coreKind ⊣ position ⊗ choice options ∥ kindCore
      where
        options =
          [ Language.real ⊣ prefixKeyword "real" ≫ kindCore,
            Language.wordRep ⊣ prefixKeyword "word" ≫ kindCore
          ]

kindCore = Language.coreKind ⊣ position ⊗ choice options ∥ betweenParens kind
  where
    options =
      [ Language.kindVariable ⊣ kindIdentifier,
        Language.meta ⊣ keyword "meta",
        Language.code ⊣ keyword "code",
        Language.datax ⊣ keyword "data",
        Language.imaginary ⊣ keyword "imaginary",
        Language.evidence ⊣ keyword "evidence",
        Language.region ⊣ prefixKeyword "region",
        Language.text ⊣ keyword "text",
        Language.pointerRep ⊣ keyword "pointer",
        Language.structRep ⊣ prefixKeyword "struct" ≫ betweenParens (commaSeperatedMany kind),
        Language.typex ⊣ betweenStarSquares kind,
        Language.byte ⊣ keyword "byte",
        Language.short ⊣ keyword "short",
        Language.int ⊣ keyword "int",
        Language.long ⊣ keyword "long",
        Language.signed ⊣ keyword "signed",
        Language.unsigend ⊣ keyword "unsigned"
      ]

kindCoreAuto = just ⊣ kindCore ∥ nothing ⊣ token "_"

kindAuto = just ⊣ kind ∥ nothing ⊣ token "_"

typePattern = Language.pattern ⊣ position ⊗ typeIdentifier ⊗ (just ⊣ token ":" ≫ kind ∥ nothing ⊣ always)

typex :: (Position δ p, Syntax δ) => δ (Language.Type (Language.KindAuto p) Void p)
typex = typeArrow
  where
    typeArrow = applyBinary ⊣ typeRTArrow ⊗ (binaryToken "-`>" ≫ typeArrow ⊕ binaryToken "-^>" ≫ typeArrow ⊕ always)
      where
        applyBinary = macro `branchDistribute` implied `branchDistribute` unit'
        macro = withInnerPosition Language.coreType Language.macro
        implied = withInnerPosition Language.coreType Language.implied
    typeRTArrow = applyBinary ⊣ typePair ⊗ (binaryToken "->" ≫ typeRTArrow ⊕ space ≫ prefixKeyword "function" ≫ typeRTArrow ⊕ always)
      where
        applyBinary = functionPointer `branchDistribute` functionLiteralType `branchDistribute` unit'
        functionPointer = withInnerPosition Language.coreType Language.functionPointer
        functionLiteralType = withInnerPosition Language.coreType Language.functionLiteralType
    typePair = foldlP pair ⊣ typeApply ⊗ many (token "," ≫ space ≫ typeApply)
      where
        pair = withInnerPosition Language.coreType Language.runtimePair
    typeApply = Language.coreType ⊣ position ⊗ choice options ∥ typeCore
      where
        options =
          [ Language.copy ⊣ prefixKeyword "copy" ≫ typeCore,
            Language.regionTransformer ⊣ prefixKeyword "state" ≫ typeCore ⊗ space ≫ typeCore,
            Language.regionReference ⊣ prefixKeyword "reference" ≫ typeCore ⊗ space ≫ typeCore,
            Language.number ⊣ prefixKeyword "number" ≫ kindCoreAuto ≪ space ⊗ kindCoreAuto,
            Language.ofCourse ⊣ betweenBangSquares typex
          ]

typeCore = Language.coreType ⊣ position ⊗ variable ∥ betweenParens typex
  where
    variable = Language.typeVariable ⊣ typeIdentifier

typeAuto = just ⊣ typex ∥ nothing ⊣ token "_"

typeCoreAuto = just ⊣ typeCore ∥ nothing ⊣ token "_"

typeAnnotation = just ⊣ binaryToken ":" ≫ typeCore ∥ nothing ⊣ always

typeScheme = typeSchemeCore
  where
    typeSchemeCore = Language.coreTypeScheme ⊣ position ⊗ choice options
    options =
      [ Language.monoType ⊣ typex,
        token "\\/" ≫ (Language.forallx ⊣ Language.bound ⊣ typePattern ⊗ lambdaCore typeScheme),
        token "\\|/" ≫ (Language.kindForall ⊣ Language.bound ⊣ kindPattern ⊗ lambdaCore typeScheme)
      ]

termPattern = patternTop
  where
    patternTop = Language.coreTermPattern ⊣ position ⊗ variableLong ∥ patternPair
      where
        variableLong = try $ Language.patternVariable ⊣ termIdentifier ⊗ (just ⊣ binaryToken ":" ≫ typex)
    patternPair = foldlP pair ⊣ patternCore ⊗ many (binaryToken "," ≫ patternCore)
      where
        pair = withInnerPosition Language.coreTermPattern Language.patternRuntimePair
    patternCore = Language.coreTermPattern ⊣ position ⊗ choice options ∥ betweenParens termPattern
      where
        options =
          [ Language.patternVariable ⊣ termIdentifier ⊗ (nothing ⊣ always),
            Language.patternCopy ⊣ betweenBangParens term ⊗ betweenSquares termPattern,
            Language.patternOfCourse ⊣ betweenBangSquares termPattern
          ]

term :: (Position δ p, Syntax δ) => δ (Language.Term () (Language.KindAuto p) (Language.TypeAuto p) p)
term = termBinding
  where
    termBinding = Language.coreTerm ⊣ position ⊗ choice options ∥ termRTApply
      where
        options =
          [ Language.bind ⊣ rotateBind ⊣ prefixKeyword "inline" ≫ termPattern ≪ binaryToken "=" ⊗ term ≪ token ";" ≪ line ⊗ term,
            Language.alias ⊣ rotateBind ⊣ prefixKeyword "let" ≫ termPattern ≪ binaryToken "=" ⊗ term ≪ token ";" ≪ line ⊗ term,
            Language.doRegionTransformer ⊣ rotateBind ⊣ prefixKeyword "do" ≫ termPattern ≪ binaryToken "=" ⊗ term ≪ token ";" ≪ line ⊗ term
          ]
        rotateBind = secondI Language.bound . associate . firstI swap
    termRTApply = applyBinary ⊣ termAdd ⊗ (binaryToken "$" ≫ termRTApply ⊗ typeAnnotation ⊕ always)
      where
        applyBinary = apply `branchDistribute` unit'
        apply = withInnerPosition3 Language.coreTerm Language.functionApplication . toPrism associate'
    signMarker = just ⊣ token "@" ≫ kindCore ≪ space ∥ nothing ⊣ always
    termAdd = foldlP applyAdd ⊣ termMul ⊗ many (binaryToken "+" ≫ (swap ⊣ signMarker ⊗ termMul) ⊕ binaryToken "-" ≫ (swap ⊣ signMarker ⊗ termMul))
      where
        applyAdd = add `branchDistribute` sub
        add = withInnerPosition3 Language.coreTerm (Language.arithmatic Language.Addition) . toPrism associate'
        sub = withInnerPosition3 Language.coreTerm (Language.arithmatic Language.Subtraction) . toPrism associate'
    termMul = foldlP applyMul ⊣ termPair ⊗ many (binaryToken "*" ≫ (swap ⊣ signMarker ⊗ termPair) ⊕ binaryToken "/" ≫ (swap ⊣ signMarker ⊗ termPair))
      where
        applyMul = mul `branchDistribute` div
        mul = withInnerPosition3 Language.coreTerm (Language.arithmatic Language.Multiplication) . toPrism associate'
        div = withInnerPosition3 Language.coreTerm (Language.arithmatic Language.Division) . toPrism associate'
    termPair = foldlP pair ⊣ termApply ⊗ many (token "," ≫ space ≫ termApply)
      where
        pair = withInnerPosition Language.coreTerm Language.runtimePairIntrouction
    termApply = Language.coreTerm ⊣ position ⊗ choice options ∥ foldlP applyBinary ⊣ termCore ⊗ many (space ≫ token "`" ≫ termCore ⊕ space ≫ token "^" ≫ termCore)
      where
        applyBinary = application `branchDistribute` implicationApplication
        application = withInnerPosition Language.coreTerm Language.macroApplication
        implicationApplication = withInnerPosition Language.coreTerm Language.implicationApplication
        options =
          [ Language.proofCopyPair ⊣ prefixKeyword "copyPair" ≫ termCore ⊗ space ≫ termCore,
            Language.readReference ⊣ prefixKeyword "read" ≫ termCore ≪ space ⊗ termCore ⊗ typeAnnotation,
            Language.pureRegionTransformer ⊣ prefixKeyword "pure" ≫ termCore
          ]

termCore = Language.coreTerm ⊣ position ⊗ choice options ∥ betweenParens term
  where
    options =
      [ Language.variable ⊣ termIdentifier ⊗ always,
        Language.macroAbstraction ⊣ Language.bound ⊣ token "`\\" ≫ termPattern ⊗ lambdaMajor term,
        Language.functionLiteral ⊣ Language.bound ⊣ token "\\" ≫ termPattern ⊗ lambdaMajor term,
        Language.implicationAbstraction ⊣ Language.bound ⊣ token "^\\" ≫ termPattern ⊗ lambdaMajor term,
        Language.extern ⊣ prefixKeyword "extern" ≫ symbol ≪ space ⊗ typeCoreAuto ≪ binaryToken "->" ⊗ typeCoreAuto,
        Language.proofCopyNumber ⊣ keyword "copyNumber",
        Language.proofCopyFunction ⊣ keyword "copyFunction",
        Language.proofCopyReference ⊣ keyword "copyReference",
        Language.ofCourseIntroduction ⊣ betweenBangSquares term,
        Language.numberLiteral ⊣ number ⊗ typeAnnotation
      ]

modulex ::
  (Syntax δ, Position δ p) =>
  δ (Module.ModuleAuto p)
modulex = Module.coreModule ⊣ orderless ⊣ list ⊣ some (item declare (token ";" ≫ line ≫ line) lambdaMajor) ⊕ never
  where
    declare = space ≫ identifer ≪ binaryToken "="

item header footer lambda =
  choice
    [ itemCore "module" (Module.modulex ⊣ lambda modulex),
      itemAnnotate "inline" (Module.global . Module.inline) term,
      itemCore "import" (Module.global . Module.importx ⊣ position ⊗ path),
      itemAnnotate "symbol" (Module.global . Module.text) term
    ]
  where
    itemCore brand inner = moduleKeyword brand ≫ header ⊗ inner ≪ footer
    itemAnnotate brand f inner = moduleKeyword brand ≫ (secondP f ⊣ correct ⊣ (annotated ∥ (nothing ⊣ always) ⊗ implicit))
      where
        correct = associate . firstI swap . associate'
        implicit = header ⊗ inner ≪ footer
        annotated = space ≫ moduleKeyword "_" ≫ binaryToken "::" ≫ (just ⊣ typeScheme) ≪ token ";" ≪ line ≪ moduleKeyword brand ⊗ implicit

itemSingleton ::
  (Syntax δ, Position δ p) => δ (Module.ItemAuto p)
itemSingleton = unit ⊣ item (token ":" ≫ line) always id

withSourcePos :: g (f SourcePos) -> g (f SourcePos)
withSourcePos = id

withInternal :: g (f Internal) -> g (f Internal)
withInternal = id

newtype Parser a = Parser (Parsec Void String a) deriving (Functor, Applicative, Monad, Alternative, MonadPlus)

parseTest (Parser p) = Megaparsec.parseTest p

parse (Parser p) = Megaparsec.parse p

parseMaybe (Parser p) = Megaparsec.parseMaybe p

instance SyntaxBase Parser where
  syntaxmap (Prism f _) p = f <$> p
  (⊗) = liftM2 (,)
  (∥) = (<|>)
  never = empty
  always = pure ()

instance Syntax Parser where
  string op = Parser $ Megaparsec.string op >> Megaparsec.space
  identifer = Parser $ do
    c <- Megaparsec.satisfy isAlpha Megaparsec.<?> "letter"
    cs <- Combinators.many (Megaparsec.satisfy isAlphaNum Megaparsec.<?> "letter or number")
    Megaparsec.space
    pure (c : cs)
  stringLiteral = Parser $ do
    Megaparsec.string "\""
    Combinators.manyTill (Megaparsec.satisfy (const True)) (Megaparsec.string "\"") <* Megaparsec.space
  _ ∥# q = q
  number = Parser $ do
    read <$> Combinators.some (Megaparsec.satisfy isNum Megaparsec.<?> "number") <* Megaparsec.space
    where
      isNum x = x `elem` ['0' .. '9']
  try (Parser m) = Parser $ Megaparsec.try m
  pick = const (∥)
  space = Parser $ pure ()
  line = Parser $ pure ()
  indent = Parser $ pure ()
  dedent = Parser $ pure ()

newtype Printer a = Printer (a -> Maybe (WriterT String (State Int) ()))

pretty (Printer p) a = snd $ fst $ (runState $ runWriterT $ fromJust $ p a) 0

prettyPrint :: Printer a -> a -> IO ()
prettyPrint p a = putStrLn $ pretty p a

instance SyntaxBase Printer where
  syntaxmap (Prism _ f) (Printer p) = Printer $ \b -> f b >>= p
  Printer p ⊗ Printer q = Printer $ \(x, y) -> liftM2 (>>) (p x) (q y)
  Printer p ∥ Printer q = Printer $ \x ->
    (p x) <|> (q x)
  never = Printer $ const Nothing
  always = Printer $ \() -> Just $ pure ()

instance Position Parser SourcePos where
  position = Parser $ Megaparsec.getSourcePos

instance Position Parser Internal where
  position = Parser $ pure Internal

instance Syntax Printer where
  string op = Printer $ \() -> Just $ tell op
  identifer = Printer $ \name -> Just $ tell name
  stringLiteral = Printer $ \str -> Just $ do
    tell "\""
    tell str
    tell "\""
  number = Printer $ \n -> Just $ tell $ show n
  try = id
  (∥#) = (∥)
  pick f (Printer left) (Printer right) = Printer $ \x -> case f x of
    True -> left x
    False -> right x
  space = Printer $ \() -> Just $ tell " "
  line = Printer $ \() -> Just $ do
    indention <- get
    tell "\n"
    sequence $ replicate indention (tell "\t")
    pure ()
  indent = Printer $ \() -> Just $ do
    indention <- get
    put $ indention + 1
    pure ()
  dedent = Printer $ \() -> Just $ do
    indention <- get
    put $ indention - 1
    pure ()

instance Position Printer Internal where
  position = Printer $ \Internal -> Just $ pure ()
