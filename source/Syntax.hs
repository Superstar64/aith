module Syntax where

import Ast.Common (Internal (..), location)
import qualified Ast.Common as Language
import qualified Ast.Kind as Language
import qualified Ast.Sort as Language
import qualified Ast.Term as Language
import qualified Ast.Type as Language
import Control.Applicative (Alternative, empty, (<|>))
import Control.Category (id, (.))
import Control.Monad (MonadPlus, guard, liftM2)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict (State, get, put, runState)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriterT, tell)
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void)
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

keywords =
  Set.fromList
    [ "multiarg",
      "existance",
      "size",
      "signedness",
      "word",
      "imaginary",
      "region",
      "pointer",
      "struct",
      "byte",
      "short",
      "int",
      "long",
      "ubyte",
      "ushort",
      "uint",
      "ulong",
      "signed",
      "unsigned",
      "inline",
      "let",
      "extern",
      "module",
      "import",
      "function",
      "uses",
      "if",
      "true",
      "false",
      "bool"
    ]

-- to allow for correct pretty printing right recursion should be limited to an equal or higher precedence level

class SyntaxBase δ => Syntax δ where
  token :: String -> δ ()
  keyword :: String -> δ ()
  identifer :: δ String
  stringLiteral :: δ String
  number :: δ Integer

  -- todo make this more general
  redundent :: Eq a => String -> δ (Maybe (a, x), (a, y)) -> δ ((a, Maybe x), y)

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

binaryToken op = space ≫ token op ≫ space

prefixKeyword word = keyword word ≫ space

binaryKeyword word = space ≫ keyword word ≫ space

betweenParens = between (token "(") (token ")")

betweenParensElse elsex e = token "(" ≫ (token ")" ≫ elsex ∥ e ≪ token ")")

betweenAngle = between (token "<") (token ">")

betweenBraces = between (token "{") (token "}")

betweenSquares = between (token "[") (token "]")

betweenBangParens = between (token "!(") (token ")")

betweenBangSquares = between (token "![") (token "]")

betweenPlusSquares = between (token "+[") (token "]")

betweenStarSquares = between (token "*[") (token "]")

betweenDoubleBraces = between (token "{{") (token "}}")

betweenDoubleSquares = between (token "[[") (token "]]")

symbol = Symbol.symbol ⊣ stringLiteral

lambdaCore e = binaryToken "=>" ≫ e

lambdaInline e = space ≫ betweenBraces e ∥ lambdaCore e

lambdaBrace e = space ≫ betweenBraces (indent ≫ line ≫ e ≪ dedent ≪ line)

lambdaMajor e = lambdaBrace e ∥ lambdaCore e

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

withInnerPosition4 core app = toPrism core . secondP app . toPrism (extractInfo $ location . fst . fst . fst)

withInnerPosition5 core app = toPrism core . secondP app . toPrism (extractInfo $ location . fst . fst . fst . fst)

path = (Path.path . swapNonEmpty) ⊣ token "/" ≫ identifer ⊗ pathTail
  where
    pathTail = cons ⊣ token "/" ≫ identifer ⊗ pathTail ∥ nil ⊣ always

semiPath = token "/" ≫ pathTail ∥ nil ⊣ always
  where
    pathTail = cons ⊣ identifer ⊗ (token "/" ≫ pathTail ∥ nil ⊣ always)

termIdentifier = Language.termIdentifier ⊣ identifer

typeIdentifier = Language.typeIdentifier ⊣ identifer

kindIdentifier = Language.kindIdentifier ⊣ identifer

auto e = just ⊣ e ∥ nothing ⊣ token "_"

sort :: Syntax δ => δ Language.Sort
sort =
  choice
    [ Language.kind ⊣ token "[" ≫ space ≫ token "]",
      Language.representation ⊣ keyword "representation",
      Language.size ⊣ keyword "size",
      Language.signedness ⊣ keyword "signedness"
    ]

kindPattern :: (Position δ p, Syntax δ) => δ (Language.Pattern Language.KindIdentifier Language.Sort p)
kindPattern = Language.pattern ⊣ position ⊗ kindIdentifier ⊗ token ":" ≫ sort

kind :: (Position δ p, Syntax δ) => δ (Language.KindSource p)
kind = kindTop
  where
    kindTop = Language.kindSource ⊣ position ⊗ choice options ∥ kindCore
      where
        options =
          [ Language.wordRep ⊣ prefixKeyword "word" ≫ kindCore
          ]

kindCore :: (Position δ p, Syntax δ) => δ (Language.KindSource p)
kindCore = Language.kindSource ⊣ position ⊗ choice options ∥ betweenParens kind
  where
    options =
      [ Language.kindVariable ⊣ kindIdentifier,
        Language.typex ⊣ token "*",
        Language.pretype ⊣ betweenPlusSquares kind,
        Language.region ⊣ keyword "region",
        Language.pointerRep ⊣ keyword "pointer",
        Language.structRep ⊣ prefixKeyword "struct" ≫ betweenParens (commaSeperatedMany kind),
        Language.byte ⊣ keyword "byte",
        Language.short ⊣ keyword "short",
        Language.int ⊣ keyword "int",
        Language.long ⊣ keyword "long",
        Language.signed ⊣ keyword "signed",
        Language.unsigned ⊣ keyword "unsigned"
      ]

kindCoreAuto :: (Position δ p, Syntax δ) => δ (Maybe (Language.KindSource p))
kindCoreAuto = auto kindCore

kindAuto :: (Position δ p, Syntax δ) => δ (Maybe (Language.KindSource p))
kindAuto = auto kind

constraint :: Syntax δ => δ Language.Constraint
constraint = Language.copy ⊣ keyword "copy" ≫ always

constraints :: Syntax δ => δ (Set Language.Constraint)
constraints = orderlessSet ⊣ (items ∥ nil ⊣ always)
  where
    items = cons ⊣ inverse nonEmpty ⊣ binaryKeyword "if" ≫ seperatedSome (constraint) (binaryToken "&")

lowerBounds :: Syntax δ => δ a -> δ [a]
lowerBounds σ = items ∥ nil ⊣ always
  where
    items = cons ⊣ inverse nonEmpty ⊣ binaryToken ">=" ≫ seperatedSome σ (binaryToken "&")

typePattern ::
  (Syntax δ, Position δ p) =>
  δ (Language.Pattern Language.TypeIdentifier (Maybe (Language.KindSource p)) p)
typePattern = Language.pattern ⊣ position ⊗ typeIdentifier ⊗ (just ⊣ token ":" ≫ kind ∥ nothing ⊣ always)

constraintBound :: Prism (((pm, c), π), σ) ((Language.Bound pm σ, c), π)
constraintBound = firstP (firstP (toPrism Language.bound)) . toPrism rotateLast3

typeFull = foldlP pair ⊣ typex ⊗ many (token "," ≫ space ≫ typex)
  where
    pair = withInnerPosition Language.typeSource Language.runtimePair

typex :: (Position δ p, Syntax δ) => δ (Language.TypeSource p)
typex = typeArrow
  where
    typeArrow = applyBinary ⊣ typeEffect ⊗ (binaryToken "->" ≫ typeArrow ⊕ always)
      where
        applyBinary = inline `branchDistribute` unit'
        inline = withInnerPosition Language.typeSource Language.inline
    typeEffect = effect `branchDistribute` unit' ⊣ typePtr ⊗ (binaryToken "@" ≫ typeCore ⊕ always)
      where
        effect = withInnerPosition Language.typeSource Language.effect

    typePtr = foldlP ptr ⊣ typeCore ⊗ many (token "*" ≫ binaryToken "@" ≫ typeCore)
      where
        ptr = withInnerPosition Language.typeSource Language.reference . toPrism swap

typeCore :: (Position δ p, Syntax δ) => δ (Language.TypeSource p)
typeCore = Language.typeSource ⊣ position ⊗ (choice options) ∥ betweenParensElse unit typeFull
  where
    unit = Language.typeSource ⊣ position ⊗ (Language.runtimeUnit ⊣ always)
    shortcut name signed size = Language.number ⊣ keyword name ≫ lit signed ⊗ lit size
      where
        lit x = just ⊣ Language.kindSource ⊣ position ⊗ (x ⊣ always)
    options =
      [ Language.typeVariable ⊣ typeIdentifier,
        shortcut "byte" Language.signed Language.byte,
        shortcut "short" Language.signed Language.short,
        shortcut "int" Language.signed Language.int,
        shortcut "long" Language.signed Language.long,
        shortcut "ubyte" Language.unsigned Language.byte,
        shortcut "ushort" Language.unsigned Language.short,
        shortcut "uint" Language.unsigned Language.int,
        shortcut "ulong" Language.unsigned Language.long,
        Language.boolean ⊣ keyword "bool",
        Language.number ⊣ token "#" ≫ kindCoreAuto ⊗ space ≫ kindCoreAuto,
        Language.explicitForall ⊣ constraintBound ⊣ token "\\/" ≫ typePattern ⊗ constraints ⊗ lowerBounds typeCore ⊗ lambdaInline typex,
        Language.ofCourse ⊣ betweenBangSquares typeFull,
        keyword "function" ≫ (funLiteral ∥ funPointer)
      ]
    rotate = associate' . secondI swap . associate
    funLiteral = Language.functionLiteralType ⊣ rotate ⊣ betweenParensElse unit typeFull ⊗ binaryToken "=>" ≫ typex ⊗ binaryKeyword "uses" ≫ typeCore
    funPointer = Language.functionPointer ⊣ rotate ⊣ token "*" ≫ betweenParensElse unit typeFull ⊗ binaryToken "=>" ≫ typex ⊗ binaryKeyword "uses" ≫ typeCore

typeFullAuto = auto typeFull

typeAuto = auto typex

typeCoreAuto = auto typeCore

newtype Scheme p = Scheme
  { runScheme ::
      [ ( p,
          Either
            ( ( Language.Pattern
                  Language.TypeIdentifier
                  (Maybe (Language.KindSource p))
                  p,
                Set Language.Constraint
              ),
              [Language.TypeSource p]
            )
            (Language.Pattern Language.KindIdentifier Language.Sort p)
        )
      ]
  }
  deriving (Show)

isoScheme = Isomorph Scheme runScheme

scheme :: (Syntax δ, Position δ p) => δ (Scheme p)
scheme = isoScheme ⊣ schema
  where
    schema = (cons ⊣ inverse nonEmpty ⊣ betweenAngle (commaSeperatedSome (position ⊗ schemeCore))) ∥ nil ⊣ always
    schemeCore = typePattern ⊗ constraints ⊗ lowerBounds typeCore ⊕ token "'" ≫ kindPattern

typeAnnotate op = just ⊣ binaryToken op ≫ typex ∥ nothing ⊣ always

termRuntimePattern :: (Position δ p, Syntax δ) => δ (Language.TermRuntimePatternSource p)
termRuntimePattern = patternPair
  where
    patternPair = foldlP pair ⊣ patternCore ⊗ many (token "," ≫ space ≫ patternCore)
      where
        pair = withInnerPosition Language.termRuntimePatternSource Language.runtimePatternPair
    patternCore = Language.termRuntimePatternSource ⊣ position ⊗ choice options ∥ betweenParensElse unit termRuntimePattern
      where
        unit = Language.termRuntimePatternSource ⊣ position ⊗ (Language.runtimePatternUnit ⊣ always)
        options =
          [ Language.runtimePatternVariable ⊣ termIdentifier ⊗ typeAnnotate "::"
          ]

termPattern :: (Position δ p, Syntax δ) => δ (Language.TermPatternSource p)
termPattern = patternCore
  where
    patternCore = Language.termPatternSource ⊣ position ⊗ choice options ∥ betweenParens termPattern
      where
        options =
          [ Language.patternVariable ⊣ termIdentifier ⊗ typeAnnotate ":",
            Language.patternOfCourse ⊣ betweenBangSquares termPattern
          ]

termFull = termPair
  where
    termPair = foldlP pair ⊣ termAnnotate ⊗ many (token "," ≫ space ≫ termAnnotate)
      where
        pair = withInnerPosition Language.termSource Language.runtimePairIntrouction
    termAnnotate = apply ⊣ term ⊗ (binaryToken "::" ≫ typeAuto ⊕ binaryToken ":" ≫ typeAuto ⊕ always)
      where
        apply = preAnnotate `branchDistribute` annotate `branchDistribute` unit'
        annotate = withInnerPosition Language.termSource Language.typeAnnotation
        preAnnotate = withInnerPosition Language.termSource Language.preTypeAnnotation

term :: (Position δ p, Syntax δ) => δ (Language.TermSource p)
term = termBinding
  where
    termBinding = Language.termSource ⊣ position ⊗ choice options ∥ termRTApply
      where
        options =
          [ Language.bind ⊣ rotateBind ⊣ prefixKeyword "inline" ≫ termPattern ≪ binaryToken "=" ⊗ term ≪ token ";" ≪ line ⊗ term,
            Language.alias ⊣ rotateBind ⊣ prefixKeyword "let" ≫ termRuntimePattern ≪ binaryToken "=" ⊗ term ≪ token ";" ≪ line ⊗ term,
            Language.ifx ⊣ prefixKeyword "if" ≫ termCore ⊗ lambdaBrace term ≪ binaryKeyword "else" ⊗ lambdaBrace term
          ]
        rotateBind = secondI Language.bound . associate . firstI swap
    termRTApply = applyBinary ⊣ termAdd ⊗ (binaryToken "$" ≫ termRTApply ⊕ always)
      where
        applyBinary = apply `branchDistribute` unit'
        apply = withInnerPosition Language.termSource Language.functionApplication
    termAdd = foldlP applyAdd ⊣ termMul ⊗ many (binaryToken "+" ≫ termMul ⊕ binaryToken "-" ≫ termMul)
      where
        applyAdd = add `branchDistribute` sub
        add = withInnerPosition Language.termSource (Language.arithmatic Language.Addition)
        sub = withInnerPosition Language.termSource (Language.arithmatic Language.Subtraction)
    termMul = foldlP applyMul ⊣ termApply ⊗ many (binaryToken "*" ≫ termApply ⊕ binaryToken "/" ≫ termApply)
      where
        applyMul = mul `branchDistribute` div
        mul = withInnerPosition Language.termSource (Language.arithmatic Language.Multiplication)
        div = withInnerPosition Language.termSource (Language.arithmatic Language.Division)
    termApply = Language.termSource ⊣ position ⊗ choice options ∥ foldlP applyBinary ⊣ termCore ⊗ many (applySyntax ⊕ typeApplySyntax)
      where
        applyBinary = application `branchDistribute` typeApplication
        application = withInnerPosition Language.termSource Language.inlineApplication
        typeApplication = withInnerPosition Language.termSource Language.typeApplication
        applySyntax = space ≫ token "`" ≫ termCore
        typeApplySyntax = space ≫ betweenAngle typeAuto
        options =
          [ Language.readReference ⊣ token "*" ≫ termApply
          ]

termCore :: (Position δ p, Syntax δ) => δ (Language.TermSource p)
termCore = Language.termSource ⊣ position ⊗ choice options ∥ betweenParensElse unit termFull
  where
    unit = Language.termSource ⊣ position ⊗ (Language.runtimeUnitIntroduction ⊣ always)
    unit' = Language.termRuntimePatternSource ⊣ position ⊗ (Language.runtimePatternUnit ⊣ always)
    options =
      [ Language.variable ⊣ termIdentifier ⊗ always,
        Language.inlineAbstraction ⊣ Language.bound ⊣ token "\\" ≫ termPattern ⊗ lambdaMajor term,
        Language.functionLiteral ⊣ Language.bound ⊣ keyword "function" ≫ betweenParensElse unit' termRuntimePattern ⊗ lambdaMajor term,
        Language.extern ⊣ extern,
        Language.ofCourseIntroduction ⊣ betweenBangSquares termFull,
        Language.numberLiteral ⊣ number,
        Language.typeLambda ⊣ constraintBound ⊣ token "/\\" ≫ typePattern ⊗ constraints ⊗ lowerBounds typeCoreAuto ⊗ lambdaMajor term,
        Language.truex ⊣ keyword "true",
        Language.falsex ⊣ keyword "false"
      ]
    externHeader = prefixKeyword "extern" ≫ symbol ≪ space ≪ keyword "function"
    extern = swapLast2 ⊣ externHeader ⊗ betweenParens typeFullAuto ≪ binaryToken "=>" ⊗ typeAuto ≪ binaryKeyword "uses" ⊗ typeCoreAuto

modulex ::
  (Syntax δ, Position δ p) =>
  δ (Module.Module (Module.GlobalSource p))
modulex =
  Module.coreModule ⊣ orderless ⊣ list
    ⊣ some
      (item identifer (binaryToken "=") (token ";" ≫ line) (token ";" ≫ line) lambdaMajor)
    ⊕ never

item ::
  forall a δ p.
  (Position δ p, Syntax δ, Eq a) =>
  δ a ->
  δ () ->
  δ () ->
  δ () ->
  (δ (Module.Module (Module.GlobalSource p)) -> δ (Module.Module (Module.GlobalSource p))) ->
  δ (a, Module.Item (Module.GlobalSource p))
item name delimit footer footer' lambda =
  choice
    [ itemCore (keyword "module" ≫ space) (Module.modulex ⊣ lambda modulex),
      itemTerm (keyword "inline" ≫ space) (Module.global . Module.inline),
      itemCore (keyword "import" ≫ space) (Module.global . Module.importx ⊣ position ⊗ path),
      itemTerm always (Module.global . Module.text)
    ]
  where
    itemCore brand inner = brand ≫ name ≪ delimit ⊗ inner ≪ footer
    itemTerm :: δ () -> Prism (Maybe (Language.TypeSchemeSource p), Language.TermSchemeSource p) b -> δ (a, b)
    itemTerm brand wrap = secondP wrap ⊣ associate ⊣ item
      where
        item =
          redundent "Type annotation doesn't match definition" $
            firstI (imap $ secondI applyType . associate)
              ⊣ secondI (secondI applyTerm . associate)
              ⊣ declaration
        declaration = branch applyAnnotated applyPlain ⊣ distribute ⊣ header ⊗ (annotated ⊕ plain)
        applyAnnotated = firstP just . toPrism associate'
        applyPlain = firstP nothing . toPrism (inverse unit)
        annotated = annotate ≪ footer' ⊗ (header ⊗ binding ≪ footer)
        plain = binding ≪ footer
        header = brand ≫ name ⊗ scheme
        annotate = Language.typeSchemeSource ⊣ position ⊗ (Language.monoType ⊣ binaryToken ":" ≫ typex)
        binding = Language.termSchemeSource ⊣ position ⊗ (Language.monoTerm ⊣ delimit ≫ term)

        applyType = apply Language.typeSchemeSource Language.forallx Language.kindForall
        applyTerm = apply Language.termSchemeSource Language.implicitTypeAbstraction Language.implicitKindAbstraction
        apply c t k =
          foldrP
            ( toPrism c
                . secondP
                  ((t . constraintBound) `branchDistribute'` (k . toPrism Language.bound))
                . toPrism associate
            )
            . firstI (inverse isoScheme)

itemSingleton ::
  (Syntax δ, Position δ p) => δ (Module.Item (Module.GlobalSource p))
itemSingleton = unit ⊣ item always (token ":::" ≫ line) always (token ";" ≫ line) id

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
  token op = Parser $ Megaparsec.string op >> Megaparsec.space
  keyword string = Parser $ do
    Megaparsec.label string $
      Megaparsec.try $ do
        c <- Megaparsec.letterChar
        cs <- Megaparsec.many Megaparsec.alphaNumChar
        guard $ (c : cs) == string
    Megaparsec.space
    pure ()
  identifer = Parser $ do
    str <- Megaparsec.label "identifer" $
      Megaparsec.try $ do
        c <- Megaparsec.letterChar
        cs <- Megaparsec.many Megaparsec.alphaNumChar
        guard $ (c : cs) `Set.notMember` keywords
        pure (c : cs)
    Megaparsec.space
    pure str
  stringLiteral = Parser $ do
    Megaparsec.string "\""
    Megaparsec.manyTill (Megaparsec.satisfy (const True)) (Megaparsec.string "\"") <* Megaparsec.space
  _ ∥# q = q
  number = Parser $ do
    read <$> Megaparsec.some (Megaparsec.satisfy isNum Megaparsec.<?> "number") <* Megaparsec.space
    where
      isNum x = x `elem` ['0' .. '9']
  try (Parser m) = Parser $ Megaparsec.try m
  pick = const (∥)
  space = Parser $ pure ()
  line = Parser $ pure ()
  indent = Parser $ pure ()
  dedent = Parser $ pure ()
  redundent message (Parser p) = Parser $ do
    v <- p
    case v of
      (Nothing, (a, y)) -> pure ((a, Nothing), y)
      (Just (a, _), (a', _)) | a /= a' -> fail message
      (Just (a, x), (_, y)) | otherwise -> pure ((a, Just x), y)

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
  token op = Printer $ \() -> Just $ tell op
  keyword name = Printer $ \() -> Just $ tell name

  -- todo invert syntax for pretty printing keywords as identifers
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
    indention <- lift $ get
    tell "\n"
    sequence $ replicate indention (tell "\t")
    pure ()
  indent = Printer $ \() -> Just $ do
    indention <- lift $ get
    lift $ put $ indention + 1
    pure ()
  dedent = Printer $ \() -> Just $ do
    indention <- lift $ get
    lift $ put $ indention - 1
    pure ()
  redundent _ (Printer f) = Printer $ \case
    ((a, Nothing), y) -> f (Nothing, (a, y))
    ((a, Just x), y) -> f (Just (a, x), (a, y))

instance Position Printer Internal where
  position = Printer $ \Internal -> Just $ pure ()
