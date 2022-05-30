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
      "else",
      "true",
      "false",
      "bool",
      "copy",
      "representation",
      "native",
      "ptrdiff",
      "io",
      "in",
      "capacity"
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

betweenTickAngle = between (token "`<") (token ">")

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

lambdaBrace e = space ≫ betweenBraces (indent ≫ line ≫ e ≪ dedent ≪ line)

lambda' e e' = lambdaBrace e ∥ lambdaCore e'

lambda e = lambda' e e

commaSome e = some (token "," ≫ space ≫ e)

commaSeperatedMany e = seperatedMany e (token "," ≫ space)

commaSeperatedSome e = seperatedSome e (token "," ≫ space)

multiarg core = multiargExclusionary core ∥ singleton ⊣ core

-- excludes single argument multiargs
multiargExclusionary :: Syntax p => p a -> p [a]
multiargExclusionary core = apply ⊣ keyword "multiarg" ≫ betweenParens (core ⊗ token "," ≫ space ≫ commaSeperatedSome core ⊕ always)
  where
    apply = branch (cons . secondP (cons . toPrism (inverse nonEmpty))) nil

withInnerPosition1 core app = toPrism core . secondP app . toPrism (extractInfo $ location) . toPrism unit'

withInnerPosition core app = toPrism core . secondP app . toPrism (extractInfo $ location . fst)

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
        Language.boxed ⊣ token "-",
        Language.region ⊣ keyword "region",
        Language.pointerRep ⊣ keyword "pointer",
        Language.structRep ⊣ prefixKeyword "struct" ≫ betweenParens (commaSeperatedMany kind),
        Language.byte ⊣ keyword "byte",
        Language.short ⊣ keyword "short",
        Language.int ⊣ keyword "int",
        Language.long ⊣ keyword "long",
        Language.native ⊣ keyword "native",
        Language.signed ⊣ keyword "signed",
        Language.unsigned ⊣ keyword "unsigned",
        Language.capacity ⊣ keyword "capacity"
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
    pair = withInnerPosition Language.typeSource Language.pair

typex :: (Position δ p, Syntax δ) => δ (Language.TypeSource p)
typex = typeLambda
  where
    typeLambda = Language.typeSource ⊣ position ⊗ typeLambda ∥ typeArrow
      where
        apply = Language.explicitForall . constraintBound
        typeLambda = apply ⊣ token "\\/" ≫ typePattern ⊗ constraints ⊗ lowerBounds typeCore ⊗ lambdaCore typex
    typeArrow = applyBinary ⊣ typeEffect ⊗ (binaryToken "->" ≫ typeArrow ⊕ always)
      where
        applyBinary = inline `branchDistribute` unit'
        inline = withInnerPosition Language.typeSource Language.inline
    typeEffect = effect `branchDistribute` unit' ⊣ typePtr ⊗ (binaryKeyword "in" ≫ typeCore ⊕ always)
      where
        effect = withInnerPosition Language.typeSource Language.effect
    typePtr = foldlP apply ⊣ typeCore ⊗ many (betweenSquares typeCore ⊕ binaryToken "@" ≫ typeCore)
      where
        apply = ptr `branchDistribute` shared
        ptr = withInnerPosition Language.typeSource Language.pointer
        shared = withInnerPosition Language.typeSource Language.shared

typeCore :: (Position δ p, Syntax δ) => δ (Language.TypeSource p)
typeCore = Language.typeSource ⊣ position ⊗ (choice options) ∥ betweenParensElse unit typeFull
  where
    unit = Language.typeSource ⊣ position ⊗ (Language.unit ⊣ always)
    shortcut name signed size = Language.number ⊣ keyword name ≫ lit signed ⊗ lit size
      where
        lit x = just ⊣ Language.kindSource ⊣ position ⊗ (x ⊣ always)
    options =
      [ Language.typeVariable ⊣ typeIdentifier,
        shortcut "byte" Language.signed Language.byte,
        shortcut "short" Language.signed Language.short,
        shortcut "int" Language.signed Language.int,
        shortcut "long" Language.signed Language.long,
        shortcut "ptrdiff" Language.signed Language.native,
        shortcut "ubyte" Language.unsigned Language.byte,
        shortcut "ushort" Language.unsigned Language.short,
        shortcut "uint" Language.unsigned Language.int,
        shortcut "ulong" Language.unsigned Language.long,
        shortcut "native" Language.unsigned Language.native,
        Language.boolean ⊣ keyword "bool",
        Language.world ⊣ keyword "io",
        Language.number ⊣ token "#" ≫ kindCoreAuto ⊗ space ≫ kindCoreAuto,
        Language.ofCourse ⊣ betweenBangSquares typeFull,
        keyword "function" ≫ (funLiteral ∥ funPointer),
        Language.wildCard ⊣ token "*"
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
    schema = betweenAngle $ cons ⊣ inverse nonEmpty ⊣ commaSeperatedSome (position ⊗ schemeCore) ∥ nil ⊣ always
    schemeCore = typePattern ⊗ constraints ⊗ lowerBounds typeCore ⊕ token "'" ≫ kindPattern

wrapType :: Isomorph (Scheme p, Language.TypeSource p) (Language.TypeSchemeSource p)
wrapType =
  wrap Language.typeSchemeSource Language.forallx Language.kindForall
    . secondI
      (assumeIsomorph (toPrism Language.typeSchemeSource . secondP Language.monoType) . extractInfo location)

wrapTerm :: Isomorph (Scheme p, Language.TermSource p) (Language.TermSchemeSource p)
wrapTerm =
  wrap Language.termSchemeSource Language.implicitTypeAbstraction Language.implicitKindAbstraction
    . secondI
      (assumeIsomorph (toPrism Language.termSchemeSource . secondP Language.monoTerm) . extractInfo location)

wrap c t k =
  foldrP
    ( toPrism c
        . secondP
          ((t . constraintBound) `branchDistribute'` (k . toPrism Language.bound))
        . toPrism associate
    )
    . firstI (inverse isoScheme)

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
        pair = withInnerPosition Language.termSource Language.pairIntroduction
    termAnnotate = apply ⊣ termStatement ⊗ (binaryToken "::" ≫ typeAuto ⊕ binaryToken ":" ≫ typeAuto ⊕ always)
      where
        apply = preAnnotate `branchDistribute` annotate `branchDistribute` unit'
        annotate = withInnerPosition Language.termSource Language.typeAnnotation
        preAnnotate = withInnerPosition Language.termSource Language.preTypeAnnotation

termStatement :: (Position δ p, Syntax δ) => δ (Language.TermSource p)
termStatement = Language.termSource ⊣ position ⊗ choice options ∥ apply ⊣ term ⊗ (token ";" ≫ termStatement ⊕ always)
  where
    options =
      [ Language.bind ⊣ rotateBind ⊣ prefixKeyword "inline" ≫ termPattern ≪ binaryToken "=" ⊗ term ≪ token ";" ≪ line ⊗ termStatement,
        Language.alias ⊣ rotateBind ⊣ prefixKeyword "let" ≫ termRuntimePattern ≪ binaryToken "=" ⊗ term ≪ token ";" ≪ line ⊗ termStatement,
        Language.ifx ⊣ prefixKeyword "if" ≫ termCore ⊗ lambdaBrace termStatement ≪ binaryKeyword "else" ⊗ lambdaBrace termStatement
      ]
    rotateBind = secondI Language.bound . associate . firstI swap
    apply = withInnerPosition Language.termSource Language.dox `branchDistribute` unit'

term :: (Position δ p, Syntax δ) => δ (Language.TermSource p)
term = termOr
  where
    termOr = foldlP apply ⊣ termAnd ⊗ many (binaryToken "|" ≫ termAnd)
      where
        apply = withInnerPosition Language.termSource Language.or
    termAnd = foldlP apply ⊣ termEqual ⊗ many (binaryToken "&" ≫ termEqual)
      where
        apply = withInnerPosition Language.termSource Language.and
    termEqual = apply ⊣ termAdd ⊗ operators
      where
        i o = withInnerPosition Language.termSource (Language.relational o)
        r op = binaryToken op ≫ termAdd
        b = branchDistribute
        apply = equal `b` notEqual `b` lessThenEqual `b` lessThen `b` greaterThenEqual `b` greaterThen `b` unit'
          where
            equal = i Language.Equal
            notEqual = i Language.NotEqual
            lessThen = i Language.LessThen
            lessThenEqual = i Language.LessThenEqual
            greaterThen = i Language.GreaterThen
            greaterThenEqual = i Language.GreaterThenEqual

        operators = r "==" ⊕ r "!=" ⊕ r "<=" ⊕ r "<" ⊕ r ">=" ⊕ r ">" ⊕ always

    termAdd = foldlP applyAdd ⊣ termMul ⊗ many (binaryToken "+" ≫ termMul ⊕ binaryToken "-" ≫ termMul)
      where
        applyAdd = add `branchDistribute` sub
        add = withInnerPosition Language.termSource (Language.arithmatic Language.Addition)
        sub = withInnerPosition Language.termSource (Language.arithmatic Language.Subtraction)
    termMul = foldlP applyMul ⊣ termDeref ⊗ many (binaryToken "*" ≫ termDeref ⊕ binaryToken "/" ≫ termDeref)
      where
        applyMul = mul `branchDistribute` div
        mul = withInnerPosition Language.termSource (Language.arithmatic Language.Multiplication)
        div = withInnerPosition Language.termSource (Language.arithmatic Language.Division)
    termDeref = Language.termSource ⊣ position ⊗ deref ∥ termPrefix
      where
        apply = branchDistribute (Language.writeReference) (Language.readReference . toPrism unit')
        deref = apply ⊣ token "*" ≫ termPrefix ⊗ (binaryToken "=" ≫ termCore ⊕ always)
    termPrefix = Language.termSource ⊣ position ⊗ options ∥ termIndex
      where
        options =
          choice
            [ Language.readReference ⊣ token "*" ≫ termPrefix,
              -- todo add proper lexer for tokens and use ! here
              Language.not ⊣ token "~" ≫ termPrefix
            ]
    termIndex = Language.termSource ⊣ position ⊗ index ∥ termApply
      where
        index = Language.pointerIncrement ⊣ token "&" ≫ termApply ⊗ betweenSquares term
    termApply = foldlP applyBinary ⊣ termCore ⊗ many (typeApplySyntax ⊕ applySyntax ⊕ rtApplySyntax)
      where
        applyBinary = typeApplication `branchDistribute` application `branchDistribute` rtApplication
        application = withInnerPosition Language.termSource Language.inlineApplication
        typeApplication = withInnerPosition Language.termSource Language.typeApplication
        rtApplication = withInnerPosition Language.termSource Language.functionApplication
        applySyntax = space ≫ token "`" ≫ termCore
        typeApplySyntax = space ≫ betweenTickAngle typeAuto
        rtApplySyntax = space ≫ betweenParensElse unit termFull
          where
            unit = Language.termSource ⊣ position ⊗ (Language.unitIntroduction ⊣ always)

termLambda = lambda' termStatement term

termCore :: (Position δ p, Syntax δ) => δ (Language.TermSource p)
termCore = Language.termSource ⊣ position ⊗ choice options ∥ betweenParensElse unit termFull
  where
    unit = Language.termSource ⊣ position ⊗ (Language.unitIntroduction ⊣ always)
    unit' = Language.termRuntimePatternSource ⊣ position ⊗ (Language.runtimePatternUnit ⊣ always)
    options =
      [ Language.variable ⊣ termIdentifier ⊗ always,
        Language.inlineAbstraction ⊣ Language.bound ⊣ token "\\" ≫ termPattern ⊗ termLambda,
        Language.functionLiteral ⊣ Language.bound ⊣ keyword "function" ≫ betweenParensElse unit' termRuntimePattern ⊗ termLambda,
        Language.extern ⊣ prefixKeyword "extern" ≫ symbol,
        Language.ofCourseIntroduction ⊣ betweenBangSquares termFull,
        Language.numberLiteral ⊣ number,
        Language.typeLambda ⊣ constraintBound ⊣ token "/\\" ≫ typePattern ⊗ constraints ⊗ lowerBounds typeCoreAuto ⊗ termLambda,
        Language.truex ⊣ keyword "true",
        Language.falsex ⊣ keyword "false"
      ]

modulex ::
  (Syntax δ, Position δ p) =>
  δ (Module.Module (Module.GlobalSource p))
modulex =
  Module.coreModule ⊣ orderless ⊣ list
    ⊣ some
      (item identifer (binaryToken "=") (token ";" ≫ line) (token ";" ≫ line) lambda)
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
    itemTerm :: δ () -> Prism (Maybe (Language.TypeSchemeSource p), Language.TermControlSource p) b -> δ (a, b)
    itemTerm brand wrap = secondP wrap ⊣ associate ⊣ item
      where
        item =
          redundent "Type annotation doesn't match definition" $
            firstI (imap $ secondI wrapType . associate)
              ⊣ secondI (secondI applyControl . associate)
              ⊣ declaration

        applyControl :: Isomorph (Maybe (Scheme p), Language.TermSource p) (Language.TermControlSource p)
        applyControl = assumeIsomorph $ (auto `branchDistribute` manual) . toPrism swap . firstP (toPrism $ inverse maybe')
          where
            auto = Language.termAutoSource . toPrism unit . toPrism swap
            manual = Language.termManualSource . toPrism wrapTerm . toPrism swap

        declaration :: δ (Maybe ((a, Scheme p), Language.TypeSource p), ((a, Maybe (Scheme p)), Language.TermSource p))
        declaration = apply ⊣ brand ≫ name ⊗ (scheme ⊗ (annotated ⊕ plain) ⊕ plain)

        apply = ((applyManualFull `branchDistribute` applyManualLite) . toPrism associate') `branchDistribute` applyAuto
        applyManualFull = secondP (firstP (secondP just)) . firstP just . toPrism associate'
        applyManualLite = firstP nothing . toPrism (inverse unit) . firstP (secondP just)
        applyAuto = firstP nothing . toPrism (inverse unit) . firstP (secondP nothing . toPrism (inverse unit'))

        annotated :: δ (Language.TypeSource p, ((a, Scheme p), Language.TermSource p))
        annotated = annotate ≪ footer' ⊗ (brand ≫ name ⊗ scheme ⊗ binding ≪ footer)

        plain :: δ (Language.TermSource p)
        plain = binding ≪ footer

        annotate :: δ (Language.TypeSource p)
        annotate = binaryToken ":" ≫ typex

        binding :: δ (Language.TermSource p)
        binding = delimit ≫ term

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
  keyword name | name `Set.member` keywords = Parser $ do
    Megaparsec.label name $
      Megaparsec.try $ do
        c <- Megaparsec.letterChar
        cs <- Megaparsec.many Megaparsec.alphaNumChar
        guard $ (c : cs) == name
    Megaparsec.space
    pure ()
  keyword name = error $ "bad keyword: " ++ name
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
  keyword name | name `Set.member` keywords = Printer $ \() -> Just $ tell name
  keyword name = error $ "bad keyword: " ++ name

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
