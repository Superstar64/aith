module Syntax where

import Ast.Common (Internal (..), location)
import qualified Ast.Common as Language
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
      "region",
      "pointer",
      "struct",
      "integer",
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
      "io",
      "in",
      "capacity",
      "unique",
      "as",
      "borrow",
      "invariant",
      "subtypable",
      "substitutability"
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

betweenPipeAngles = between (token "|<") (token ">|")

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

termGlobalIdentifier = Language.termGlobalIdentifier ⊣ path

typeIdentifier = Language.typeIdentifier ⊣ identifer

auto e = just ⊣ e ∥ nothing ⊣ token "_"

kindPattern = Language.kindPatternSource ⊣ position ⊗ typeIdentifier ⊗ sort
  where
    sort = just ⊣ token ":" ≫ typex ∥ nothing ⊣ always

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
  δ (Language.TypePatternSource p)
typePattern =
  Language.typePatternSource ⊣ position ⊗ typeIdentifier ⊗ k ⊗ constraints ⊗ (lowerBounds typeCore)
  where
    k = just ⊣ token ":" ≫ typex ∥ nothing ⊣ always

typeFull = foldlP pair ⊣ typex ⊗ many (token "," ≫ space ≫ typex)
  where
    pair = withInnerPosition Language.typeSource Language.pair

typex :: (Position δ p, Syntax δ) => δ (Language.TypeSource p)
typex = typeLambda
  where
    typeLambda = Language.typeSource ⊣ position ⊗ poly ∥ typeArrow
      where
        poly = Language.poly ⊣ wrapType ⊣ scheme ≪ space ⊗ typeLambda
    typeArrow = applyBinary ⊣ typeEffect ⊗ (binaryToken "->" ≫ typeArrow ⊕ always)
      where
        applyBinary = inline `branchDistribute` unit'
        inline = withInnerPosition Language.typeSource Language.inline
    typeEffect = effect `branchDistribute` unit' ⊣ typeUnique ⊗ (binaryKeyword "in" ≫ typeCore ⊕ always)
      where
        effect = withInnerPosition Language.typeSource Language.effect
    typeUnique = Language.typeSource ⊣ position ⊗ unique ∥ typePtr
      where
        unique = Language.unique ⊣ prefixKeyword "unique" ≫ typePtr
    typePtr = foldlP apply ⊣ typeInt ⊗ many (betweenSquares typex ⊕ binaryToken "@" ≫ typeInt)
      where
        apply = ptr `branchDistribute` shared
        ptr = withInnerPosition Language.typeSource Language.pointer
        shared = withInnerPosition Language.typeSource Language.shared
    typeInt = integers ∥# apply ⊣ kindWord ⊗ (space ≫ keyword "integer" ≫ betweenParens typex ⊕ always)
      where
        apply = num `branchDistribute` unit'
        num = withInnerPosition Language.typeSource Language.number
    kindWord = (word `branchDistribute` unit') ⊣ typeCore ⊗ (space ≫ keyword "word" ⊕ always)
      where
        word = withInnerPosition1 Language.typeSource Language.wordRep

integers =
  Language.typeSource ⊣ position
    ⊗ choice
      [ shortcut "byte" Language.signed Language.byte,
        shortcut "short" Language.signed Language.short,
        shortcut "int" Language.signed Language.int,
        shortcut "long" Language.signed Language.long,
        shortcut "ubyte" Language.unsigned Language.byte,
        shortcut "ushort" Language.unsigned Language.short,
        shortcut "uint" Language.unsigned Language.int,
        shortcut "ulong" Language.unsigned Language.long
      ]
  where
    shortcut name signed size = Language.number ⊣ keyword name ≫ lit signed ⊗ lit size
      where
        lit x = Language.typeSource ⊣ position ⊗ (x ⊣ always)

typeCore :: (Position δ p, Syntax δ) => δ (Language.TypeSource p)
typeCore = Language.typeSource ⊣ position ⊗ (choice options) ∥ integers ∥ betweenParensElse unit typeFull
  where
    unit = Language.typeSource ⊣ position ⊗ (Language.unit ⊣ always)
    options =
      [ Language.typeVariable ⊣ typeIdentifier,
        Language.boolean ⊣ keyword "bool",
        Language.world ⊣ keyword "io",
        Language.ofCourse ⊣ betweenBangSquares typeFull,
        keyword "function" ≫ (funLiteral ∥ funPointer),
        Language.wildCard ⊣ token ":",
        Language.typex ⊣ token "*",
        Language.pretype ⊣ betweenPlusSquares typex,
        Language.boxed ⊣ token "-",
        Language.region ⊣ keyword "region",
        Language.pointerRep ⊣ keyword "pointer",
        Language.structRep ⊣ prefixKeyword "struct" ≫ betweenParens (commaSeperatedMany typex),
        Language.byte ⊣ token "8bit",
        Language.short ⊣ token "16bit",
        Language.int ⊣ token "32bit",
        Language.long ⊣ token "64bit",
        Language.native ⊣ keyword "native",
        Language.signed ⊣ keyword "signed",
        Language.unsigned ⊣ keyword "unsigned",
        Language.capacity ⊣ keyword "capacity",
        Language.kind ⊣ betweenSquares typex,
        Language.representation ⊣ keyword "representation",
        Language.size ⊣ keyword "size",
        Language.signedness ⊣ keyword "signedness",
        Language.sort ⊣ token "/\\",
        Language.invariant ⊣ keyword "invariant",
        Language.subtypable ⊣ keyword "subtypable",
        Language.substitutability ⊣ keyword "substitutability"
      ]
    rotate = associate' . secondI swap . associate
    funLiteral = Language.functionLiteralType ⊣ rotate ⊣ betweenParensElse unit typeFull ⊗ binaryToken "=>" ≫ typex ⊗ binaryKeyword "uses" ≫ typeCore
    funPointer = Language.functionPointer ⊣ rotate ⊣ token "*" ≫ betweenParensElse unit typeFull ⊗ binaryToken "=>" ≫ typex ⊗ binaryKeyword "uses" ≫ typeCore

typeAuto = auto typex

newtype Scheme p = Scheme
  { runScheme ::
      [ ( p,
          Either
            (Language.TypePatternSource p)
            (Language.KindPatternSource p)
        )
      ]
  }
  deriving (Show)

isoScheme = Isomorph Scheme runScheme

scheme :: (Syntax δ, Position δ p) => δ (Scheme p)
scheme = isoScheme ⊣ schema
  where
    schema = betweenAngle $ cons ⊣ inverse nonEmpty ⊣ commaSeperatedSome (position ⊗ schemeCore) ∥ nil ⊣ always
    schemeCore = typePattern ⊕ token "'" ≫ kindPattern

wrapType :: Isomorph (Scheme p, Language.TypeSource p) (Language.TypeSchemeSource p)
wrapType =
  wrap Language.typeSchemeSource Language.typeForall Language.kindForall
    . secondI
      (assumeIsomorph (toPrism Language.typeSchemeSource . secondP Language.monoType) . extractInfo location)

wrapTerm :: Isomorph (Scheme p, Language.TermSource p) (Language.TermSchemeSource p)
wrapTerm =
  wrap Language.termSchemeSource Language.typeAbstraction Language.kindAbstraction
    . secondI
      (assumeIsomorph (toPrism Language.termSchemeSource . secondP Language.monoTerm) . extractInfo location)

wrap c t k =
  foldrP
    ( toPrism c
        . secondP
          ((t . toPrism Language.bound) `branchDistribute'` (k . toPrism Language.bound))
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
term = termLambda
  where
    termLambda = Language.termSource ⊣ position ⊗ lambda ∥ termOr
      where
        lambda = Language.polyIntroduction ⊣ wrapTerm ⊣ scheme ≪ space ⊗ term
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
    termApply = foldlP applyBinary ⊣ termCore ⊗ many (applySyntax ⊕ rtApplySyntax)
      where
        applyBinary = application `branchDistribute` rtApplication
        application = withInnerPosition Language.termSource Language.inlineApplication
        rtApplication = withInnerPosition Language.termSource Language.functionApplication
        applySyntax = space ≫ token "`" ≫ termCore
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
      [ Language.variable ⊣ termIdentifier,
        Language.globalVariable ⊣ termGlobalIdentifier,
        Language.inlineAbstraction ⊣ Language.bound ⊣ token "\\" ≫ termPattern ⊗ termLambda,
        Language.functionLiteral ⊣ Language.bound ⊣ keyword "function" ≫ betweenParensElse unit' termRuntimePattern ⊗ termLambda,
        Language.extern ⊣ prefixKeyword "extern" ≫ symbol,
        Language.ofCourseIntroduction ⊣ betweenBangSquares termFull,
        Language.numberLiteral ⊣ number,
        Language.truex ⊣ keyword "true",
        Language.falsex ⊣ keyword "false",
        borrow,
        Language.polyElimination ⊣ betweenPipeAngles termFull
      ]
    borrow = Language.borrow ⊣ prefixKeyword "borrow" ≫ termCore ⊗ binaryKeyword "as" ≫ binding
      where
        binding = Language.bound ⊣ betweenAngle typePattern ⊗ binding'
          where
            binding' = Language.bound ⊣ betweenParens termRuntimePattern ⊗ lambdaBrace termStatement

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
      itemTerm always (Module.global . Module.text)
    ]
  where
    itemCore brand inner = brand ≫ name ≪ delimit ⊗ inner ≪ footer
    itemTerm :: δ () -> Prism (Maybe (Language.TypeSchemeSource p), Language.TermControlSource p) b -> δ (a, b)
    itemTerm brand wrap = secondP wrap ⊣ associate ⊣ item
      where
        item =
          redundent "Type annotation doesn't match definition" declaration

        declaration :: δ (Maybe (a, Language.TypeSchemeSource p), (a, Language.TermControlSource p))
        declaration = typed `branchDistribute` semiAutomatic `branchDistribute` auto ⊣ decleration'
          where
            decleration' = brand ≫ name ⊗ (signatured ⊕ plain)
              where
                signatured = otherwise `branchDistribute` semiAutomatic ⊣ scheme ⊗ (annotated ⊕ plain)
                  where
                    semiAutomatic = right . toPrism wrapTerm
                    otherwise = left . toPrism (firstI wrapType . associate')

                    annotated :: δ (Language.TypeSource p, (a, Language.TermControlSource p))
                    annotated = binaryToken ":" ≫ typex ≪ footer' ⊗ (brand ≫ name ⊗ (manual ∥ scoped) ≪ footer)
                      where
                        manual = Language.termManualSource ⊣ wrapTerm ⊣ scheme ⊗ binding
                        scoped = Language.termAutoSource ⊣ binding
            notype = firstP nothing . toPrism (inverse unit)
            semiAutomatic = notype . secondP Language.termManualSource
            auto = notype . secondP Language.termAutoSource
            typed = firstP just . toPrism associate'

        plain :: δ (Language.TermSource p)
        plain = binding ≪ footer

        binding :: δ (Language.TermSource p)
        binding = delimit ≫ term

itemSingleton ::
  (Syntax δ, Position δ p) => δ (Module.Item (Module.GlobalSource p))
itemSingleton = unit ⊣ item always (token "::" ≫ line) always (token ";" ≫ line) id

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
