module Syntax where

import qualified Ast.Surface as Language
import qualified Ast.Symbol as Language
import Control.Applicative (Alternative, empty, (<|>))
import Control.Category (id, (.))
import Control.Monad (MonadPlus, guard, liftM2)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict (State, get, put, runState)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriterT, tell)
import Data.Foldable (asum)
import Data.List (isPrefixOf)
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Data.Void (Void)
import Misc.Isomorph
import Misc.Prism
import Misc.Syntax
import Text.Megaparsec (Parsec, SourcePos)
import qualified Text.Megaparsec as Megaparsec
import qualified Text.Megaparsec.Char as Megaparsec
import Prelude hiding (id, (.))

-- Invertable Syntax Descriptions
-- https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf

infixl 3 ∥#

keywords =
  Set.fromList
    [ "ambiguous",
      "as",
      "bool",
      "boxed",
      "break",
      "byte",
      "capacity",
      "cast",
      "continue",
      "copy",
      "else",
      "existance",
      "extern",
      "false",
      "function",
      "if",
      "in",
      "inline",
      "int",
      "integer",
      "internal",
      "syntactic",
      "io",
      "kind",
      "label",
      "let",
      "linear",
      "long",
      "loop",
      "multiarg",
      "multiplicity",
      "native",
      "natural",
      "concrete",
      "newtype",
      "unification",
      "pointer",
      "pretype",
      "region",
      "representation",
      "short",
      "signed",
      "signedness",
      "size",
      "step",
      "struct",
      "propositional",
      "switch",
      "this",
      "transparent",
      "transparency",
      "true",
      "type",
      "ubyte",
      "uint",
      "ulong",
      "union",
      "unique",
      "universe",
      "unrestricted",
      "unsigned",
      "used",
      "uses",
      "ushort",
      "word"
    ]

tokens =
  [ "!",
    "!=",
    "&",
    "&*",
    "(",
    ")",
    "(+)",
    "*",
    "+",
    ",",
    "-",
    "->",
    "-*",
    "-[",
    "/",
    ":",
    "::",
    ":*",
    ":^",
    ";",
    "<",
    "<=",
    "=",
    "==",
    ">",
    ">=",
    ">|",
    "@",
    "[",
    "\\",
    "]",
    "]>",
    "_",
    "{",
    "|",
    "|<",
    "}",
    "%[",
    "/|\\"
  ]

tokenFamily = Map.fromList (map family tokens)
  where
    family token = (token, filter (/= token) $ filter (isPrefixOf token) tokens)

descendants :: String -> [String]
descendants token | Map.member token tokenFamily = tokenFamily Map.! token
descendants token = error $ "Unknown token " ++ token

-- to allow for correct pretty printing right recursion should be limited to an equal or higher precedence level
class SyntaxBase δ => Syntax δ where
  token :: String -> δ ()
  tokenNumeric :: Integer -> String -> δ ()
  keyword :: String -> δ ()
  identifer :: δ String
  stringLiteral :: δ String
  number :: δ Integer
  number' :: δ Int

  -- pretty printer only methods
  pick :: (a -> Bool) -> δ a -> δ a -> δ a -- normal ∥ for parser, left when function is true for printer
  (∥#) :: δ a -> δ a -> δ a -- pretty printer only ∥, parser ignores first argument
  space :: δ ()
  line :: δ ()
  indent :: δ ()
  dedent :: δ ()

class Syntax δ => Position δ p where
  position :: δ p
  discard :: Functor f => δ (f p) -> δ (f ())
  discard' :: Functor f => δ (f (p, a)) -> δ (f a)
  discard' x = fmapI unit' ⊣ inverse compose ⊣ discard (compose ⊣ fmapI swap ⊣ x)

binaryToken op = space ≫ token op ≫ space

prefixKeyword word = keyword word ≫ space

binaryKeyword word = space ≫ keyword word ≫ space

betweenParens = between (token "(") (token ")")

betweenParensElse elsex e = token "(" ≫ (token ")" ≫ elsex ∥ e ≪ token ")")

betweenAngle = between (token "<") (token ">")

betweenBraces = between (token "{") (token "}")

betweenSquares = between (token "[") (token "]")

symbol = Language.symbol ⊣ stringLiteral

lambdaCore e = binaryToken "->" ≫ e

lambdaBrace e = space ≫ betweenBraces (indent ≫ line ≫ e ≪ dedent ≪ line)

delimitToken op = token op ≫ line

delimit = delimitToken ";"

commaSome e = some (token "," ≫ space ≫ e)

commaSeperatedMany e = seperatedMany e (token "," ≫ space)

commaSeperatedSome e = seperatedSome e (token "," ≫ space)

commaSeperatedManyLine e = indent ≫ seperatedMany (line ≫ e) (token ",") ≪ dedent ≪ line

commaNonSingle :: (Syntax δ, Position δ p) => δ a -> δ (Either (p, [a]) a)
commaNonSingle = commaNonSingle' always

commaNonSingle' :: (Syntax δ, Position δ p) => δ () -> δ a -> δ (Either (p, [a]) a)
commaNonSingle' final e = discard' positioned
  where
    positioned = distribute ⊣ body final e
      where
        body :: (Syntax δ, Position δ p) => δ () -> δ a -> δ (p, Either [a] a)
        body final e =
          token "(" ≫ position ⊗ (empty ∥ list)
          where
            empty = left ⊣ nil ⊣ token ")"
            list =
              branchDistribute (right . toPrism unit') (left . applyList) ⊣ e ⊗ (final ≪ token ")" ⊕ commaSome e ≪ final ≪ token ")")
              where
                applyList = cons . secondP cons . secondP (toPrism $ inverse nonEmpty)

multiarg core = multiargExclusionary core ∥ singleton ⊣ core

-- excludes single argument multiargs
multiargExclusionary :: Syntax p => p a -> p [a]
multiargExclusionary core = apply ⊣ keyword "multiarg" ≫ betweenParens (core ⊗ token "," ≫ space ≫ commaSeperatedSome core ⊕ always)
  where
    apply = branch (cons . secondP (cons . toPrism (inverse nonEmpty))) nil

pathTail = cons ⊣ token "/" ≫ identifer ⊗ pathTail ∥ nil ⊣ always

path = Language.path . nonEmpty ⊣ token "/" ≫ identifer ⊗ pathTail

localPath = Language.path . nonEmpty ⊣ identifer ⊗ pathTail

semiPath = Language.semiPath ⊣ pathTail

termIdentifier = Language.termIdentifier ⊣ identifer

termGlobalIdentifier = Language.termGlobalIdentifier ⊣ path

typeIdentifier = Language.typeIdentifier ⊣ identifer

typeGlobalIdentifier = Language.typeGlobalIdentifier ⊣ path

typePattern ::
  (Syntax δ, Position δ p) =>
  δ (Language.TypePattern p)
typePattern =
  Language.typePattern ⊣ position ⊗ typeIdentifier ⊗ erase ⊗ typex
  where
    erase =
      choice
        [ Language.transparent ⊣ token ":",
          Language.concrete ⊣ token ":*"
        ]

typeParen :: (Position δ p, Syntax δ) => δ (Language.Type p)
typeParen = branch' Language.tuple id ⊣ commaNonSingle typex

typex :: (Position δ p, Syntax δ) => δ (Language.Type p)
typex = typeLambda
  where
    typeLambda = Language.typeScheme ⊣ position ⊗ body ∥ typeArrow
      where
        body = wrapType ⊣ scheme False ≪ space ⊗ typeLambda
    typeArrow = applyBinary ⊣ typeEffect ⊗ ((linearArrow ∥ unrestrictedArrow ∥ polymorphicArrow) ⊕ always)
      where
        applyBinary = Language.inline `branchDistribute` unit'
        linearArrow = position ⊗ binaryToken "->" ≫ linear ⊗ typeArrow
          where
            linear = Language.typeFalse ⊣ position
        unrestrictedArrow = position ⊗ binaryToken "-*" ≫ unrestricted ⊗ typeArrow
          where
            unrestricted = Language.typeTrue ⊣ position
        polymorphicArrow = position ⊗ space ≫ token "-" ≫ typeCore ⊗ space ≫ typeArrow
    typeEffect = Language.effect `branchDistribute` unit' ⊣ typeUnique ⊗ (position ⊗ binaryKeyword "in" ≫ typeUnique ⊕ always)

typeUnique :: (Position δ p, Syntax δ) => δ (Language.Type p)
typeUnique = unique ∥ typePtr
  where
    unique = Language.unique ⊣ position ⊗ prefixKeyword "unique" ≫ typePtr
    typePtr =
      foldlP apply ⊣ typeInt
        ⊗ many
          (position ≪ token "*" ⊕ position ≪ token "[" ≪ token "]" ⊕ position ⊗ binaryToken "@" ≫ typeInt)
      where
        apply = Language.pointer `branchDistribute` Language.array `branchDistribute` Language.shared
    typeInt = integers ∥# apply ⊣ kindWord ⊗ (position ⊗ space ≫ keyword "integer" ≫ typeParen ⊕ always)
      where
        apply = Language.number `branchDistribute` unit'
    kindWord = apply ⊣ typeXor ⊗ (position ≪ space ≪ keyword "word" ⊕ always)
      where
        apply = Language.wordRep `branchDistribute` unit'
    typeXor = foldlP Language.typeXor ⊣ typeOr ⊗ many (position ⊗ binaryToken "(+)" ≫ typeOr)
    typeOr = foldlP Language.typeOr ⊣ typeAnd ⊗ many (position ⊗ binaryToken "|" ≫ typeAnd)
    typeAnd = foldlP Language.typeAnd ⊣ typeNot ⊗ many (position ⊗ binaryToken "&" ≫ typeNot)
    typeNot = not ∥ typeCore
      where
        not = Language.typeNot ⊣ position ⊗ token "!" ≫ typeNot

integers :: (Position δ p, Syntax δ) => δ (Language.Type p)
integers =
  choice
    [ shortcut "byte" Language.signed Language.byte,
      shortcut "short" Language.signed Language.short,
      shortcut "int" Language.signed Language.int,
      shortcut "long" Language.signed Language.long,
      shortcut "ubyte" Language.unsigned Language.byte,
      shortcut "ushort" Language.unsigned Language.short,
      shortcut "uint" Language.unsigned Language.int,
      shortcut "ulong" Language.unsigned Language.long,
      Language.number' ⊣ position ⊗ keyword "integer" ≫ literal Language.signed ⊗ parameterized,
      Language.number' ⊣ position ⊗ keyword "natural" ≫ literal Language.unsigned ⊗ parameterized
    ]
  where
    shortcut name signed size = Language.number' ⊣ position ⊗ keyword name ≫ literal signed ⊗ literal size
    parameterized = literal Language.native ∥# betweenParens typex ∥ literal Language.native
    literal x = x ⊣ position

typeCore :: (Position δ p, Syntax δ) => δ (Language.Type p)
typeCore = choice options ∥ hole ∥ integers ∥ typeParen
  where
    options :: (Position δ p, Syntax δ) => [δ (Language.Type p)]
    options =
      [ Language.typeVariable ⊣ position ⊗ typeIdentifier,
        Language.typeGlobalVariable ⊣ position ⊗ typeGlobalIdentifier,
        Language.boolean ⊣ position ≪ keyword "bool",
        Language.world ⊣ position ≪ keyword "io",
        keyword "function" ≫ (funLiteral ∥ funPointer),
        Language.typex ⊣ position ≪ keyword "type",
        Language.pretype ⊣ position ⊗ keyword "pretype" ≫ betweenAngle (typex ≪ token "," ⊗ space ≫ typex),
        Language.boxed ⊣ position ≪ keyword "boxed",
        Language.region ⊣ position ≪ keyword "region",
        Language.pointerRep ⊣ position ≪ keyword "pointer",
        Language.structRep ⊣ position ⊗ prefixKeyword "struct" ≫ betweenParens (commaSeperatedMany typex),
        Language.unionRep ⊣ position ⊗ prefixKeyword "union" ≫ betweenParens (commaSeperatedMany typex),
        Language.byte ⊣ position ≪ tokenNumeric 8 "bit",
        Language.short ⊣ position ≪ tokenNumeric 16 "bit",
        Language.int ⊣ position ≪ tokenNumeric 32 "bit",
        Language.long ⊣ position ≪ tokenNumeric 64 "bit",
        Language.native ⊣ position ≪ keyword "native",
        Language.signed ⊣ position ≪ keyword "signed",
        Language.unsigned ⊣ position ≪ keyword "unsigned",
        Language.kind ⊣ position ⊗ keyword "kind" ≫ betweenAngle typex,
        Language.representation ⊣ position ≪ keyword "representation",
        Language.size ⊣ position ≪ keyword "size",
        Language.signedness ⊣ position ≪ keyword "signedness",
        Language.syntactic ⊣ position ≪ keyword "syntactic",
        Language.propositional ⊣ position ≪ keyword "propositional",
        Language.multiplicity ⊣ position ≪ keyword "multiplicity",
        Language.step ⊣ position ⊗ keyword "step" ≫ betweenAngle (typex ≪ token "," ≪ space ⊗ typex),
        Language.top ⊣ position ≪ token "/|\\",
        Language.unification ⊣ position ≪ keyword "unification",
        Language.label ⊣ position ≪ keyword "label",
        Language.ambiguousLabel ⊣ position ≪ keyword "ambiguous",
        Language.typeTrue ⊣ position ≪ keyword "true",
        Language.typeFalse ⊣ position ≪ keyword "false"
      ]
    hole = Language.hole ⊣ position ≪ token "_"
    rotate = swap_2_3_of_3
    -- todo remove this eventually
    funLiteral = Language.functionLiteralType ⊣ position ⊗ body
      where
        body = rotate ⊣ space ≫ prefixKeyword "internal" ≫ arguments ⊗ binaryToken "->" ≫ typex ⊗ binaryKeyword "uses" ≫ typeCore
    funPointer = Language.functionPointer ⊣ position ⊗ body
      where
        body = rotate ⊣ arguments ⊗ binaryToken "->" ≫ typex ⊗ binaryKeyword "uses" ≫ typeCore
    arguments = betweenParens (commaSeperatedMany typex)

newtype Scheme p = Scheme {runScheme :: [Language.TypePattern p]}

isoScheme = Isomorph Scheme runScheme

scheme :: (Syntax δ, Position δ p) => Bool -> δ (Scheme p)
scheme line = isoScheme ⊣ schema
  where
    schema = betweenAngle $ seperate typePattern
      where
        seperate = if line then commaSeperatedManyLine else commaSeperatedMany

wrapType :: Isomorph (Scheme p, Language.Type p) (Language.TypeScheme p)
wrapType =
  wrap Language.typeForall . secondI (assumeIsomorph Language.monoType)

wrapTerm :: Isomorph (Scheme p, Language.Term p) (Language.TermScheme p)
wrapTerm =
  wrap Language.typeAbstraction . secondI (assumeIsomorph Language.monoTerm)

wrap scheme = foldrP scheme . firstI (inverse isoScheme)

termPatternParen :: (Position δ p, Syntax δ) => δ (Language.TermPattern p)
termPatternParen = branch' Language.matchTuple id ⊣ commaNonSingle' always termPattern

termPattern :: (Position δ p, Syntax δ) => δ (Language.TermPattern p)
termPattern = choice options ∥ termPatternParen
  where
    options =
      [ Language.matchVariable ⊣ position ⊗ termIdentifier ⊗ annotation,
        Language.matchTrue ⊣ position ≪ keyword "true",
        Language.matchFalse ⊣ position ≪ keyword "false"
      ]
    annotation = blank ∥# binaryToken "::" ≫ typex ∥ blank
    blank = Language.hole ⊣ position

termPatternCore = choice options ∥ termPatternParen
  where
    options =
      [ Language.matchVariable ⊣ position ⊗ termIdentifier ⊗ annotation,
        Language.matchTrue ⊣ position ≪ keyword "true",
        Language.matchFalse ⊣ position ≪ keyword "false"
      ]
    annotation = blank
    blank = Language.hole ⊣ position

termMetaPattern :: (Position δ p, Syntax δ) => δ (Language.TermMetaPattern p)
termMetaPattern = choice options ∥ betweenParens termMetaPattern
  where
    options =
      [ Language.inlineMatchVariable ⊣ position ⊗ termIdentifier ⊗ annotation
      ]
    annotation =
      implicit
        ∥# choice
          [ linearAnnotation ⊗ typex,
            unrestrictedAnnotation ⊗ typex,
            polymorphicAnnotation ⊗ typex,
            implicit
          ]
    implicit = linear ⊗ blank
      where
        linear = Language.typeFalse ⊣ position
        blank = Language.hole ⊣ position
    linearAnnotation = Language.typeFalse ⊣ position ≪ binaryToken ":"
    unrestrictedAnnotation = Language.typeTrue ⊣ position ≪ binaryToken ":*"
    polymorphicAnnotation = space ≫ token ":^" ≫ typeCore ≪ space

termMetaPatternCore = variable ∥ betweenParens termMetaPattern
  where
    variable = Language.inlineMatchVariable ⊣ position ⊗ termIdentifier ⊗ implicit where
    implicit = linear ⊗ blank
    blank = Language.hole ⊣ position
    linear = Language.typeFalse ⊣ position

termParen :: (Position δ p, Syntax δ) => δ (Language.Term p)
termParen = branch' Language.tupleLiteral id ⊣ commaNonSingle term

isStatement e = case e of
  (Language.Let {}) -> True
  (Language.InlineLet {}) -> True
  (Language.Loop {}) -> True
  (Language.If {}) -> True
  (Language.Case {}) -> True
  (Language.Do {}) -> True
  _ -> False

termStatement :: (Position δ p, Syntax δ) => δ (Language.Term p)
termStatement = choice options ∥ apply ⊣ term ⊗ (position ⊗ delimit ≫ termStatement ⊕ always)
  where
    options =
      [ Language.inlineLet ⊣ position ⊗ inlineLet,
        Language.letx ⊣ position ⊗ letx,
        Language.loop ⊣ position ⊗ loop,
        Language.ifx ⊣ position ⊗ ifx,
        Language.casex ⊣ position ⊗ casex
      ]
    inlineLet = prefixKeyword "inline" ≫ termMetaPattern ≪ binaryToken "=" ⊗ term ≪ delimit ⊗ termStatement
    letx = prefixKeyword "let" ≫ termPattern ≪ binaryToken "=" ⊗ term ≪ delimit ⊗ termStatement
    loop = prefixKeyword "loop" ≫ betweenParens (prefixKeyword "let" ≫ termPattern ≪ binaryToken "=" ⊗ term) ⊗ lambdaBrace termStatement
    ifx = prefixKeyword "if" ≫ termCore ⊗ lambdaBrace termStatement ≪ binaryKeyword "else" ⊗ lambdaBrace termStatement
    casex = prefixKeyword "switch" ≫ termCore ⊗ lambdaBrace (many $ termPatternCore ⊗ binaryToken "->" ≫ term ≪ delimit)
    apply = Language.dox `branchDistribute` unit'

termTop :: forall δ p. (Position δ p, Syntax δ) => δ (Language.Term p)
termTop = lambda ∥# term
  where
    lambda = Language.inlineAbstraction ⊣ position ⊗ (token "\\" ≫ termMetaPatternCore ⊗ line ≫ lambdaCore termTop)

term :: forall δ p. (Position δ p, Syntax δ) => δ (Language.Term p)
term = termLambda
  where
    termLambda = lambda ∥ poly ∥ termAnnotate
      where
        lambda = Language.inlineAbstraction ⊣ position ⊗ (token "\\" ≫ termMetaPatternCore ⊗ lambdaCore term)
        poly = Language.polyIntroduction ⊣ position ⊗ (wrapTerm ⊣ scheme False ≪ space ⊗ term)
    termAnnotate :: δ (Language.Term p)
    termAnnotate = apply ⊣ termOr ⊗ (position ⊗ binaryToken "::" ≫ typex ⊕ position ⊗ binaryToken ":" ≫ typex ⊕ always)
      where
        apply = Language.pretypeAnnotation `branchDistribute` Language.typeAnnotation `branchDistribute` unit'
    termOr = foldlP Language.or ⊣ termAnd ⊗ many (position ⊗ binaryToken "|" ≫ termAnd)
    termAnd = foldlP Language.and ⊣ termEqual ⊗ many (position ⊗ binaryToken "&" ≫ termEqual)
    termEqual = apply ⊣ termAdd ⊗ operators
      where
        apply = equal `b` notEqual `b` lessThenEqual `b` lessThen `b` greaterThenEqual `b` greaterThen `b` unit'
          where
            i o = Language.relational o
            b = branchDistribute
            equal = i Language.Equal
            notEqual = i Language.NotEqual
            lessThen = i Language.LessThen
            lessThenEqual = i Language.LessThenEqual
            greaterThen = i Language.GreaterThen
            greaterThenEqual = i Language.GreaterThenEqual
        operators = r "==" ⊕ r "!=" ⊕ r "<=" ⊕ r "<" ⊕ r ">=" ⊕ r ">" ⊕ always
          where
            r op = position ⊗ binaryToken op ≫ termAdd
    termAdd = foldlP apply ⊣ termMul ⊗ many (position ⊗ binaryToken "+" ≫ termMul ⊕ position ⊗ binaryToken "-" ≫ termMul)
      where
        apply = Language.arithmatic Language.Addition `branchDistribute` Language.arithmatic Language.Subtraction
    termMul = foldlP apply ⊣ termDeref ⊗ many (position ⊗ binaryToken "*" ≫ termDeref ⊕ position ⊗ binaryToken "/" ≫ termDeref)
      where
        apply = Language.arithmatic Language.Multiplication `branchDistribute` Language.arithmatic Language.Division
    termDeref = deref ∥ termPrefix
      where
        apply = branchDistribute (Language.write) (Language.read . secondP (toPrism unit')) . toPrism (secondI distribute)
        deref = apply ⊣ position ⊗ (token "*" ≫ termPrefix ⊗ (binaryToken "=" ≫ betweenParens term ⊕ always))
    termPrefix = choice options ∥ termIndex
      where
        options =
          [ Language.read ⊣ position ⊗ token "*" ≫ termPrefix,
            Language.not ⊣ position ⊗ token "!" ≫ termPrefix,
            Language.isolate ⊣ position ⊗ token "&*" ≫ termPrefix
          ]
    termIndex = index ∥ termApply
      where
        index = Language.pointerAddition ⊣ position ⊗ token "&" ≫ termApply ⊗ betweenSquares term
    termApply = termVariable noInstance ∥# foldlP apply ⊣ termLateVariable ⊗ many (applySyntax ⊕ rtApplySyntax ⊕ elimSyntax)
      where
        apply = Language.inlineApplication `branchDistribute` Language.application `branchDistribute` Language.polyElimination
        applySyntax = position ⊗ space ≫ pick isStatement (lambdaBrace termStatement) (betweenBraces termStatement)
        rtApplySyntax = position ⊗ space ≫ betweenParens (commaSeperatedMany term)
        elimSyntax = position ⊗ space ≫ instanciation
    termLateVariable = termVariable (instanciation ∥ noInstance) ∥ termCore

    noInstance = Language.instantiationInfer ⊣ always

termVariable instanciation = choice variables
  where
    instanciationVariable = instanciation ∥ Language.instantiationInfer ⊣ always
    variables =
      [ Language.variable ⊣ position ⊗ termIdentifier ⊗ instanciationVariable,
        Language.globalVariable ⊣ position ⊗ termGlobalIdentifier ⊗ instanciationVariable
      ]

instanciation = token "@" ≫ inst
  where
    inst = Language.instanciation ⊣ betweenAngle (commaSeperatedMany typex) ∥ Language.instantiationInfer ⊣ token "_"

termCore :: forall δ p. (Position δ p, Syntax δ) => δ (Language.Term p)
termCore = choice options ∥ termVariable noInstance ∥ pick isStatement (lambdaBrace termStatement) termParen
  where
    noInstance = Language.instantiationInfer ⊣ always
    options =
      [ Language.extern ⊣ position ⊗ prefixKeyword "extern" ≫ number' ⊗ symbol,
        Language.numberLiteral ⊣ position ⊗ number,
        Language.true ⊣ position ≪ keyword "true",
        Language.false ⊣ position ≪ keyword "false",
        Language.break ⊣ position ⊗ prefixKeyword "break" ≫ termCore,
        Language.continue ⊣ position ⊗ prefixKeyword "continue" ≫ termCore,
        Language.cast ⊣ position ⊗ prefixKeyword "cast" ≫ termCore
      ]

inline :: (Syntax δ, Position δ p) => δ (Language.Path, Language.Global p)
inline = prefixKeyword "inline" ≫ localPath ⊗ (Language.macro ⊣ definition)
  where
    definition = manual ∥ auto
    manual = Language.termManual ⊣ wrapTerm ⊣ scheme True ⊗ body
    auto = Language.termAuto ⊣ body
    body = annotated ∥ plain
    annotated = Language.typeAnnotation' ⊣ marked
    marked = position ⊗ binaryToken ":" ≫ typex ⊗ binaryToken "=" ≫ termTop ≪ token ";"
    plain = binaryToken "=" ≫ termTop ≪ token ";"

text :: (Syntax δ, Position δ p) => δ (Language.Path, Language.Global p)
text = localPath ⊗ (Language.text ⊣ definition)
  where
    definition = Language.termManual ⊣ manual ∥ Language.termAuto ⊣ auto
    manual = wrapTerm ⊣ scheme True ⊗ (Language.functionLiteral ⊣ position ⊗ syntax)
    auto = Language.functionLiteral ⊣ position ⊗ syntax
    syntax = betweenParens (commaSeperatedManyLine termPattern) ⊗ main
    main = implicit ∥# semi ∥ explicit ∥ implicit
    semi = binaryToken "::" ≫ typeUnique ⊗ false ⊗ braced
    false = Language.typeFalse ⊣ position
    implicit = hole ⊗ hole ⊗ braced
    hole = Language.hole ⊣ position
    explicit = binaryToken ":" ≫ typeUnique ⊗ binaryKeyword "in" ≫ typex ⊗ braced
    braced = lambdaBrace termStatement

synonym :: (Syntax δ, Position δ p) => δ (Language.Path, Language.Global p)
synonym = prefixKeyword "type" ≫ localPath ⊗ binaryToken "=" ≫ (Language.synonym ⊣ typex) ≪ token ";"

newType :: (Syntax δ, Position δ p) => δ (Language.Path, Language.Global p)
newType = prefixKeyword "newtype" ≫ localPath ⊗ declare
  where
    declare = Language.forwardNewtype ⊣ binaryToken ":" ≫ typex ≪ token ";"

itemsRaw = seperatedMany (inline ∥ text ∥ synonym ∥ newType) (line ≫ line) where

-- todo readd syntax for forward declarations
items :: (Syntax δ, Position δ p) => δ (Map Language.Path (NonEmpty (Language.Global p)))
items = orderlessMulti ⊣ itemsRaw

newtype Parser a = Parser (Parsec Void String a) deriving (Functor, Applicative, Monad, Alternative, MonadPlus)

parseMain ::
  Parser a ->
  String ->
  String ->
  Either
    (Megaparsec.ParseErrorBundle String Void)
    a
parseMain (Parser p) = Megaparsec.parse (Megaparsec.space *> p <* Megaparsec.eof)

parseMaybe :: Parser a -> String -> Maybe a
parseMaybe (Parser p) = Megaparsec.parseMaybe (p <* Megaparsec.eof)

instance SyntaxBase Parser where
  syntaxmap (Prism f _) p = f <$> p
  (⊗) = liftM2 (,)
  (∥) = (<|>)
  never = empty
  always = pure ()

instance Syntax Parser where
  token op = Parser $ do
    Megaparsec.notFollowedBy $ asum (Megaparsec.string <$> descendants op)
    Megaparsec.string op >> Megaparsec.space
  tokenNumeric n word = Parser $ Megaparsec.string (show n ++ word) *> Megaparsec.space
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
    n <- Megaparsec.try $ read <$> Megaparsec.some (Megaparsec.satisfy isNum Megaparsec.<?> "number") <* Megaparsec.space
    Megaparsec.notFollowedBy (Megaparsec.string "bit")
    pure n
    where
      isNum x = x `elem` ['0' .. '9']
  number' = let (Parser n) = number in Parser (fromIntegral <$> n)
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
  discard (Parser p) = Parser (fmap (() <$) p)

instance Position Parser () where
  position = Parser $ pure ()
  discard = id

instance Syntax Printer where
  token op = Printer $ \() -> Just $ tell op
  tokenNumeric i word = token (show i ++ word)
  keyword name | name `Set.member` keywords = Printer $ \() -> Just $ tell name
  keyword name = error $ "bad keyword: " ++ name

  -- todo invert syntax for pretty printing keywords as identifers
  identifer = Printer $ \name -> Just $ tell name
  stringLiteral = Printer $ \str -> Just $ do
    tell "\""
    tell str
    tell "\""
  number = Printer $ \n -> Just $ tell $ show n
  number' = Printer $ \n -> Just $ tell $ show n
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

instance Position Printer () where
  position = Printer $ \() -> Just $ pure ()
  discard = id
