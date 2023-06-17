module Syntax where

import qualified Ast.Module.Surface as Module
import qualified Ast.Term.Algebra as Language
import qualified Ast.Term.Runtime as Language
import qualified Ast.Term.Surface as Language
import qualified Ast.Type.Surface as Language
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
import Misc.Path (Path)
import qualified Misc.Path as Path hiding (combine)
import Misc.Prism
import qualified Misc.Symbol as Symbol
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
      "borrow",
      "boxed",
      "break",
      "byte",
      "capacity",
      "continue",
      "copy",
      "else",
      "existance",
      "extern",
      "false",
      "function",
      "extern",
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
      "opaque",
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
      "unwrap",
      "used",
      "uses",
      "ushort",
      "word",
      "wrap",
      "wrapper"
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

symbol = Symbol.symbol ⊣ stringLiteral

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

path = Path.path . nonEmpty ⊣ token "/" ≫ identifer ⊗ pathTail

localPath = Path.path . nonEmpty ⊣ identifer ⊗ pathTail

semiPath = Path.semiPath ⊣ pathTail

termIdentifier = Language.termIdentifier ⊣ identifer

termGlobalIdentifier = Language.termGlobalIdentifier ⊣ path

typeIdentifier = Language.typeIdentifier ⊣ identifer

typeGlobalIdentifier = Language.typeGlobalIdentifier ⊣ path

typePattern ::
  (Syntax δ, Position δ p) =>
  δ (Language.TypePattern p)
typePattern =
  Language.typePattern ⊣ position ⊗ typeIdentifier ⊗ k
  where
    k = token ":" ≫ typex

typeParen :: (Position δ p, Syntax δ) => δ (Language.Type p)
typeParen = branch' (toPrism Language.typeSource . secondP Language.tuple) id ⊣ commaNonSingle typex

typex :: (Position δ p, Syntax δ) => δ (Language.Type p)
typex = typeLambda
  where
    typeLambda = Language.typeSource ⊣ position ⊗ poly ∥ typeArrow
      where
        poly = Language.poly ⊣ label ⊗ body
          where
            label = ambiguous ∥# token "%[" ≫ typeCore ≪ token "]" ∥ ambiguous
              where
                ambiguous = Language.typeSource ⊣ position ⊗ (Language.ambiguousLabel ⊣ always)
            body = wrapType ⊣ scheme False ≪ space ⊗ position ⊗ typeLambda
    typeArrow = applyBinary ⊣ typeEffect ⊗ ((linearArrow ∥ unrestrictedArrow ∥ polymorphicArrow) ⊕ always)
      where
        applyBinary = Language.inline `branchDistribute` unit'
        linearArrow = position ⊗ binaryToken "->" ≫ linear ⊗ typeArrow
          where
            linear = Language.typeSource ⊣ position ⊗ (Language.typeFalse ⊣ always)
        unrestrictedArrow = position ⊗ binaryToken "-*" ≫ unrestricted ⊗ typeArrow
          where
            unrestricted = Language.typeSource ⊣ position ⊗ (Language.typeTrue ⊣ always)
        polymorphicArrow = position ⊗ space ≫ token "-" ≫ typeCore ⊗ space ≫ typeArrow
    typeEffect = Language.effect `branchDistribute` unit' ⊣ typeUnique ⊗ (position ⊗ binaryKeyword "in" ≫ typeUnique ⊕ always)

typeUnique :: (Position δ p, Syntax δ) => δ (Language.Type p)
typeUnique = Language.typeSource ⊣ position ⊗ unique ∥ typePtr
  where
    unique = Language.unique ⊣ prefixKeyword "unique" ≫ typePtr
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
    typeNot = Language.typeSource ⊣ position ⊗ not ∥ typeCore
      where
        not = Language.typeNot ⊣ token "!" ≫ typeNot

integers :: (Position δ p, Syntax δ) => δ (Language.Type p)
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
        shortcut "ulong" Language.unsigned Language.long,
        Language.number' ⊣ keyword "integer" ≫ literal Language.signed ⊗ parameterized,
        Language.number' ⊣ keyword "natural" ≫ literal Language.unsigned ⊗ parameterized
      ]
  where
    shortcut name signed size = Language.number' ⊣ keyword name ≫ literal signed ⊗ literal size
    parameterized = literal Language.native ∥# betweenParens typex ∥ literal Language.native
    literal x = Language.typeSource ⊣ position ⊗ (x ⊣ always)

typeCore :: (Position δ p, Syntax δ) => δ (Language.Type p)
typeCore = Language.typeSource ⊣ position ⊗ (choice options) ∥ integers ∥ typeParen
  where
    options =
      [ Language.typeVariable ⊣ typeIdentifier,
        Language.typeGlobalVariable ⊣ typeGlobalIdentifier,
        Language.boolean ⊣ keyword "bool",
        Language.world ⊣ keyword "io",
        keyword "function" ≫ (funLiteral ∥ funPointer),
        Language.typex ⊣ keyword "type",
        Language.pretype ⊣ keyword "pretype" ≫ betweenAngle (typex ≪ token "," ⊗ space ≫ typex),
        Language.boxed ⊣ keyword "boxed",
        Language.region ⊣ keyword "region",
        Language.pointerRep ⊣ keyword "pointer",
        Language.structRep ⊣ prefixKeyword "struct" ≫ betweenParens (commaSeperatedMany typex),
        Language.unionRep ⊣ prefixKeyword "union" ≫ betweenParens (commaSeperatedMany typex),
        Language.byte ⊣ tokenNumeric 8 "bit",
        Language.short ⊣ tokenNumeric 16 "bit",
        Language.int ⊣ tokenNumeric 32 "bit",
        Language.long ⊣ tokenNumeric 64 "bit",
        Language.native ⊣ keyword "native",
        Language.signed ⊣ keyword "signed",
        Language.unsigned ⊣ keyword "unsigned",
        Language.kind ⊣ keyword "kind" ≫ betweenAngle (typex ⊗ token "," ≫ space ≫ typex),
        Language.representation ⊣ keyword "representation",
        Language.size ⊣ keyword "size",
        Language.signedness ⊣ keyword "signedness",
        Language.syntactic ⊣ keyword "syntactic",
        Language.propositional ⊣ keyword "propositional",
        Language.transparent ⊣ keyword "transparent",
        Language.opaque ⊣ keyword "opaque",
        Language.multiplicity ⊣ keyword "multiplicity",
        Language.step ⊣ keyword "step" ≫ betweenAngle (typex ≪ token "," ≪ space ⊗ typex),
        Language.top ⊣ token "/|\\",
        Language.unification ⊣ keyword "unification",
        Language.transparency ⊣ keyword "transparency",
        Language.label ⊣ keyword "label",
        Language.ambiguousLabel ⊣ keyword "ambiguous",
        Language.hole ⊣ token "_",
        Language.typeTrue ⊣ keyword "true",
        Language.typeFalse ⊣ keyword "false"
      ]
    rotate = swap_2_3_of_3
    -- todo remove this eventually
    funLiteral = Language.functionLiteralType ⊣ rotate ⊣ space ≫ prefixKeyword "internal" ≫ typeParen ⊗ binaryToken "->" ≫ typex ⊗ binaryKeyword "uses" ≫ typeCore
    funPointer = Language.functionPointer ⊣ rotate ⊣ typeParen ⊗ binaryToken "->" ≫ typex ⊗ binaryKeyword "uses" ≫ typeCore

newtype Scheme p = Scheme {runScheme :: [(p, Language.TypePattern p)]}

isoScheme = Isomorph Scheme runScheme

scheme :: (Syntax δ, Position δ p) => Bool -> δ (Scheme p)
scheme line = isoScheme ⊣ schema
  where
    schema = betweenAngle $ seperate (position ⊗ schemeCore)
      where
        seperate = if line then commaSeperatedManyLine else commaSeperatedMany
    schemeCore = typePattern

wrapType :: Isomorph ((Scheme p, p), Language.Type p) (Language.TypeScheme p)
wrapType =
  wrap Language.typeForall . secondI (assumeIsomorph Language.monoType) . associate

wrapTerm :: Isomorph ((Scheme p, p), Language.Term p) (Language.TermScheme p)
wrapTerm =
  wrap Language.typeAbstraction . secondI (assumeIsomorph Language.monoTerm) . associate

wrap scheme = foldrP scheme . firstI (inverse isoScheme)

termPatternParen :: (Position δ p, Syntax δ) => Bool -> δ (Language.TermPattern p)
termPatternParen top =
  branch' (toPrism Language.termPattern . secondP Language.runtimePatternTuple) id
    ⊣ commaNonSingle' last (go termPattern)
  where
    go e
      | top = indent ≫ line ≫ e ≪ dedent
      | otherwise = e
    last = if top then line else always

termPattern :: (Position δ p, Syntax δ) => δ (Language.TermPattern p)
termPattern = Language.termPattern ⊣ position ⊗ choice options ∥ termPatternParen False
  where
    options =
      [ Language.runtimePatternVariable ⊣ termIdentifier ⊗ annotation,
        Language.runtimePatternTrue ⊣ keyword "true",
        Language.runtimePatternFalse ⊣ keyword "false"
      ]
    annotation = blank ∥# binaryToken "::" ≫ typex ∥ blank
    blank = Language.typeSource ⊣ (position ⊗ (Language.hole ⊣ always))

termPatternCore = Language.termPattern ⊣ position ⊗ choice options ∥ termPatternParen False
  where
    options =
      [ Language.runtimePatternVariable ⊣ termIdentifier ⊗ annotation,
        Language.runtimePatternTrue ⊣ keyword "true",
        Language.runtimePatternFalse ⊣ keyword "false"
      ]
    annotation = blank
    blank = Language.typeSource ⊣ (position ⊗ (Language.hole ⊣ always))

termMetaPattern :: (Position δ p, Syntax δ) => δ (Language.TermMetaPattern p)
termMetaPattern = Language.termMetaPattern ⊣ position ⊗ choice options ∥ betweenParens termMetaPattern
  where
    options =
      [ Language.patternVariable ⊣ associate' ⊣ termIdentifier ⊗ annotation
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
        linear = Language.typeSource ⊣ (position ⊗ (Language.typeFalse ⊣ always))
        blank = Language.typeSource ⊣ (position ⊗ (Language.hole ⊣ always))
    linearAnnotation = Language.typeSource ⊣ position ⊗ (Language.typeFalse ⊣ binaryToken ":")
    unrestrictedAnnotation = Language.typeSource ⊣ position ⊗ (Language.typeTrue ⊣ binaryToken ":*")
    polymorphicAnnotation = space ≫ token ":^" ≫ typeCore ≪ space

termMetaPatternCore = Language.termMetaPattern ⊣ position ⊗ variable ∥ betweenParens termMetaPattern
  where
    variable = Language.patternVariable ⊣ associate' ⊣ termIdentifier ⊗ implicit where
    implicit = linear ⊗ blank
    blank = Language.typeSource ⊣ (position ⊗ (Language.hole ⊣ always))
    linear = Language.typeSource ⊣ (position ⊗ (Language.typeFalse ⊣ always))

termParen :: (Position δ p, Syntax δ) => δ (Language.Term p)
termParen = branch' (toPrism Language.term . secondP Language.tupleIntroduction) id ⊣ commaNonSingle term

isStatement (Language.Term _ e) = case e of
  (Language.Bind _ _) -> True
  (Language.TermRuntime (Language.Alias _ _)) -> True
  (Language.TermRuntime (Language.Loop _ _)) -> True
  (Language.TermSugar (Language.If _ _ _ _)) -> True
  (Language.TermErasure (Language.Borrow _ _)) -> True
  (Language.TermRuntime (Language.Case _ _ _ _)) -> True
  _ -> False

termStatement :: (Position δ p, Syntax δ) => δ (Language.Term p)
termStatement =
  Language.term ⊣ position ⊗ choice options
    ∥ apply ⊣ term ⊗ (position ⊗ delimit ≫ termStatement ⊕ always)
  where
    options =
      [ Language.bind ⊣ rotateBind Language.termMetaBound ⊣ prefixKeyword "inline" ≫ termMetaPattern ≪ binaryToken "=" ⊗ term ≪ delimit ⊗ termStatement,
        Language.alias ⊣ rotateBind Language.termBound ⊣ prefixKeyword "let" ≫ termPattern ≪ binaryToken "=" ⊗ term ≪ delimit ⊗ termStatement,
        Language.loop ⊣ rotateBind Language.termBound ⊣ prefixKeyword "loop" ≫ betweenParens (prefixKeyword "let" ≫ termPattern ≪ binaryToken "=" ⊗ term) ⊗ lambdaBrace termStatement,
        Language.ifx ⊣ prefixKeyword "if" ≫ termCore ⊗ lambdaBrace termStatement ≪ binaryKeyword "else" ⊗ lambdaBrace termStatement,
        Language.casex ⊣ prefixKeyword "switch" ≫ termCore ⊗ lambdaBrace (many $ Language.termBound ⊣ termPatternCore ⊗ binaryToken "->" ≫ term ≪ delimit)
      ]
    rotateBind bound = secondI bound . associate . firstI swap
    apply = Language.dox `branchDistribute` unit'

termTop :: forall δ p. (Position δ p, Syntax δ) => δ (Language.Term p)
termTop = prettyLambda ∥# term
  where
    prettyLambda = Language.term ⊣ (position ⊗ lambda)
    lambda = Language.inlineAbstraction ⊣ Language.termMetaBound ⊣ token "\\" ≫ termMetaPatternCore ⊗ line ≫ lambdaCore termTop

term :: forall δ p. (Position δ p, Syntax δ) => δ (Language.Term p)
term = termLambda
  where
    termLambda = Language.term ⊣ position ⊗ (lambdas ∥ poly) ∥ termAnnotate
      where
        lambdas = Language.inlineAbstraction ⊣ Language.termMetaBound ⊣ token "\\" ≫ termMetaPatternCore ⊗ lambdaCore term
        poly = Language.polyIntroduction ⊣ wrapTerm ⊣ scheme False ≪ space ⊗ position ⊗ term
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
    termDeref = Language.term ⊣ position ⊗ deref ∥ termPrefix
      where
        apply = branchDistribute (Language.writeReference) (Language.readReference . toPrism unit')
        deref = apply ⊣ token "*" ≫ termPrefix ⊗ (binaryToken "=" ≫ betweenParens term ⊕ always)
    termPrefix = Language.term ⊣ position ⊗ options ∥ termIndex
      where
        options =
          choice
            [ Language.readReference ⊣ token "*" ≫ termPrefix,
              -- todo add proper lexer for tokens and use ! here
              Language.not ⊣ token "!" ≫ termPrefix,
              Language.isolatePointer ⊣ token "&*" ≫ termPrefix
            ]
    termIndex = Language.term ⊣ position ⊗ index ∥ termApply
      where
        index = Language.pointerIncrement ⊣ token "&" ≫ termApply ⊗ betweenSquares term
    termApply = termVariable noInstance ∥# foldlP apply ⊣ termLateVariable ⊗ many (applySyntax ⊕ rtApplySyntax ⊕ elimSyntax)
      where
        apply = Language.inlineApplication `branchDistribute` Language.functionApplication `branchDistribute` Language.polyElimination
        applySyntax = position ⊗ space ≫ pick isStatement (lambdaBrace termStatement) (betweenBraces termStatement)
        rtApplySyntax = position ⊗ space ≫ termParen
        elimSyntax = position ⊗ space ≫ instanciation
    termLateVariable = termVariable (instanciation ∥ noInstance) ∥ termCore

    noInstance = Language.instantiationInfer ⊣ always

termVariable instanciation = Language.term ⊣ position ⊗ choice variables
  where
    instanciationVariable = instanciation ∥ Language.instantiationInfer ⊣ always
    variables =
      [ Language.variable ⊣ termIdentifier ⊗ instanciationVariable,
        Language.globalVariable ⊣ termGlobalIdentifier ⊗ instanciationVariable
      ]

instanciation = token "@" ≫ inst
  where
    inst = Language.instanciation ⊣ betweenAngle (commaSeperatedMany typex) ∥ Language.instantiationInfer ⊣ token "_"

termCore :: forall δ p. (Position δ p, Syntax δ) => δ (Language.Term p)
termCore = Language.term ⊣ position ⊗ choice options ∥ termVariable noInstance ∥ pick isStatement (lambdaBrace termStatement) termParen
  where
    noInstance = Language.instantiationInfer ⊣ always
    options =
      [ Language.extern ⊣ prefixKeyword "extern" ≫ symbol,
        Language.numberLiteral ⊣ number,
        Language.truex ⊣ keyword "true",
        Language.falsex ⊣ keyword "false",
        Language.break ⊣ prefixKeyword "break" ≫ termCore,
        Language.continue ⊣ prefixKeyword "continue" ≫ termCore,
        Language.wrap ⊣ prefixKeyword "wrap" ≫ termCore,
        Language.unwrap ⊣ prefixKeyword "unwrap" ≫ termCore,
        Language.borrow ⊣ prefixKeyword "borrow" ≫ termIdentifier ⊗ space ≫ (wrapTerm ⊣ scheme False ⊗ position ⊗ lambdaBrace termStatement)
      ]

inline :: (Syntax δ, Position δ p) => δ (Path, Module.Global p)
inline = prefixKeyword "inline" ≫ localPath ⊗ (Module.inline ⊣ definition)
  where
    definition = manual ∥ auto
    manual = Language.termManual ⊣ wrapTerm ⊣ scheme True ⊗ position ⊗ body
    auto = Language.termAuto ⊣ body
    body = annotated ∥ plain
    annotated = Language.typeAnnotation' ⊣ marked
    marked = position ⊗ binaryToken ":" ≫ typex ⊗ binaryToken "=" ≫ termTop ≪ token ";"
    plain = binaryToken "=" ≫ termTop ≪ token ";"

text :: (Syntax δ, Position δ p) => δ (Path, Module.Global p)
text = localPath ⊗ (Module.text ⊣ definition)
  where
    definition = Language.termManual ⊣ manual ∥ Language.termAuto ⊣ auto
    manual = wrapTerm ⊣ scheme True ⊗ position ⊗ (Language.term ⊣ position ⊗ (Language.functionLiteral ⊣ body))
    auto = Language.term ⊣ position ⊗ (Language.functionLiteral ⊣ body)
    body = associate' . firstI Language.termBound . associate' . secondI (swap) ⊣ syntax
    syntax = termPatternParen True ⊗ main
    main = implicit ∥# semi ∥ explicit ∥ implicit
    semi = binaryToken "::" ≫ typeUnique ⊗ false ⊗ braced
    false = Language.typeSource ⊣ (position ⊗ (Language.typeFalse ⊣ always))
    implicit = hole ⊗ hole ⊗ braced
    hole = Language.typeSource ⊣ (position ⊗ (Language.hole ⊣ always))
    explicit = binaryToken ":" ≫ typeUnique ⊗ binaryKeyword "in" ≫ typex ⊗ braced
    braced = lambdaBrace termStatement

synonym :: (Syntax δ, Position δ p) => δ (Path, Module.Global p)
synonym = prefixKeyword "type" ≫ localPath ⊗ binaryToken "=" ≫ (Module.synonym ⊣ typex) ≪ token ";"

newType :: (Syntax δ, Position δ p) => δ (Path, Module.Global p)
newType = prefixKeyword "wrapper" ≫ localPath ⊗ (define ∥ declare)
  where
    define = Module.newType ⊣ binaryToken "=" ≫ typex ≪ token ";"
    declare = Module.forwardNewtype ⊣ binaryToken ":" ≫ typex ≪ token ";"

itemsRaw = seperatedMany (inline ∥ text ∥ synonym ∥ newType) (line ≫ line) where

-- todo readd syntax for forward declarations
items :: (Syntax δ, Position δ p) => δ (Map Path (NonEmpty (Module.Global p)))
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
