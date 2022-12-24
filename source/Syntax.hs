module Syntax where

import qualified Ast.Common as Language
import qualified Ast.Term as Language
import qualified Ast.Type as Language
import Control.Applicative (Alternative, empty, (<|>))
import Control.Category (id, (.))
import Control.Monad (MonadPlus, guard, liftM2)
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict (State, get, put, runState)
import Control.Monad.Trans.Writer.Strict (WriterT, runWriterT, tell)
import Data.Foldable (asum)
import Data.List (isPrefixOf)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
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
      "if",
      "in",
      "inline",
      "int",
      "integer",
      "internal",
      "invariant",
      "io",
      "kind",
      "label",
      "let",
      "linear",
      "long",
      "loop",
      "module",
      "multiarg",
      "multiplicity",
      "native",
      "opaque",
      "orderability",
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
      "subtypable",
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
    "*",
    "+",
    ",",
    "-",
    "->",
    "-[",
    "/",
    ":",
    "::",
    ";",
    "<",
    "<=",
    "<_>",
    "=",
    "==",
    "=>",
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
descendants token = tokenFamily Map.! token

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

  -- ugly hack for parsing modules
  groupItems :: (Show x, Ord x) => δ (Map x (NonEmpty (Item p))) -> δ (Map x (Module.Item (Module.GlobalSource p)))

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

symbol = Symbol.symbol ⊣ stringLiteral

lambdaCore e = binaryToken "=>" ≫ e

lambdaBrace e = space ≫ betweenBraces (indent ≫ line ≫ e ≪ dedent ≪ line)

delimitToken op = token op ≫ line

delimit = delimitToken ";"

commaSome e = some (token "," ≫ space ≫ e)

commaSeperatedMany e = seperatedMany e (token "," ≫ space)

commaSeperatedSome e = seperatedSome e (token "," ≫ space)

commaSeperatedManyLine e = indent ≫ seperatedMany (line ≫ e) (token ",") ≪ dedent ≪ line

commaNonSingle :: (Syntax δ, Position δ p) => δ a -> δ (Either (p, [a]) a)
commaNonSingle e = bimapI unit' id ⊣ commaNonSingle' always e

-- todo position is wrong, it should be at the start of the list
commaNonSingle' :: (Syntax δ, Position δ p) => δ e -> δ a -> δ (Either ((p, [a]), e) a)
commaNonSingle' ex e =
  token "("
    ≫ ( left ⊣ position ⊗ (nil ⊣ token ")") ⊗ ex
          ∥ apply ⊣ e ⊗ (position ⊗ commaSome e ≪ token ")" ⊗ ex ⊕ token ")")
      )
  where
    apply = bimapP (firstP (secondP packList . toPrism swap_1_2_of_3) . toPrism associate') (toPrism unit') . toPrism distribute
    packList = cons . secondP cons . secondP (toPrism $ inverse nonEmpty)

multiarg core = multiargExclusionary core ∥ singleton ⊣ core

-- excludes single argument multiargs
multiargExclusionary :: Syntax p => p a -> p [a]
multiargExclusionary core = apply ⊣ keyword "multiarg" ≫ betweenParens (core ⊗ token "," ≫ space ≫ commaSeperatedSome core ⊕ always)
  where
    apply = branch (cons . secondP (cons . toPrism (inverse nonEmpty))) nil

withInnerPosition1 location core app = toPrism core . secondP app . toPrism (extractInfo $ location) . toPrism unit'

withInnerPosition location core app = toPrism core . secondP app . toPrism (extractInfo $ location . fst)

withInnerPosition3 location core app = toPrism core . secondP app . toPrism (extractInfo $ location . fst . fst) . toPrism associate'

path = (Path.path . swapNonEmpty) ⊣ token "/" ≫ identifer ⊗ pathTail
  where
    pathTail = cons ⊣ token "/" ≫ identifer ⊗ pathTail ∥ nil ⊣ always

semiPath = token "/" ≫ pathTail ∥ nil ⊣ always
  where
    pathTail = cons ⊣ identifer ⊗ (token "/" ≫ pathTail ∥ nil ⊣ always)

termIdentifier = Language.termIdentifier ⊣ identifer

termGlobalIdentifier = Language.termGlobalIdentifier ⊣ path

typeIdentifier = Language.typeIdentifier ⊣ identifer

typeGlobalIdentifier = Language.typeGlobalIdentifier ⊣ path

lowerBounds :: Syntax δ => δ a -> δ [a]
lowerBounds σ = items ∥ nil ⊣ always
  where
    items = cons ⊣ inverse nonEmpty ⊣ binaryToken ">=" ≫ seperatedSome σ (binaryToken "&")

typePattern ::
  (Syntax δ, Position δ p) =>
  δ (Language.TypePatternSource p)
typePattern =
  Language.typePatternSource ⊣ position ⊗ typeIdentifier ⊗ k ⊗ lowerBounds typeCore
  where
    k = token ":" ≫ typex

typeParen :: (Position δ p, Syntax δ) => δ (Language.TypeSource p)
typeParen = branch' (toPrism Language.typeSource . secondP Language.tuple) id ⊣ commaNonSingle typex

typex :: (Position δ p, Syntax δ) => δ (Language.TypeSource p)
typex = typeLambda
  where
    typeLambda = Language.typeSource ⊣ position ⊗ poly ∥ typeArrow
      where
        poly = Language.poly ⊣ label ⊗ body
          where
            label = ambiguous ∥# token "%[" ≫ typeCore ≪ token "]" ∥ ambiguous
              where
                ambiguous = Language.typeSource ⊣ position ⊗ (Language.ambiguousLabel ⊣ always)
            body = wrapType ⊣ scheme ≪ space ⊗ typeLambda
    typeArrow = applyBinary ⊣ typeEffect ⊗ ((partial ∥ full) ⊕ always)
      where
        applyBinary = inline `branchDistribute` unit'
        full = space ≫ token "-[" ≫ typex ⊗ token "]>" ≫ space ≫ typeArrow
        partial = binaryToken "->" ≫ unres ⊗ typeArrow
          where
            unres = Language.typeSource ⊣ position ⊗ (Language.unrestricted ⊣ always)
        inline = withInnerPosition3 Language.positionType Language.typeSource Language.inline
    typeEffect = effect `branchDistribute` unit' ⊣ typeUnique ⊗ (binaryKeyword "in" ≫ typeCore ⊕ always)
      where
        effect = withInnerPosition Language.positionType Language.typeSource Language.effect

typeUnique = Language.typeSource ⊣ position ⊗ unique ∥ typePtr
  where
    unique = Language.unique ⊣ prefixKeyword "unique" ≫ typePtr
    typePtr = foldlP apply ⊣ typeInt ⊗ many (token "*" ⊕ token "[" ≫ token "]" ⊕ binaryToken "@" ≫ typeInt)
      where
        apply = ptr `branchDistribute` arr `branchDistribute` shared
        ptr = withInnerPosition1 Language.positionType Language.typeSource Language.pointer
        arr = withInnerPosition1 Language.positionType Language.typeSource Language.array
        shared = withInnerPosition Language.positionType Language.typeSource Language.shared
    typeInt = integers ∥# apply ⊣ kindWord ⊗ (space ≫ keyword "integer" ≫ typeParen ⊕ always)
      where
        apply = num `branchDistribute` unit'
        num = withInnerPosition Language.positionType Language.typeSource Language.number
    kindWord = (word `branchDistribute` unit') ⊣ kindUni ⊗ (space ≫ keyword "word" ⊕ always)
      where
        word = withInnerPosition1 Language.positionType Language.typeSource Language.wordRep
    kindUni = Language.typeSource ⊣ position ⊗ upper ∥ typeCore
      where
        upper = Language.higher ⊣ token "+" ≫ kindUni

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
        Language.kind ⊣ keyword "kind" ≫ betweenAngle (typex ⊗ token "," ≫ space ≫ typex ⊗ token "," ≫ space ≫ typex),
        Language.representation ⊣ keyword "representation",
        Language.size ⊣ keyword "size",
        Language.signedness ⊣ keyword "signedness",
        Language.invariant ⊣ keyword "invariant",
        Language.subtypable ⊣ keyword "subtypable",
        Language.transparent ⊣ keyword "transparent",
        Language.opaque ⊣ keyword "opaque",
        Language.unrestricted ⊣ keyword "unrestricted",
        Language.linear ⊣ keyword "linear",
        Language.multiplicity ⊣ keyword "multiplicity",
        Language.step ⊣ keyword "step" ≫ betweenAngle (typex ≪ token "," ≪ space ⊗ typex),
        Language.top ⊣ token "/|\\",
        Language.orderability ⊣ keyword "orderability",
        Language.transparency ⊣ keyword "transparency",
        Language.universe ⊣ keyword "universe",
        Language.base ⊣ tokenNumeric 1 "u",
        Language.label ⊣ keyword "label",
        Language.ambiguousLabel ⊣ keyword "ambiguous",
        Language.hole ⊣ token "_"
      ]
    rotate = swap_2_3_of_3
    -- todo remove this eventually
    funLiteral = Language.functionLiteralType ⊣ rotate ⊣ prefixKeyword "internal" ≫ typeParen ⊗ binaryToken "=>" ≫ typex ⊗ binaryKeyword "uses" ≫ typeCore
    funPointer = Language.functionPointer ⊣ rotate ⊣ typeParen ⊗ binaryToken "=>" ≫ typex ⊗ binaryKeyword "uses" ≫ typeCore

newtype Scheme p = Scheme {runScheme :: [(p, Language.TypePatternSource p)]}

isoScheme = Isomorph Scheme runScheme

scheme :: (Syntax δ, Position δ p) => δ (Scheme p)
scheme = isoScheme ⊣ schema
  where
    schema = betweenAngle $ commaSeperatedManyLine (position ⊗ schemeCore)
    schemeCore = typePattern

wrapType :: Isomorph (Scheme p, Language.TypeSource p) (Language.TypeSchemeSource p)
wrapType =
  wrap Language.typeSchemeSource Language.typeForall
    . secondI
      (assumeIsomorph (toPrism Language.typeSchemeSource . secondP Language.monoType) . extractInfo Language.positionType)

wrapTerm :: Isomorph (Scheme p, Language.TermSource p) (Language.TermSchemeSource p)
wrapTerm =
  wrap Language.termSchemeSource Language.typeAbstraction
    . secondI
      (assumeIsomorph (toPrism Language.termSchemeSource . secondP Language.monoTerm) . extractInfo Language.positionTerm)

wrap c t =
  foldrP
    ( toPrism c
        . secondP
          (t . toPrism Language.bound)
        . toPrism associate
    )
    . firstI (inverse isoScheme)

typeAnnotate op =
  Language.typeSource ⊣ (position ⊗ (Language.hole ⊣ always))
    ∥# binaryToken op ≫ typex ∥ Language.typeSource ⊣ (position ⊗ (Language.hole ⊣ always))

termRuntimePatternParen :: (Position δ p, Syntax δ) => δ (Language.TermRuntimePatternSource p)
termRuntimePatternParen =
  branch' (toPrism Language.termRuntimePatternSource . secondP Language.runtimePatternTuple) id
    ⊣ commaNonSingle termRuntimePattern

termRuntimePattern :: (Position δ p, Syntax δ) => δ (Language.TermRuntimePatternSource p)
termRuntimePattern = patternCore
  where
    patternCore = Language.termRuntimePatternSource ⊣ position ⊗ choice options ∥ termRuntimePatternParen
      where
        options =
          [ Language.runtimePatternVariable ⊣ termIdentifier ⊗ typeAnnotate "::"
          ]

termPattern :: (Position δ p, Syntax δ) => δ (Language.TermPatternSource p)
termPattern = patternCore
  where
    patternCore = Language.termPatternSource ⊣ position ⊗ choice options ∥ betweenParens termPattern
      where
        options =
          [ Language.patternVariable ⊣ termIdentifier ⊗ typeAnnotate ":"
          ]

termParen :: (Position δ p, Syntax δ) => δ (Language.TermSource p)
termParen = branch' (toPrism Language.termSource . secondP Language.tupleIntroduction) id ⊣ commaNonSingle term

isStatement (Language.Term _ e) = isStatementF e

isStatementF (Language.Bind _ _) = True
isStatementF (Language.TermRuntime (Language.Alias _ _)) = True
isStatementF (Language.TermRuntime (Language.Loop _ _)) = True
isStatementF (Language.TermRuntime (Language.If _ _ _)) = True
isStatementF (Language.TermErasure (Language.Borrow _ _)) = True
isStatementF _ = False

termStatement :: (Position δ p, Syntax δ) => δ (Language.TermSource p)
termStatement = Language.termSource ⊣ position ⊗ choice options ∥ apply ⊣ term ⊗ (delimit ≫ termStatement ⊕ always)
  where
    options =
      [ Language.bind ⊣ rotateBind ⊣ prefixKeyword "inline" ≫ termPattern ≪ binaryToken "=" ⊗ term ≪ delimit ⊗ termStatement,
        Language.alias ⊣ rotateBind ⊣ prefixKeyword "let" ≫ termRuntimePattern ≪ binaryToken "=" ⊗ term ≪ delimit ⊗ termStatement,
        Language.loop ⊣ rotateBind ⊣ prefixKeyword "loop" ≫ betweenParens (prefixKeyword "let" ≫ termRuntimePattern ≪ binaryToken "=" ⊗ term) ⊗ lambdaBrace termStatement,
        Language.ifx ⊣ prefixKeyword "if" ≫ termCore ⊗ lambdaBrace termStatement ≪ binaryKeyword "else" ⊗ lambdaBrace termStatement,
        borrow
      ]
    borrow = Language.borrow ⊣ prefixKeyword "borrow" ≫ termCore ⊗ binaryKeyword "as" ≫ binding
      where
        binding = Language.bound ⊣ betweenAngle typePattern ⊗ binding'
          where
            binding' = Language.bound ⊣ termRuntimePatternParen ⊗ lambdaBrace termStatement

    rotateBind = secondI Language.bound . associate . firstI swap
    apply = withInnerPosition Language.positionTerm Language.termSource Language.dox `branchDistribute` unit'

term :: forall δ p. (Position δ p, Syntax δ) => δ (Language.TermSource p)
term = termLambda
  where
    termLambda = Language.termSource ⊣ position ⊗ (lambdas ∥# poly) ∥ termAnnotate
      where
        lambdas = termLambdas (pick isStatement never (lambdaCore term))
        poly = Language.polyIntroduction ⊣ wrapTerm ⊣ scheme ≪ space ⊗ term
    termAnnotate :: δ (Language.TermSource p)
    termAnnotate = apply ⊣ termOr ⊗ (binaryToken "::" ≫ typex ⊕ binaryToken ":" ≫ typex ⊕ always)
      where
        apply = preAnnotate `branchDistribute` annotate `branchDistribute` unit'
        annotate = withInnerPosition Language.positionTerm Language.termSource Language.typeAnnotation
        preAnnotate = withInnerPosition Language.positionTerm Language.termSource Language.preTypeAnnotation
    termOr = foldlP apply ⊣ termAnd ⊗ many (binaryToken "|" ≫ termAnd)
      where
        apply = withInnerPosition Language.positionTerm Language.termSource Language.or
    termAnd = foldlP apply ⊣ termEqual ⊗ many (binaryToken "&" ≫ termEqual)
      where
        apply = withInnerPosition Language.positionTerm Language.termSource Language.and
    termEqual = apply ⊣ termAdd ⊗ operators
      where
        i o = withInnerPosition Language.positionTerm Language.termSource (Language.relational o)
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
        add = withInnerPosition Language.positionTerm Language.termSource (Language.arithmatic Language.Addition)
        sub = withInnerPosition Language.positionTerm Language.termSource (Language.arithmatic Language.Subtraction)
    termMul = foldlP applyMul ⊣ termDeref ⊗ many (binaryToken "*" ≫ termDeref ⊕ binaryToken "/" ≫ termDeref)
      where
        applyMul = mul `branchDistribute` div
        mul = withInnerPosition Language.positionTerm Language.termSource (Language.arithmatic Language.Multiplication)
        div = withInnerPosition Language.positionTerm Language.termSource (Language.arithmatic Language.Division)
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
              Language.not ⊣ token "!" ≫ termPrefix,
              Language.isolatePointer ⊣ token "&*" ≫ termPrefix
            ]
    termIndex = Language.termSource ⊣ position ⊗ index ∥ termApply
      where
        index = Language.pointerIncrement ⊣ token "&" ≫ termApply ⊗ betweenSquares term
    termApply = foldlP applyBinary ⊣ termCore ⊗ many (applySyntax ⊕ rtApplySyntax ⊕ elimSyntax)
      where
        applyBinary = application `branchDistribute` rtApplication `branchDistribute` elimatePoly
        application = withInnerPosition Language.positionTerm Language.termSource Language.inlineApplication
        rtApplication = withInnerPosition Language.positionTerm Language.termSource Language.functionApplication
        elimatePoly = withInnerPosition1 Language.positionTerm Language.termSource Language.polyElimination
        applySyntax = space ≫ token "!" ≫ termCore
        rtApplySyntax = space ≫ termParen
        elimSyntax = space ≫ token "<_>"

termLambdas e = Language.inlineAbstraction ⊣ Language.bound ⊣ token "\\" ≫ termPattern ⊗ e

termCore :: forall δ p. (Position δ p, Syntax δ) => δ (Language.TermSource p)
termCore = Language.termSource ⊣ position ⊗ choice options ∥ pick isStatement (betweenBraces termStatement) termParen
  where
    options =
      [ Language.variable ⊣ termIdentifier,
        Language.globalVariable ⊣ termGlobalIdentifier,
        Language.extern ⊣ prefixKeyword "extern" ≫ symbol,
        Language.numberLiteral ⊣ number,
        Language.truex ⊣ keyword "true",
        Language.falsex ⊣ keyword "false",
        Language.break ⊣ prefixKeyword "break" ≫ termCore,
        Language.continue ⊣ prefixKeyword "continue" ≫ termCore,
        Language.wrap ⊣ prefixKeyword "wrap" ≫ termCore,
        Language.unwrap ⊣ prefixKeyword "unwrap" ≫ termCore,
        termLambdas (lambdaBrace termStatement ∥ lambdaCore term)
      ]

itemSingleton ::
  (Syntax δ, Position δ p) => δ (Module.Item (Module.GlobalSource p))
itemSingleton = inverse (assumeIsomorph singletonMap) ⊣ items (keyword "this")

data Item p
  = InlineDeclare (Language.TypeSchemeSource p)
  | InlineDefine (Language.TermControlSource p)
  | TextDeclare (Language.TypeSchemeSource p)
  | TextDefine (Language.TermControlSource p)
  | Synonym (Language.TypeSource p)
  | NewtypeDeclare (Language.TypeSource p)
  | NewTypeDefine (Language.TypeSource p)
  | Module (Module.Module (Module.GlobalSource p))

inlineDeclareP = Prism InlineDeclare $ \case
  (InlineDeclare e) -> Just e
  _ -> Nothing

inlineDefineP = Prism InlineDefine $ \case
  (InlineDefine e) -> Just e
  _ -> Nothing

textDeclareP = Prism TextDeclare $ \case
  (TextDeclare e) -> Just e
  _ -> Nothing

textDefineP = Prism TextDefine $ \case
  (TextDefine e) -> Just e
  _ -> Nothing

synonymP = Prism Synonym $ \case
  (Synonym σ) -> Just σ
  _ -> Nothing

newTypeDeclareP = Prism NewtypeDeclare $ \case
  (NewtypeDeclare σ) -> Just σ
  _ -> Nothing

newTypeDefineP = Prism NewTypeDefine $ \case
  (NewTypeDefine σ) -> Just σ
  _ -> Nothing

moduleP = Prism Module $ \case
  (Module m) -> Just m
  _ -> Nothing

inline :: (Syntax δ, Position δ p) => δ a -> δ (a, Item p)
inline name = prefixKeyword "inline" ≫ name ⊗ (apply ⊣ scoped ⊕ plain)
  where
    scoped = scheme ⊗ (plain ⊕ binaryToken ":" ≫ typex ≪ delimit)
    plain = binaryToken "=" ≫ term ≪ delimit'

    apply = applyDefine `branchDistribute` applyDeclare `branch` applyPlain
    applyDefine = inlineDefineP . Language.termManualSource . toPrism wrapTerm
    applyPlain = inlineDefineP . Language.termAutoSource
    applyDeclare = inlineDeclareP . toPrism wrapType

    delimit' = delimit ≪ line

-- todo disallow type declerations with patterns without type annotations
text :: (Syntax δ, Position δ p) => δ a -> δ (a, Syntax.Item p)
text name = name ⊗ (applyDefine `branchDistribute` applyDeclare `branch` applyPlain ⊣ scoped ⊕ plain)
  where
    scoped = position ⊗ scheme ⊗ termRuntimePatternParen ⊗ (lambdaBrace termStatement ≪ line ⊕ binaryToken "::" ≫ typeUnique ⊗ binaryKeyword "in" ≫ typex ≪ delimit)
    plain = position ⊗ (termRuntimePatternParen ⊗ lambdaBrace termStatement ≪ line)

    applyDefine = textDefineP . Language.termManualSource . toPrism wrapTerm . secondP (toPrism Language.termSource . secondP Language.functionLiteral . secondP (toPrism Language.bound)) . toPrism morphTerm
    applyDeclare = textDeclareP . toPrism wrapType . secondP (toPrism Language.typeSource . secondP Language.functionLiteralType . secondP (firstP (firstP $ toPrism Language.patternType))) . toPrism morphType
    applyPlain = textDefineP . Language.termAutoSource . toPrism Language.termSource . secondP (Language.functionLiteral . toPrism Language.bound)

    morphType ::
      Isomorph
        (((p, scheme), pattern), (return, region))
        (scheme, (p, ((pattern, region), return)))
    morphType =
      Isomorph
        (\(((p, scheme), pattern), (return, region)) -> (scheme, (p, ((pattern, region), return))))
        (\(scheme, (p, ((pattern, region), return))) -> (((p, scheme), pattern), (return, region)))

    morphTerm ::
      Isomorph
        (((p, scheme), pattern), term)
        (scheme, (p, (pattern, term)))
    morphTerm =
      Isomorph
        (\(((p, scheme), pattern), term) -> (scheme, (p, (pattern, term))))
        (\(scheme, (p, (pattern, term))) -> (((p, scheme), pattern), term))

synonym name = prefixKeyword "type" ≫ name ⊗ binaryToken "=" ≫ (synonymP ⊣ typex) ≪ delimit

newType name = prefixKeyword "wrapper" ≫ name ⊗ (declare ∥ define)
  where
    declare = binaryToken ":" ≫ (newTypeDeclareP ⊣ typex) ≪ delimit
    define = binaryToken "=" ≫ (newTypeDefineP ⊣ typex) ≪ delimit

modulex :: (Syntax δ, Position δ p) => δ a -> δ (a, Syntax.Item p)
modulex name = prefixKeyword "module" ≫ name ⊗ (scoped ∥ inline)
  where
    scoped = space ≫ token "=" ≫ lambdaBrace contents ≪ token ";"
    inline = delimit ≫ contents
    contents = moduleP ⊣ Module.coreModule ⊣ items identifer

items :: (Syntax δ, Position δ p, Show x, Ord x) => δ x -> δ (Map x (Module.Item (Module.GlobalSource p)))
items name = groupItems $ orderlessMulti ⊣ list ⊣ left ⊣ some (inline name ∥ text name ∥ modulex name ∥ synonym name ∥ newType name)

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
  groupItems (Parser parser) = Parser $ do
    items <- parser
    flip Map.traverseWithKey items $ \k -> \case
      (InlineDefine e :| []) -> pure $ Module.Global $ Module.GlobalSource $ Module.Inline Nothing e
      (InlineDeclare ς :| [InlineDefine e]) -> pure $ Module.Global $ Module.GlobalSource $ Module.Inline (Just ς) e
      (TextDefine e :| []) -> pure $ Module.Global $ Module.GlobalSource $ Module.Text Nothing e
      (TextDeclare ς :| [TextDefine e]) -> pure $ Module.Global $ Module.GlobalSource $ Module.Text (Just ς) e
      (Synonym σ :| []) -> pure $ Module.Global $ Module.GlobalSource $ Module.Synonym σ
      (NewtypeDeclare κ :| [NewTypeDefine σ]) -> pure $ Module.Global $ Module.GlobalSource $ Module.NewType κ σ
      (Module m :| []) -> pure $ Module.Module m
      _ -> fail $ "unknown module item for " ++ show k

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

instance Position Parser () where
  position = Parser $ pure ()

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
  groupItems (Printer printer) = Printer $ \items -> printer (fmap convert items)
    where
      convert (Module.Module m) = Module m :| []
      convert (Module.Global (Module.GlobalSource (Module.Inline Nothing e))) = InlineDefine e :| []
      convert (Module.Global (Module.GlobalSource (Module.Inline (Just ς) e))) = InlineDeclare ς :| [InlineDefine e]
      convert (Module.Global (Module.GlobalSource (Module.Text Nothing e))) = TextDefine e :| []
      convert (Module.Global (Module.GlobalSource (Module.Text (Just ς) e))) = TextDeclare ς :| [TextDefine e]
      convert (Module.Global (Module.GlobalSource (Module.NewType κ σ))) = NewtypeDeclare κ :| [NewTypeDefine σ]
      convert (Module.Global (Module.GlobalSource (Module.Synonym σ))) = Synonym σ :| []

instance Position Printer () where
  position = Printer $ \() -> Just $ pure ()
