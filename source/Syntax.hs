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
      "signed",
      "unsigned",
      "inline",
      "let",
      "extern",
      "module",
      "import",
      "symbol"
    ]

-- to allow for correct pretty printing right recursion should be limited to an equal or higher precedence level

class SyntaxBase δ => Syntax δ where
  token :: String -> δ ()
  keyword :: String -> δ ()
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

binaryToken op = space ≫ token op ≫ space

prefixKeyword word = keyword word ≫ space

betweenParens = between (token "(") (token ")")

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

sort :: Syntax δ => δ Language.Sort
sort =
  choice
    [ Language.kind ⊣ token "[" ≫ space ≫ token "]",
      Language.existance ⊣ keyword "existance",
      Language.representation ⊣ keyword "representation",
      Language.size ⊣ keyword "size",
      Language.signedness ⊣ keyword "signedness"
    ]

kindPattern :: (Position δ p, Syntax δ) => δ (Language.Pattern Language.KindIdentifier Language.Sort p)
kindPattern = Language.pattern ⊣ position ⊗ kindIdentifier ⊗ token ":" ≫ sort

kind :: (Position δ p, Syntax δ) => δ (Language.KindSource p)
kind = kindTop
  where
    kindTop = Language.kindSource ⊣ position ⊗ (Language.real ⊣ token "#" ≫ kindPrefix ≪ token "#") ∥ kindPrefix
    kindPrefix = Language.kindSource ⊣ position ⊗ choice options ∥ kindCore
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
        Language.imaginary ⊣ keyword "imaginary",
        Language.region ⊣ keyword "region",
        Language.pointerRep ⊣ keyword "pointer",
        Language.structRep ⊣ prefixKeyword "struct" ≫ betweenParens (commaSeperatedMany kind),
        Language.byte ⊣ keyword "byte",
        Language.short ⊣ keyword "short",
        Language.int ⊣ keyword "int",
        Language.long ⊣ keyword "long",
        Language.signed ⊣ keyword "signed",
        Language.unsigend ⊣ keyword "unsigned"
      ]

kindCoreAuto :: (Position δ p, Syntax δ) => δ (Maybe (Language.KindSource p))
kindCoreAuto = just ⊣ kindCore ∥ nothing ⊣ token "_"

kindAuto :: (Position δ p, Syntax δ) => δ (Maybe (Language.KindSource p))
kindAuto = just ⊣ kind ∥ nothing ⊣ token "_"

constraint :: Syntax δ => δ Language.Constraint
constraint = Language.copy ⊣ keyword "copy" ≫ always

constraints :: Syntax δ => δ (Set Language.Constraint)
constraints = orderlessSet ⊣ (items ∥ nil ⊣ always)
  where
    items = cons ⊣ inverse nonEmpty ⊣ binaryToken "+" ≫ seperatedSome (constraint) (binaryToken "&")

lowerBounds :: Syntax δ => δ a -> δ [a]
lowerBounds σ = items ∥ nil ⊣ always
  where
    items = cons ⊣ inverse nonEmpty ⊣ binaryToken ">=" ≫ seperatedSome σ (binaryToken "&")

typePattern ::
  (Syntax δ, Position δ p) =>
  δ (Language.Pattern Language.TypeIdentifier (Maybe (Language.KindSource p)) p)
typePattern = Language.pattern ⊣ position ⊗ typeIdentifier ⊗ (just ⊣ token ":" ≫ kind ∥ nothing ⊣ always)

constraintBound :: Prism (((pm, c), π), σ) ((Language.Bound pm σ, c), π)
constraintBound = firstP (firstP (toPrism Language.bound)) . toPrism transform
  where
    transform :: Isomorph (((pm, c), π), σ) (((pm, σ), c), π)
    transform = Isomorph (\(((pm, c), π), σ) -> (((pm, σ), c), π)) (\(((pm, σ), c), π) -> (((pm, c), π), σ))

typex :: (Position δ p, Syntax δ) => δ (Language.TypeSource p)
typex = typeArrow
  where
    typeArrow = applyBinary ⊣ typeEffect ⊗ (binaryToken "-`>" ≫ typeArrow ⊕ always)
      where
        applyBinary = inline `branchDistribute` unit'
        inline = withInnerPosition Language.typeSource Language.inline
    typeEffect = effect `branchDistribute` unit' ⊣ typeRTArrow ⊗ (binaryToken "@" ≫ typeCore ⊕ always)
      where
        effect = withInnerPosition Language.typeSource Language.effect
    typeRTArrow = applyBinary ⊣ typePair ⊗ (binaryToken "-*>" ≫ typeCore ≪ space ⊗ typeRTArrow ⊕ binaryToken "->" ≫ typeCore ≪ space ⊗ typeRTArrow ⊕ always)
      where
        applyBinary = functionPointer `branchDistribute` functionLiteralType `branchDistribute` unit'
        functionPointer = withInnerPosition3 Language.typeSource Language.functionPointer . toPrism associate'
        functionLiteralType = withInnerPosition3 Language.typeSource Language.functionLiteralType . toPrism associate'
    typePair = foldlP pair ⊣ typePtr ⊗ many (token "," ≫ space ≫ typePtr)
      where
        pair = withInnerPosition Language.typeSource Language.runtimePair
    typePtr = foldlP ptr ⊣ typeCore ⊗ many (token "*" ≫ binaryToken "@" ≫ typeCore)
      where
        ptr = withInnerPosition Language.typeSource Language.reference . toPrism swap

typeCore :: (Position δ p, Syntax δ) => δ (Language.TypeSource p)
typeCore = Language.typeSource ⊣ position ⊗ (choice options) ∥ betweenParens typex
  where
    options =
      [ Language.typeVariable ⊣ typeIdentifier,
        Language.number ⊣ token "#" ≫ kindCoreAuto ⊗ space ≫ kindCoreAuto,
        Language.explicitForall ⊣ constraintBound ⊣ token "\\/" ≫ typePattern ⊗ constraints ⊗ lowerBounds typeCore ⊗ lambdaInline typex,
        Language.ofCourse ⊣ betweenBangSquares typex
      ]

typeAuto :: (Position δ p, Syntax δ) => δ (Maybe (Language.TypeSource p))
typeAuto = just ⊣ typex ∥ nothing ⊣ token "_"

typeCoreAuto :: (Position δ p, Syntax δ) => δ (Maybe (Language.TypeSource p))
typeCoreAuto = just ⊣ typeCore ∥ nothing ⊣ token "_"

scheme ::
  (Syntax δ, Position δ p) =>
  δ
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
scheme = (cons ⊣ inverse nonEmpty ⊣ betweenAngle (commaSeperatedSome (position ⊗ schemeCore))) ∥ nil ⊣ always
  where
    schemeCore = typePattern ⊗ constraints ⊗ lowerBounds typeCore ⊕ token "'" ≫ kindPattern

typeScheme :: (Position δ p, Syntax δ) => δ (Language.TypeSchemeSource p)
typeScheme = foldrP applyScheme ⊣ (scheme ⊗ space ≫ mono)
  where
    mono = Language.typeSchemeSource ⊣ position ⊗ (Language.monoType ⊣ typex)
    applyScheme = toPrism Language.typeSchemeSource . secondP inner . toPrism associate
      where
        inner = (Language.forallx . constraintBound) `branchDistribute'` (Language.kindForall . toPrism Language.bound)

termRuntimePattern :: (Position δ p, Syntax δ) => δ (Language.TermRuntimePatternSource p)
termRuntimePattern = patternTop
  where
    patternTop = Language.termRuntimePatternSource ⊣ position ⊗ variableLong ∥ patternPair
      where
        variableLong = try $ Language.runtimePatternVariable ⊣ termIdentifier ⊗ (just ⊣ binaryToken ":" ≫ typex)
    patternPair = foldlP pair ⊣ patternCore ⊗ many (binaryToken "," ≫ patternCore)
      where
        pair = withInnerPosition Language.termRuntimePatternSource Language.runtimePatternPair
    patternCore = Language.termRuntimePatternSource ⊣ position ⊗ choice options ∥ betweenParens patternTop
      where
        options =
          [ Language.runtimePatternVariable ⊣ termIdentifier ⊗ (nothing ⊣ always)
          ]

termPattern :: (Position δ p, Syntax δ) => δ (Language.TermPatternSource p)
termPattern = patternTop
  where
    patternTop = Language.termPatternSource ⊣ position ⊗ variableLong ∥ patternPair
      where
        variableLong = try $ Language.patternVariable ⊣ termIdentifier ⊗ (just ⊣ binaryToken ":" ≫ typex)
    patternPair = patternCore
    patternCore = Language.termPatternSource ⊣ position ⊗ choice options ∥ betweenParens patternTop
      where
        options =
          [ Language.patternVariable ⊣ termIdentifier ⊗ (nothing ⊣ always),
            Language.patternOfCourse ⊣ betweenBangSquares patternTop
          ]

term :: (Position δ p, Syntax δ) => δ (Language.TermSource p)
term = termBinding
  where
    optionalAnnotate e = e ⊗ pass ∥# betweenParens (term ⊗ annotate) ∥ e ⊗ pass
      where
        annotate = just ⊣ binaryToken ":" ≫ typex ∥ pass
        pass = nothing ⊣ always
    semiBinaryToken t = space ≫ token t
    termBinding = Language.termSource ⊣ position ⊗ choice options ∥ termRTApply
      where
        options =
          [ Language.bind ⊣ rotateBind ⊣ prefixKeyword "inline" ≫ termPattern ≪ binaryToken "=" ⊗ term ≪ token ";" ≪ line ⊗ term,
            Language.alias ⊣ rotateBind ⊣ prefixKeyword "let" ≫ termRuntimePattern ≪ binaryToken "=" ⊗ term ≪ token ";" ≪ line ⊗ term
          ]
        rotateBind = secondI Language.bound . associate . firstI swap
    termRTApply = applyBinary ⊣ termAdd ⊗ (binaryToken "$" ≫ optionalAnnotate termRTApply ⊕ always)
      where
        applyBinary = apply `branchDistribute` unit'
        apply = withInnerPosition3 Language.termSource Language.functionApplication . toPrism associate'
    signMarker = just ⊣ token "'" ≫ kindCore ≪ space ∥ nothing ⊣ space
    termAdd = foldlP applyAdd ⊣ termMul ⊗ many (semiBinaryToken "+" ≫ (swap ⊣ signMarker ⊗ termMul) ⊕ semiBinaryToken "-" ≫ (swap ⊣ signMarker ⊗ termMul))
      where
        applyAdd = add `branchDistribute` sub
        add = withInnerPosition3 Language.termSource (Language.arithmatic Language.Addition) . toPrism associate'
        sub = withInnerPosition3 Language.termSource (Language.arithmatic Language.Subtraction) . toPrism associate'
    termMul = foldlP applyMul ⊣ termPair ⊗ many (semiBinaryToken "*" ≫ (swap ⊣ signMarker ⊗ termPair) ⊕ semiBinaryToken "/" ≫ (swap ⊣ signMarker ⊗ termPair))
      where
        applyMul = mul `branchDistribute` div
        mul = withInnerPosition3 Language.termSource (Language.arithmatic Language.Multiplication) . toPrism associate'
        div = withInnerPosition3 Language.termSource (Language.arithmatic Language.Division) . toPrism associate'
    termPair = foldlP pair ⊣ termApply ⊗ many (token "," ≫ space ≫ termApply)
      where
        pair = withInnerPosition Language.termSource Language.runtimePairIntrouction
    termApply = Language.termSource ⊣ position ⊗ choice options ∥ foldlP applyBinary ⊣ termCore ⊗ many (applySyntax ⊕ typeApplySyntax)
      where
        applyBinary = application `branchDistribute` typeApplication
        application = withInnerPosition3 Language.termSource Language.inlineApplication . toPrism associate'
        typeApplication = withInnerPosition5 Language.termSource Language.typeApplication . toPrism transform
          where
            transform = Isomorph (\(e, (((pm, c), π), σ)) -> ((((e, σ), pm), c), π)) (\((((e, σ), pm), c), π) -> (e, (((pm, c), π), σ)))
        applySyntax = space ≫ token "`" ≫ optionalAnnotate termCore
        typeApplySyntax =
          space
            ≫ betweenDoubleSquares (constraintBound ⊣ token "\\/" ≫ typePattern ⊗ constraints ⊗ lowerBounds typeCoreAuto ⊗ lambdaInline typeAuto) ⊗ betweenAngle typeAuto
        options =
          [ Language.readReference ⊣ token "*" ≫ termApply
          ]

termCore :: (Position δ p, Syntax δ) => δ (Language.TermSource p)
termCore = Language.termSource ⊣ position ⊗ choice options ∥ betweenParens term
  where
    options =
      [ Language.variable ⊣ termIdentifier ⊗ always,
        Language.inlineAbstraction ⊣ Language.bound ⊣ token "`\\" ≫ termPattern ⊗ lambdaMajor term,
        Language.functionLiteral ⊣ Language.bound ⊣ token "\\" ≫ termRuntimePattern ⊗ lambdaMajor term,
        Language.extern ⊣ prefixKeyword "extern" ≫ symbol ≪ space ⊗ typeCoreAuto ≪ binaryToken "->" ⊗ typeCoreAuto ≪ space ⊗ typeCoreAuto,
        Language.ofCourseIntroduction ⊣ betweenBangSquares term,
        Language.numberLiteral ⊣ number,
        Language.typeLambda ⊣ constraintBound ⊣ token "/\\" ≫ typePattern ⊗ constraints ⊗ lowerBounds typeCoreAuto ⊗ lambdaMajor term
      ]

modulex ::
  (Syntax δ, Position δ p) =>
  δ (Module.Module (Module.GlobalSource p))
modulex =
  Module.coreModule ⊣ orderless ⊣ list
    ⊣ some
      (item (space ≫ identifer) (binaryToken "=") (token ";" ≫ line) lambdaMajor)
    ⊕ never

item ::
  forall a δ p.
  (Position δ p, Syntax δ) =>
  δ a ->
  δ () ->
  δ () ->
  (δ (Module.Module (Module.GlobalSource p)) -> δ (Module.Module (Module.GlobalSource p))) ->
  δ (a, Module.Item (Module.GlobalSource p))
item name delimit footer lambda =
  choice
    [ itemCore "module" (Module.modulex ⊣ lambda modulex),
      itemTerm "inline" (Module.global . Module.inline),
      itemCore "import" (Module.global . Module.importx ⊣ position ⊗ path),
      itemTerm "symbol" (Module.global . Module.text)
    ]
  where
    itemCore brand inner = keyword brand ≫ name ≪ delimit ⊗ inner ≪ footer
    itemTerm brand wrap = keyword brand ≫ (secondP wrap ⊣ correct ⊣ (annotated ∥ (nothing ⊣ always) ⊗ binding))
      where
        correct = associate . firstI swap . associate'
        mono = Language.termSchemeSource ⊣ position ⊗ (Language.monoTerm ⊣ term)
        binding :: δ (a, Language.TermSchemeSource p)
        binding = secondI (foldrP (toPrism Language.termSchemeSource . secondP inner . toPrism associate)) . associate ⊣ name ⊗ scheme ⊗ delimit ≫ mono ≪ footer
        inner = (Language.implicitTypeLambda . constraintBound) `branchDistribute'` (Language.implicitKindLambda . toPrism Language.bound)
        annotated = space ≫ token "_" ≫ binaryToken "::" ≫ (just ⊣ typeScheme) ≪ token ";" ≪ line ≪ keyword brand ⊗ binding

itemSingleton ::
  (Syntax δ, Position δ p) => δ (Module.Item (Module.GlobalSource p))
itemSingleton = unit ⊣ item always (token ":" ≫ line) always id

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

instance Position Printer Internal where
  position = Printer $ \Internal -> Just $ pure ()
