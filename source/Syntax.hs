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
import qualified Core.Ast.Pattern as Core
import qualified Core.Ast.RuntimePattern as Core
import qualified Core.Ast.Sort as Core
import qualified Core.Ast.Term as Core
import qualified Core.Ast.Type as Core
import qualified Core.Ast.TypePattern as Core
import Data.Char (isAlphaNum)
import Data.Maybe (fromJust)
import Data.Void (Void)
import Misc.Identifier
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

-- to allow for correct pretty printing right recursion is limited to an equal or higher precedence level

class SyntaxBase δ => Syntax δ where
  string :: String -> δ ()
  identifer :: δ Identifier
  stringLiteral :: δ String

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

betweenTypeParens = between (token "`(") (token ")")

betweenAngle = between (token "<") (token ">")

betweenKindParens = between (token "``(") (token ")")

betweenBraces = between (token "{") (token "}")

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

path = (Path.path . swapNonEmpty) ⊣ token "/" ≫ identifer ⊗ pathTail
  where
    pathTail = cons ⊣ token "/" ≫ identifer ⊗ pathTail ∥ nil ⊣ always

semiPath = token "/" ≫ pathTail ∥ nil ⊣ always
  where
    pathTail = cons ⊣ identifer ⊗ (token "/" ≫ pathTail ∥ nil ⊣ always)

sort =
  choice
    [ Core.kind ⊣ keyword "kind",
      Core.stage ⊣ keyword "stage",
      Core.impact ⊣ keyword "impact",
      Core.existance ⊣ keyword "existance",
      Core.representation ⊣ keyword "representation"
    ]

kindPattern = Core.coreKindPattern ⊣ position ⊗ core
  where
    core = Core.kindPatternVariable ⊣ identifer ⊗ token ":" ≫ sort

kind = kindBottom
  where
    kindLambda lambda = Core.coreKind ⊣ position ⊗ core
      where
        core = Core.poly ⊣ Core.bound ⊣ token "`\\/" ≫ kindPattern ⊗ lambda kind
    kindBottom = kindLambda lambdaCore ∥# higher `branchDistribute` unit' ⊣ kindCore ⊗ (binaryToken "->" ≫ kind ⊕ always)
      where
        higher = withInnerPosition Core.coreKind Core.higher
    kindCore = kindLambda lambdaInline ∥ core ∥ betweenParens kind
      where
        core =
          Core.coreKind ⊣ position
            ⊗ choice
              [ Core.kindVariable ⊣ identifer,
                Core.typex ⊣ prefixKeyword "type" ≫ kindCore,
                Core.runtime ⊣ prefixKeyword "runtime" ≫ kindCore ⊗ space ≫ kindCore,
                Core.code ⊣ keyword "code",
                Core.datax ⊣ keyword "data",
                Core.imaginary ⊣ keyword "imaginary",
                Core.real ⊣ prefixKeyword "real" ≫ kindCore,
                Core.constraint ⊣ keyword "constraint",
                Core.region ⊣ prefixKeyword "region",
                Core.meta ⊣ keyword "meta",
                Core.text ⊣ keyword "text",
                Core.pointerRep ⊣ keyword "pointer",
                Core.structRep ⊣ prefixKeyword "struct" ≫ betweenParens (commaSeperatedMany kind)
              ]

typePattern = Core.coreTypePattern ⊣ position ⊗ core
  where
    core = Core.typePatternVariable ⊣ identifer ⊗ (token ":" ≫ kind)

data Mode = Runtime | Meta deriving (Eq)

typex mode = typeBottom
  where
    typeParens = case mode of
      Runtime -> foldlP runtimePair ⊣ betweenParens (inverse nonEmpty ⊣ commaSeperatedSome typeBottom)
        where
          runtimePair = withInnerPosition Core.coreType Core.runtimePair
      Meta -> betweenParens typeBottom
    typeLambda lambda = Core.coreType ⊣ position ⊗ choice options
      where
        options =
          [ Core.forallx ⊣ Core.bound ⊣ token "`\\/" ≫ typePattern ⊗ lambda typeBottom,
            Core.kindForall ⊣ Core.bound ⊣ token "``\\/" ≫ kindPattern ⊗ lambda typeBottom,
            Core.typeOperator ⊣ Core.bound ⊣ token "\\" ≫ typePattern ⊗ lambda typeBottom,
            Core.polyOperator ⊣ Core.bound ⊣ token "`\\" ≫ kindPattern ⊗ lambda typeBottom,
            recursive,
            Core.qualifiedx ⊣ prefixKeyword "when" ≫ typeBottom ⊗ lambda typeBottom
          ]
        recursive = case mode of
          Runtime -> Core.recursive ⊣ Core.bound ⊣ prefixKeyword "recursive" ≫ typePattern ⊗ lambda typeBottom
          Meta -> never
    typeBottom = case mode of
      Runtime -> pick ((== Runtime) . categorize) typeBase (token "~" ≫ typex Meta)
      Meta -> pick ((== Meta) . categorize) typeBase (token "#" ≫ typex Runtime)
    typeBase =
      typeLambda lambdaCore ∥# case mode of
        Meta -> applyBinary ⊣ typePostfix ⊗ binary
          where
            applyBinary = applyBinaryCommon `branchDistribute` unit'
            binary = binaryCommon ⊕ always
        Runtime -> applyBinary ⊣ typePostfix ⊗ binary
          where
            applyBinary = applyBinaryCommon `branchDistribute` functionLiteralType `branchDistribute` unit'
            binary = binaryCommon ⊕ (space ≫ prefixKeyword "function" ≫ typeBottom) ⊕ always
            functionLiteralType = withInnerPosition Core.coreType Core.functionLiteralType
      where
        binaryCommon = binaryToken "->" ≫ typeBottom
        applyBinaryCommon = arrow
        arrow = withInnerPosition Core.coreType prism
          where
            prism = case mode of
              Meta -> Core.macro
              Runtime -> Core.functionPointer

    typePostfix = foldlP applyPostfix ⊣ typeCore ⊗ many postfix
      where
        applyPostfix = polyConstruction `branchDistribute` typeConstruction
        postfix = space ≫ betweenTypeParens kind ⊕ space ≫ typeCore
        typeConstruction = withInnerPosition Core.coreType Core.typeConstruction
        polyConstruction = withInnerPosition Core.coreType Core.polyConstruction
    typeCore = typeLambda lambdaInline ∥ core ∥ typeParens
      where
        core = Core.coreType ⊣ position ⊗ choice options
        options =
          [Core.typeVariable ⊣ identifer] ++ case mode of
            Meta -> [Core.ofCourse ⊣ token "!" ≫ typeCore]
            Runtime ->
              [ Core.regionTransformer ⊣ prefixKeyword "state" ≫ typeCore ⊗ space ≫ typeCore,
                Core.regionReference ⊣ prefixKeyword "reference" ≫ typeCore ⊗ space ≫ typeCore,
                Core.regionSubtype ⊣ prefixKeyword "outlive" ≫ typeCore ⊗ space ≫ typeCore,
                Core.copy ⊣ prefixKeyword "copy" ≫ typeCore
              ]
    categorize (Core.CoreType _ σ) = go σ
      where
        go (Core.TypeVariable _) = mode
        go (Core.Macro _ _) = Meta
        go (Core.Forall _) = mode
        go (Core.KindForall _) = mode
        go (Core.OfCourse _) = Meta
        go (Core.TypeConstruction _ _) = mode
        go (Core.TypeOperator _) = mode
        go (Core.PolyConstruction _ _) = mode
        go (Core.PolyOperator _) = mode
        go (Core.FunctionPointer _ _) = Runtime
        go (Core.FunctionLiteralType _ _) = Runtime
        go (Core.Qualified _ _) = mode
        go (Core.Copy _) = Runtime
        go (Core.RuntimePair _ _) = Runtime
        go (Core.Recursive _) = Runtime
        go (Core.RegionTransformer _ _) = Runtime
        go (Core.RegionReference _ _) = Runtime
        go (Core.RegionSubtype _ _) = Runtime

pattern = patternBottom
  where
    patternBottom = Core.corePattern ⊣ position ⊗ variable ∥ patternCore
      where
        variable = Core.patternVariable ⊣ identifer ⊗ token ":" ≫ typex Meta
    patternCore = Core.corePattern ⊣ position ⊗ patternOfCourse ∥ betweenParens pattern
      where
        patternOfCourse = Core.patternOfCourse ⊣ token "!" ≫ patternCore

runtimePatternParens = foldlP runtimePatternPair ⊣ betweenParens (inverse nonEmpty ⊣ commaSeperatedSome runtimePattern)
  where
    runtimePatternPair = withInnerPosition Core.coreRuntimePattern Core.runtimePatternPair

runtimePatternMultiarg = multiarg runtimePattern

runtimePattern = patternBottom
  where
    patternBottom = Core.coreRuntimePattern ⊣ position ⊗ variable ∥ runtimePatternParens
      where
        variable = Core.runtimePatternVariable ⊣ identifer ⊗ token ":" ≫ typex Runtime

term mode = termBottom
  where
    typexx = typex mode
    binderPattern name = prefixKeyword name ≫ pattern ≪ binaryToken "=" ⊗ termBottom ≪ token ";" ⊗ line ≫ termBottom
    binderRuntimeCore name = prefixKeyword name ≫ runtimePattern ≪ binaryToken "=" ⊗ termBottom
    binderRuntime name = binderRuntimeCore name ≪ token ";" ⊗ line ≫ termBottom
    termParens = case mode of
      Runtime -> foldlP runtimePairIntrouction ⊣ betweenParens (inverse nonEmpty ⊣ commaSeperatedSome termBottom)
        where
          runtimePairIntrouction = withInnerPosition Core.coreTerm Core.runtimePairIntrouction
      Meta -> betweenParens termBottom
    termLambda lambda =
      Core.coreTerm ⊣ position
        ⊗ choice
          [ Core.typeAbstraction ⊣ Core.bound ⊣ token "`\\" ≫ typePattern ⊗ lambda termBottom,
            Core.kindAbstraction ⊣ Core.bound ⊣ token "``\\" ≫ kindPattern ⊗ lambda termBottom,
            Core.qualifiedAssume ⊣ prefixKeyword "when" ≫ typexx ⊗ lambda termBottom
          ]
    termBottom = case mode of
      Meta -> pick ((== Meta) . categorize) termBase (token "#" ≫ term Runtime)
      Runtime -> pick ((== Runtime) . categorize) termBase (token "~" ≫ term Meta)
    termBase =
      termLambda lambdaCore ∥# binding ∥ foldlP applyPostfix ⊣ termCore ⊗ many (space ≫ postfix)
      where
        binding =
          let rotateBind = secondI Core.bound . associate . firstI swap
           in Core.coreTerm ⊣ position ⊗ case mode of
                Meta -> Core.bind ⊣ rotateBind ⊣ binderPattern "let"
                Runtime -> letx ∥ doRegionTransformer
                  where
                    letx = Core.alias ⊣ rotateBind ⊣ binderRuntime "let"
                    doRegionTransformer = Core.doRegionTransformer ⊣ rotateBind ⊣ binderRuntime "do"
        applyPostfix = typeApplication `branchDistribute` kindApplication `branchDistribute` qualifiedCheck `branchDistribute` application
        postfix = betweenTypeParens typexx ⊕ betweenKindParens kind ⊕ token "?" ⊕ termCore
        application = withInnerPosition Core.coreTerm $ case mode of
          Meta -> Core.macroApplication
          Runtime -> Core.functionApplication
        typeApplication = withInnerPosition Core.coreTerm Core.typeApplication
        kindApplication = withInnerPosition Core.coreTerm Core.kindApplication
        qualifiedCheck = withInnerPosition Core.coreTerm (Core.qualifiedCheck . toPrism unit')
    termCore = core ∥ termLambda lambdaInline ∥ termParens
      where
        core = Core.coreTerm ⊣ position ⊗ choice options
        options =
          [Core.variable ⊣ identifer, abstract] ++ case mode of
            Meta -> [Core.ofCourseIntroduction ⊣ token "!" ≫ termCore]
            Runtime ->
              [ Core.extern ⊣ prefixKeyword "extern" ≫ symbol ≪ space ⊗ betweenParens typexx ⊗ betweenParens typexx,
                Core.pack ⊣ prefixKeyword "pack" ≫ betweenParens (Core.bound ⊣ typePattern ⊗ lambdaInline typexx) ⊗ space ≫ termCore,
                Core.unpack ⊣ prefixKeyword "unpack" ≫ termCore,
                Core.pureRegionTransformer ⊣ prefixKeyword "pure" ≫ betweenParens typexx ⊗ space ≫ termCore,
                Core.readReference ⊣ prefixKeyword "read" ≫ termCore,
                Core.castRegionTransformer ⊣ prefixKeyword "cast" ≫ betweenParens typexx ⊗ space ≫ termCore,
                Core.localRegion ⊣ Core.bound ⊣ fixRegion ⊣ localRegion
              ]
        fixRegion = secondI (secondI (secondI bound . associate . firstI swap) . associate . firstI swap) . associate . firstI associate
        localRegion = prefixKeyword "stack" ≫ betweenParens (typePattern ⊗ token ";" ≫ binderRuntimeCore "local") ⊗ binaryToken "->" ≫ typexx ⊗ lambdaMajor termBottom
        abstract = case mode of
          Meta -> Core.macroAbstraction ⊣ Core.bound ⊣ token "\\" ≫ pattern ⊗ lambdaMajor termBottom
          Runtime -> Core.functionLiteral ⊣ Core.bound ⊣ token "\\" ≫ runtimePattern ⊗ lambdaMajor termBottom
    categorize (Core.CoreTerm _ e) = go e
      where
        go (Core.TermCommon (Core.Variable _)) = mode
        go (Core.MacroAbstraction _) = Meta
        go (Core.MacroApplication _ _) = Meta
        go (Core.TypeAbstraction _) = mode
        go (Core.TypeApplication _ _) = mode
        go (Core.KindAbstraction _) = mode
        go (Core.KindApplication _ _) = mode
        go (Core.OfCourseIntroduction _) = Meta
        go (Core.Bind _ _) = Meta
        go (Core.TermCommon (Core.Alias _ _)) = Runtime
        go (Core.TermCommon (Core.FunctionApplication _ _ _ _)) = Runtime
        go (Core.TermCommon (Core.Extern _ _ _ _ _)) = Runtime
        go (Core.TermCommon (Core.FunctionLiteral _ _)) = Runtime
        go (Core.QualifiedAssume _ _) = mode
        go (Core.QualifiedCheck _) = mode
        go (Core.TermCommon (Core.RuntimePairIntroduction _ _ _)) = Runtime
        go (Core.Pack _ _) = Runtime
        go (Core.Unpack _) = Runtime
        go (Core.PureRegionTransformer _ _) = Runtime
        go (Core.DoRegionTransformer _ _) = Runtime
        go (Core.TermCommon (Core.ReadReference _ _)) = Runtime
        go (Core.CastRegionTransformer _ _) = Runtime
        go (Core.TermCommon (Core.LocalRegion _ _)) = Runtime

modulex ::
  (Syntax δ, Position δ p) =>
  δ (Module.Module p)
modulex = Module.coreModule ⊣ orderless ⊣ list ⊣ some (item declare (token ";" ≫ line) lambdaMajor) ⊕ never
  where
    declare = space ≫ identifer ≪ binaryToken "="

item header footer lambda =
  choice
    [ itemCore "module" (Module.modulex ⊣ lambda modulex),
      itemAnnotate "inline" (Module.global . Module.inline) (term Runtime),
      itemCore "import" (Module.global . Module.importx ⊣ position ⊗ path),
      itemAnnotate "function" (Module.global . Module.text) (term Runtime),
      itemCore "type" (Module.global . Module.synonym ⊣ typex Runtime)
    ]
  where
    itemCore brand inner = moduleKeyword brand ≫ header ⊗ inner ≪ footer
    itemAnnotate brand f inner = moduleKeyword brand ≫ (secondP f ⊣ correct ⊣ (annotated ∥ (nothing ⊣ always) ⊗ implicit))
      where
        correct = associate . firstI swap . inverse associate
        implicit = header ⊗ inner ≪ footer
        annotated = space ≫ moduleKeyword "_" ≫ binaryToken "::" ≫ (just ⊣ typex Runtime) ≪ token ";" ≪ line ≪ moduleKeyword brand ⊗ implicit

itemSingleton ::
  (Syntax δ, Position δ p) => δ (Module.Item p)
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
  identifer = Parser $ Identifier <$> Combinators.some (Megaparsec.satisfy legalChar Megaparsec.<?> "letter") <* Megaparsec.space
    where
      legalChar x = isAlphaNum x
  stringLiteral = Parser $ do
    Megaparsec.string "\""
    Combinators.manyTill (Megaparsec.satisfy (const True)) (Megaparsec.string "\"") <* Megaparsec.space
  _ ∥# q = q
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
  Printer p ∥ Printer q = Printer $ \x -> (p x) <|> (q x)
  never = Printer $ const Nothing
  always = Printer $ \() -> Just $ pure ()

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
  pick f (Printer left) (Printer right) = Printer $ \x -> case f x of
    True -> left x
    False -> right x
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
