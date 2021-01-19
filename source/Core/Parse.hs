module Core.Parse where

import Control.Applicative (Alternative, (<|>))
import Control.Monad (MonadPlus)
import Control.Monad.Combinators (between, choice, many, some)
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.Pattern
import Core.Ast.Stage
import Core.Ast.Term
import Core.Ast.Type
import Core.Ast.TypePattern
import Data.Char (isAlphaNum, ord)
import Data.Void (Void)
import Misc.Identifier
import Text.Megaparsec (Parsec, SourcePos, getSourcePos, satisfy, (<?>))
import Text.Megaparsec.Char (space, string)

newtype Parser a = Parser (Parsec Void String a) deriving (Functor, Applicative, Monad, Alternative, MonadPlus)

token :: String -> Parser ()
token op = Parser $ string op >> space

keyword :: String -> Parser ()
keyword name = Parser $ string ('%' : name) >> space

isGreek :: Int -> Bool
isGreek x = x >= 0x370 && x <= 0x3ff

legalChar :: Char -> Bool
legalChar x = isAlphaNum x && not (isGreek (ord x))

identfier :: Parser Identifier
identfier = Parser $ Identifier <$> some (satisfy legalChar <?> "letter") <* space

position = Parser $ getSourcePos

betweenParens = between (token "(") (token ")")

lambda :: Parser b -> Parser b
lambda inner = do
  delimit <- False <$ token "=>" <|> True <$ token "{"
  e <- inner
  case delimit of
    True -> token "}"
    False -> pure ()
  pure e

linear :: Parser (Multiplicity SourcePos)
linear = do
  p <- position
  core <- Linear <$ keyword "linear" <|> Unrestricted <$ keyword "unrestricted"
  pure (CoreMultiplicity p core)

stageMacro s = do
  token "~>"
  s' <- stage
  pure (StageMacro s s')

stageCore = do
  p <- position
  betweenParens stage <|> CoreStage p <$> (Runtime <$ keyword "runtime") <|> CoreStage p <$> StageOfCourse <$> (token "!" >> stageCore)

stage :: Parser (Stage SourcePos)
stage = do
  p <- position
  core <- stageCore
  CoreStage p <$> stageMacro core <|> pure core

kindType = do
  keyword "type"
  s <- stage
  pure (Type s)

kindCore = do
  p <- position
  betweenParens kind <|> CoreKind p <$> kindType

higher κ = do
  token "->"
  κ' <- kind
  pure (Higher κ κ')

kind :: Parser (Kind SourcePos)
kind = do
  p <- position
  core <- kindCore
  (CoreKind p <$> higher core) <|> pure core

typeVariable = TypeVariable <$> identfier

forallx = do
  token "∀<"
  pm <- typePattern
  token ">"
  σ <- lambda typex
  pure (Forall pm σ)

macro σ = do
  token "->"
  τ <- typex
  pure (Macro σ τ)

ofCourse = do
  token "!"
  OfCourse <$> typeCore

typeOperator = do
  token "λ"
  pm <- typePattern
  σ <- lambda typex
  pure (TypeOperator pm σ)

typeCore :: Parser (Type SourcePos)
typeCore = do
  p <- position
  core <- betweenParens typex <|> CoreType p <$> typeVariable <|> CoreType p <$> forallx <|> CoreType p <$> ofCourse <|> CoreType p <$> typeOperator
  postfix <- many (betweenParens typex)
  pure $ foldl (\σ τ -> CoreType p $ TypeConstruction σ τ) core postfix

typex :: Parser (Type SourcePos)
typex = do
  p <- position
  core <- typeCore
  (CoreType p <$> macro core) <|> pure core

typePattern :: Parser (TypePattern (Kind SourcePos) SourcePos)
typePattern = do
  p <- position
  x <- identfier
  token ":"
  κ <- kind
  pure (CoreTypePattern p (TypePatternVariable x κ))

variable = Variable <$> identfier

macroAbstraction = do
  token "λ"
  pm <- pattern
  e <- lambda term
  pure (MacroAbstraction pm e)

typeAbstraction = do
  token "Λ"
  token "<"
  pm <- typePattern
  token ">"
  e <- lambda term
  pure (TypeAbstraction pm e)

ofCourseIntroduction = do
  token "!"
  e <- term
  pure (OfCourseIntroduction e)

patternOfCourse = do
  token "!"
  PatternOfCourse <$> patternCore

patternVariable = do
  x <- identfier
  token ":"
  σ <- typex
  pure (PatternVariable x σ)

patternCore = do
  p <- position
  betweenParens pattern <|> CorePattern p <$> patternOfCourse

pattern = do
  p <- position
  CorePattern p <$> patternVariable <|> patternCore

bind = do
  keyword "let"
  pm <- pattern
  token "="
  e1 <- term
  token ";"
  e2 <- term
  pure (Bind pm e1 e2)

data Post = MacroApp (Term SourcePos) | TypeApp (Type SourcePos)

term :: Parser (Term SourcePos)
term = do
  p <- position
  core <- betweenParens term <|> x p <|> λ p <|> λσ p <|> bangIntro p <|> bindImpl p
  postfix <- many $ choice [MacroApp <$> between (token "(") (token ")") term, TypeApp <$> between (token "<") (token ">") typex]
  pure $ foldl (fix p) core postfix
  where
    fix p e1 (MacroApp e2) = CoreTerm p $ MacroApplication e1 e2
    fix p e (TypeApp σ) = CoreTerm p $ TypeApplication e σ
    x p = CoreTerm p <$> variable
    λ p = CoreTerm p <$> macroAbstraction
    λσ p = CoreTerm p <$> typeAbstraction
    bangIntro p = CoreTerm p <$> ofCourseIntroduction
    bindImpl p = CoreTerm p <$> bind
