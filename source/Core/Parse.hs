module Core.Parse where

import Core.Ast
import Data.Char (isAlphaNum, ord)
import Data.Void (Void)
import Misc.Identifier
import Text.Megaparsec (Parsec, SourcePos, between, choice, getSourcePos, many, satisfy, some, (<?>), (<|>))
import Text.Megaparsec.Char (space, string)

type Parser = Parsec Void String

token :: String -> Parser ()
token op = string op >> space

builtin :: String -> Parser ()
builtin name = string ('%' : name) >> space

isGreek :: Int -> Bool
isGreek x = x >= 0x370 && x <= 0x3ff

legalChar :: Char -> Bool
legalChar x = isAlphaNum x && not (isGreek (ord x))

identfier :: Parser Identifier
identfier = Identifier <$> some (satisfy legalChar <?> "letter") <* space

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
  p <- getSourcePos
  core <- Linear <$ builtin "linear" <|> Unrestricted <$ builtin "unrestricted"
  pure (CoreMultiplicity p core)

stageMacro s = do
  token "->"
  s' <- stage
  pure (StageMacro s s')

stage :: Parser Stage
stage = do
  core <- Runtime <$ builtin "runtime"
  stageMacro core <|> pure core

kind :: Parser (Kind SourcePos)
kind = do
  p <- getSourcePos
  s <- stage
  pure (CoreKind p $ Type s)

typeVariable = TypeVariable <$> identfier

forallx = do
  token "∀<"
  x <- identfier
  token ":"
  κ <- kind
  token ">"
  σ <- lambda typex
  pure (Forall x κ σ)

macro σ = do
  token "->"
  τ <- typex
  pure (Macro σ τ)

ofCourse = do
  token "!"
  OfCourse <$> typeCore

typeCore :: Parser (Type SourcePos)
typeCore = do
  p <- getSourcePos
  between (token "(") (token ")") typex <|> CoreType p <$> typeVariable <|> CoreType p <$> forallx <|> CoreType p <$> ofCourse

typex :: Parser (Type SourcePos)
typex = do
  p <- getSourcePos
  core <- typeCore
  (CoreType p <$> macro core) <|> pure core

variable = Variable <$> identfier

macroAbstraction = do
  token "λ"
  token "("
  x <- identfier
  token ":"
  σ <- typex
  token ")"
  e <- lambda term
  pure (MacroAbstraction x σ e)

typeAbstraction = do
  token "Λ"
  token "<"
  x <- identfier
  token ":"
  κ <- kind
  token ">"
  e <- lambda term
  pure (TypeAbstraction x κ e)

ofCourseIntroduction = do
  token "!"
  e <- term
  pure (OfCourseIntroduction e)

ofCourseElimination = do
  builtin "let"
  token "!"
  x <- identfier
  token "="
  e1 <- term
  token ";"
  e2 <- term
  pure (OfCourseElimination x e1 e2)

data Post = MacroApp (Term SourcePos) | TypeApp (Type SourcePos)

term :: Parser (Term SourcePos)
term = do
  p <- getSourcePos
  core <- between (token "(") (token ")") term <|> x p <|> λ p <|> λσ p <|> bangIntro p <|> bangElim p
  postfix <- many $ choice [MacroApp <$> between (token "(") (token ")") term, TypeApp <$> between (token "<") (token ">") typex]
  pure $ foldl (fix p) core postfix
  where
    fix p e1 (MacroApp e2) = CoreTerm p $ MacroApplication e1 e2
    fix p e (TypeApp σ) = CoreTerm p $ TypeApplication e σ
    x p = CoreTerm p <$> variable
    λ p = CoreTerm p <$> macroAbstraction
    λσ p = CoreTerm p <$> typeAbstraction
    bangIntro p = CoreTerm p <$> ofCourseIntroduction
    bangElim p = CoreTerm p <$> ofCourseElimination
