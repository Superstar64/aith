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
  core <- Linear <$ builtin "linear" <|> Unrestricted <$ builtin "unrestricted" <|> LinearVariable <$> identfier
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
  l <- linear
  token "@"
  s <- stage
  pure (CoreKind p $ Type l s)

typeVariable = TypeVariable <$> identfier

forallx = do
  token "∀<"
  x <- identfier
  token ":"
  κ <- kind
  token ">"
  σ <- lambda typex
  pure (Forall x κ σ)

forallLinear = do
  token "∀["
  x <- identfier
  token "]"
  σ <- lambda typex
  pure (LinearForall x σ)

macro σ = do
  token "-"
  token "["
  l <- linear
  token "]"
  token ">"
  τ <- typex
  pure (Macro l σ τ)

typex :: Parser (Type SourcePos)
typex = do
  p <- getSourcePos
  core <- between (token "(") (token ")") typex <|> CoreType p <$> typeVariable <|> CoreType p <$> forallx <|> CoreType p <$> forallLinear
  (CoreType p <$> macro core) <|> pure core

variable = Variable <$> identfier

macroAbstraction = do
  token "λ"
  token "["
  l <- linear
  token "]"
  token "("
  x <- identfier
  token ":"
  σ <- typex
  token ")"
  e <- lambda term
  pure (MacroAbstraction x l σ e)

typeAbstraction = do
  token "Λ<"
  x <- identfier
  token ":"
  κ <- kind
  token ">"
  e <- lambda term
  pure (TypeAbstraction x κ e)

linearAbstraction = do
  token "Λ["
  x <- identfier
  token "]"
  e <- lambda term
  pure (LinearAbstraction x e)

data Post = MacroApp (Term SourcePos) | TypeApp (Type SourcePos) | LinearApp (Multiplicity SourcePos)

term :: Parser (Term SourcePos)
term = do
  p <- getSourcePos
  core <- between (token "(") (token ")") term <|> x p <|> λ p <|> λσ p <|> λl p
  postfix <- many $ choice [MacroApp <$> between (token "(") (token ")") term, TypeApp <$> between (token "<") (token ">") typex, LinearApp <$> between (token "[") (token "]") linear]
  pure $ foldl (fix p) core postfix
  where
    fix p e1 (MacroApp e2) = CoreTerm p $ MacroApplication e1 e2
    fix p e (TypeApp σ) = CoreTerm p $ TypeApplication e σ
    fix p e (LinearApp l) = CoreTerm p $ LinearApplication e l
    x p = CoreTerm p <$> variable
    λ p = CoreTerm p <$> macroAbstraction
    λσ p = CoreTerm p <$> typeAbstraction
    λl p = CoreTerm p <$> linearAbstraction
