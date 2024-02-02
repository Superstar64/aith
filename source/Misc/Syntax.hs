module Misc.Syntax where

import Data.List.NonEmpty (NonEmpty)
import Misc.Isomorph
import Misc.Prism

-- Invertable Syntax Descriptions
-- https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf

infixr 4 ⊣

infixl 7 ≫

infixl 7 ≪

infixl 5 ⊕

infixl 6 ⊗

infixl 3 ∥

class SyntaxBase δ where
  syntaxmap :: Prism a b -> δ a -> δ b
  (⊗) :: δ a -> δ b -> δ (a, b)
  (∥) :: δ a -> δ a -> δ a
  never :: δ a
  always :: δ () -- effictivly 'pure ()'

(⊣) :: (SyntaxBase δ, ToPrism f) => f a b -> δ a -> δ b
f ⊣ p = syntaxmap (toPrism f) p

(⊕) :: (SyntaxBase δ) => δ a -> δ b -> δ (Either a b)
p ⊕ q = left ⊣ p ∥ right ⊣ q

(≫) :: (SyntaxBase p) => p () -> p a -> p a
p ≫ q = unit ⊣ p ⊗ q

(≪) :: (SyntaxBase p) => p a -> p () -> p a
p ≪ q = unit' ⊣ p ⊗ q

choice :: (Foldable t, SyntaxBase δ) => t (δ a) -> δ a
choice = foldl (∥) never

many :: (SyntaxBase δ) => δ a -> δ [a]
many p = cons ⊣ p ⊗ (many p) ∥ nil ⊣ always

some :: (SyntaxBase δ) => δ a -> δ (NonEmpty a)
some p = nonEmpty ⊣ p ⊗ (many p)

seperatedMany :: (SyntaxBase δ) => δ a -> δ () -> δ [a]
seperatedMany p c = cons ⊣ p ⊗ many (c ≫ p) ∥ nil ⊣ always

seperatedSome :: (SyntaxBase δ) => δ a -> δ () -> δ (NonEmpty a)
seperatedSome p c = nonEmpty ⊣ p ⊗ many (c ≫ p)

between :: (SyntaxBase p) => p () -> p () -> p a -> p a
between a b p = a ≫ p ≪ b
