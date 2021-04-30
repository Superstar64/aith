module Misc.Syntax where

import Control.Applicative (Alternative, empty, (<|>))
import Control.Monad (MonadPlus, liftM2)
import Control.Monad.Trans.State (State, runState)
import Control.Monad.Trans.Writer (WriterT, runWriterT)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (fromJust)
import Data.Void (Void)
import Misc.Isomorph
import Misc.Prism
import Text.Megaparsec (Parsec)
import qualified Text.Megaparsec as Megaparsec

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

(⊕) :: SyntaxBase δ => δ a -> δ b -> δ (Either a b)
p ⊕ q = left ⊣ p ∥ right ⊣ q

(≫) :: SyntaxBase p => p () -> p a -> p a
p ≫ q = unit ⊣ p ⊗ q

(≪) :: SyntaxBase p => p a -> p () -> p a
p ≪ q = unit' ⊣ p ⊗ q

choice :: (Foldable t, SyntaxBase δ) => t (δ a) -> δ a
choice = foldl (∥) never

many :: SyntaxBase δ => δ a -> δ [a]
many p = cons ⊣ p ⊗ (many p) ∥ nil ⊣ always

some :: SyntaxBase δ => δ a -> δ (NonEmpty a)
some p = nonEmpty ⊣ p ⊗ (many p)

seperatedMany :: SyntaxBase δ => δ a -> δ () -> δ [a]
seperatedMany p c = cons ⊣ inverse nonEmpty ⊣ seperatedSome p c ∥ nil ⊣ always

seperatedSome :: SyntaxBase δ => δ a -> δ () -> δ (NonEmpty a)
seperatedSome p c = nonEmpty ⊣ p ⊗ (c ≫ (cons ⊣ inverse nonEmpty ⊣ seperatedSome p c) ∥ nil ⊣ always)

between :: SyntaxBase p => p () -> p () -> p a -> p a
between a b p = a ≫ p ≪ b

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
