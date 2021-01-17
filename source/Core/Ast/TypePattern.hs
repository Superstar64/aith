module Core.Ast.TypePattern where

import Core.Ast.Common
import Core.Ast.Kind
import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier
import TypeSystem.Methods
import qualified TypeSystem.Pattern as TypeSystem
import qualified TypeSystem.PatternVariable as TypeSystem

data TypePatternF κ p = TypePatternVariable Identifier κ deriving (Show)

instance Bifunctor TypePatternF where
  bimap f _ (TypePatternVariable x κ) = TypePatternVariable x (f κ)

data TypePattern κ p = CoreTypePattern p (TypePatternF κ p) deriving (Show)

instance InternalType (TypePattern KindInternal p) KindInternal where
  internalType (CoreTypePattern _ pm) = internalType $ projectTypePattern pm

projectTypePattern :: TypePatternF κ p -> TypeSystem.PatternVariable () KindSort κ
projectTypePattern (TypePatternVariable x κ) = TypeSystem.PatternVariable x κ

instance Bifunctor TypePattern where
  bimap f g (CoreTypePattern p pm) = CoreTypePattern (g p) (bimap f g pm)

instance TypeSystem.EmbedPatternVariable KindInternal (TypePattern KindInternal Internal) where
  patternVariable κ x = CoreTypePattern Internal $ TypePatternVariable κ x

data TypePatternSort = TypePattern

instance TypeSystem.EmbedPattern TypePatternSort where
  pattern = TypePattern

instance ConvertPattern (TypePattern KindInternal Internal) (TypePattern KindInternal Internal) where
  convertPattern ix x (CoreTypePattern Internal pm) = convertPattern ix x (projectTypePattern pm)

instance Reduce (TypePattern KindInternal Internal) where
  reduce (CoreTypePattern Internal pm) = reduceImpl $ projectTypePattern pm

instance Strip (TypePattern KindInternal p) (TypePattern KindInternal Internal) where
  strip = bimap id (const Internal)
