module Core.Ast.TypePattern where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Sort
import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier
import TypeSystem.Methods
import qualified TypeSystem.PatternVariable as TypeSystem

data TypePatternF κ p = TypePatternVariable Identifier κ deriving (Show)

instance Bifunctor TypePatternF where
  bimap f _ (TypePatternVariable x κ) = TypePatternVariable x (f κ)

data TypePattern κ p = CoreTypePattern p (TypePatternF κ p) deriving (Show)

instance InternalType (TypePattern KindInternal p) KindInternal where
  internalType (CoreTypePattern _ pm) = internalType $ projectTypePattern pm

projectTypePattern :: TypePatternF κ p -> TypeSystem.PatternVariable () Sort κ
projectTypePattern (TypePatternVariable x κ) = TypeSystem.PatternVariable x κ

instance Bifunctor TypePattern where
  bimap f g (CoreTypePattern p pm) = CoreTypePattern (g p) (bimap f g pm)

instance TypeSystem.EmbedPatternVariable KindInternal (TypePattern KindInternal Internal) where
  patternVariable κ x = CoreTypePattern Internal $ TypePatternVariable κ x

instance Bindings (TypePattern KindInternal Internal) where
  bindings (CoreTypePattern Internal pm) = bindings $ projectTypePattern pm

instance FreeVariables KindInternal (TypePattern KindInternal Internal) where
  freeVariables (CoreTypePattern Internal pm) = freeVariables @KindInternal $ projectTypePattern pm

instance ModifyVariables KindInternal (TypePattern KindInternal Internal) where
  modifyVariables pm free = freeVariables @KindInternal pm <> free

instance Substitute KindInternal (TypePattern KindInternal Internal) where
  substitute κx x (CoreTypePattern Internal pm) = substituteImpl κx x $ projectTypePattern pm

instance ConvertPattern (TypePattern KindInternal Internal) (TypePattern KindInternal Internal) where
  convertPattern ix x (CoreTypePattern Internal pm) = convertPattern ix x (projectTypePattern pm)

instance Reduce (TypePattern KindInternal Internal) where
  reduce (CoreTypePattern Internal pm) = reduceImpl $ projectTypePattern pm

instance Strip (TypePattern KindInternal p) (TypePattern KindInternal Internal) where
  strip = bimap id (const Internal)