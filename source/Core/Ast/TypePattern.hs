module Core.Ast.TypePattern where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Sort
import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import TypeSystem.Methods
import qualified TypeSystem.PatternVariable as TypeSystem

data TypePatternF κ p = TypePatternVariable Identifier κ deriving (Show)

typePatternVariable = Isomorph (uncurry TypePatternVariable) $ \(TypePatternVariable x κ) -> (x, κ)

instance Bifunctor TypePatternF where
  bimap f _ (TypePatternVariable x κ) = TypePatternVariable x (f κ)

data TypePattern κ p = CoreTypePattern p (TypePatternF κ p) deriving (Show)

coreTypePattern = Isomorph (uncurry CoreTypePattern) $ \(CoreTypePattern p pm) -> (p, pm)

type TypePatternInternal = TypePattern KindInternal Internal

instance InternalType (TypePattern KindInternal p) KindInternal where
  internalType (CoreTypePattern _ pm) = internalType $ projectTypePattern pm

projectTypePattern :: TypePatternF κ p -> TypeSystem.PatternVariable () Sort κ
projectTypePattern (TypePatternVariable x κ) = TypeSystem.PatternVariable x κ

instance Bifunctor TypePattern where
  bimap f g (CoreTypePattern p pm) = CoreTypePattern (g p) (bimap f g pm)

instance TypeSystem.EmbedPatternVariable KindInternal TypePatternInternal where
  patternVariable κ x = CoreTypePattern Internal $ TypePatternVariable κ x

instance Bindings (TypePattern (Kind p) p) where
  bindings (CoreTypePattern _ pm) = bindings $ projectTypePattern pm

instance Semigroup p => FreeVariables (Kind p) p (TypePattern (Kind p) p) where
  freeVariables (CoreTypePattern p pm) = freeVariablesImpl @(Kind p) p $ projectTypePattern pm

instance Semigroup p => ModifyVariables (Kind p) p (TypePattern (Kind p) p) where
  modifyVariables pm free = freeVariables @(Kind p) pm <> free

instance Substitute KindInternal TypePatternInternal where
  substitute κx x (CoreTypePattern Internal pm) = substituteImpl κx x $ projectTypePattern pm

instance ConvertPattern TypePatternInternal TypePatternInternal where
  convertPattern ix x (CoreTypePattern Internal pm) = convertPattern ix x (projectTypePattern pm)

instance Reduce TypePatternInternal where
  reduce (CoreTypePattern Internal pm) = reduceImpl $ projectTypePattern pm

instance Strip (TypePattern KindInternal p) TypePatternInternal where
  strip = bimap id (const Internal)
