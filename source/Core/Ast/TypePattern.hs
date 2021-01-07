module Core.Ast.TypePattern where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier
import TypeSystem.Methods
import qualified TypeSystem.Pattern as TypeSystem
import qualified TypeSystem.PatternVariable as TypeSystem

data TypePatternF κ p = TypePatternVariable Identifier κ deriving (Show)

instance Bifunctor TypePatternF where
  bimap f _ (TypePatternVariable x κ) = TypePatternVariable x (f κ)

data TypePattern κ p = CoreTypePattern p (TypePatternF κ p) deriving (Show)

instance (κ ~ KindInternal, κ' ~ KindInternal) => InternalType (TypePattern κ p) κ' where
  internalType (CoreTypePattern _ pm) = internalType $ projectTypePattern pm

projectTypePattern :: TypePatternF κ p -> TypeSystem.PatternVariable () KindSort κ
projectTypePattern (TypePatternVariable x κ) = TypeSystem.PatternVariable x κ

instance Bifunctor TypePattern where
  bimap f g (CoreTypePattern p pm) = CoreTypePattern (g p) (bimap f g pm)

instance (i ~ Internal, i' ~ Internal, κ ~ KindInternal) => TypeSystem.EmbedPatternVariable (Kind i') (TypePattern κ i') where
  patternVariable κ x = CoreTypePattern Internal $ TypePatternVariable κ x

data TypePatternSort = TypePattern

instance TypeSystem.EmbedPattern TypePatternSort where
  pattern = TypePattern

instance (i ~ Internal, i' ~ Internal, κ ~ KindInternal) => FreeVariables (TypePattern κ i) (Multiplicity i') where
  freeVariables' (CoreTypePattern Internal pm) = freeVariables @MultiplicityInternal $ projectTypePattern pm

instance (i ~ Internal, κ ~ KindInternal) => RemoveBindings (TypePattern κ i) where
  removeBindings (CoreTypePattern Internal pm) = removeBindings $ projectTypePattern pm

instance (i ~ Internal, i' ~ Internal, κ ~ KindInternal) => Substitute (Multiplicity i) (TypePattern κ i') where
  substitute lx x (CoreTypePattern Internal pm) = substituteImpl lx x $ projectTypePattern pm

instance (i ~ Internal, κ ~ KindInternal) => Reduce (TypePattern κ i) where
  reduce (CoreTypePattern Internal pm) = reduceImpl $ projectTypePattern pm

instance (κ ~ KindInternal, κ' ~ KindInternal, i ~ Internal) => Strip (TypePattern κ p) (TypePattern κ' i) where
  strip = bimap id (const Internal)
