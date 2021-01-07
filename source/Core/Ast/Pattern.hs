module Core.Ast.Pattern where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.Stage
import Core.Ast.Type
import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier
import TypeSystem.Methods
import qualified TypeSystem.Pattern as TypeSystem
import qualified TypeSystem.PatternOfCourse as TypeSystem
import qualified TypeSystem.PatternVariable as TypeSystem

data PatternF σ p
  = PatternVariable Identifier σ
  | PatternOfCourse (Pattern σ p)
  deriving (Show)

instance Bifunctor PatternF where
  bimap f _ (PatternVariable x σ) = PatternVariable x (f σ)
  bimap f g (PatternOfCourse pm) = PatternOfCourse (bimap f g pm)

data Pattern σ p = CorePattern p (PatternF σ p) deriving (Show)

instance Bifunctor Pattern where
  bimap f g (CorePattern p pm) = CorePattern (g p) (bimap f g pm)

type PatternInternal = Pattern Internal

data PatternSort = Pattern

projectPattern ::
  PatternF σ p ->
  Either
    (TypeSystem.PatternVariable Stage KindInternal σ)
    (TypeSystem.PatternOfCourse (Pattern σ p))
projectPattern (PatternVariable x σ) = Left $ TypeSystem.PatternVariable x σ
projectPattern (PatternOfCourse pm) = Right $ TypeSystem.PatternOfCourse pm

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => TypeSystem.EmbedPatternVariable (Type i) (Pattern σ i') where
  patternVariable x σ = CorePattern Internal $ PatternVariable x σ

instance (i ~ Internal, σ ~ TypeInternal) => TypeSystem.EmbedPatternOfCourse (Pattern σ i) where
  patternOfCourse pm = CorePattern Internal $ PatternOfCourse pm

instance TypeSystem.EmbedPattern PatternSort where
  pattern = Pattern

instance (σ ~ TypeInternal, σ' ~ TypeInternal) => InternalType (Pattern σ p) σ' where
  internalType (CorePattern _ pm) = internalType $ projectPattern pm

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => FreeVariables (Pattern σ i) (Type i') where
  freeVariables' (CorePattern Internal pm) = freeVariables @TypeInternal $ projectPattern pm

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => FreeVariables (Pattern σ i) (Multiplicity i') where
  freeVariables' (CorePattern Internal pm) = freeVariables @MultiplicityInternal $ projectPattern pm

instance (i ~ Internal, σ ~ TypeInternal) => RemoveBindings (Pattern σ i) where
  removeBindings (CorePattern Internal pm) = removeBindings $ projectPattern pm

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => Substitute (Type i) (Pattern σ i') where
  substitute σx x (CorePattern Internal pm) = substituteImpl σx x $ projectPattern pm

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => Substitute (Multiplicity i) (Pattern σ i') where
  substitute lx x (CorePattern Internal pm) = substituteImpl lx x $ projectPattern pm

instance (i ~ Internal, σ ~ TypeInternal) => Reduce (Pattern σ i) where
  reduce (CorePattern Internal pm) = reduceImpl $ projectPattern pm
