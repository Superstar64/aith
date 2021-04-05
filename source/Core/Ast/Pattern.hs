module Core.Ast.Pattern where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Type
import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import Misc.Prism
import TypeSystem.Methods
import qualified TypeSystem.PatternOfCourse as TypeSystem
import qualified TypeSystem.PatternVariable as TypeSystem

data PatternF σ p
  = PatternVariable Identifier σ
  | PatternOfCourse (Pattern σ p)
  deriving (Show)

patternVariable = Prism (uncurry PatternVariable) $ \case
  (PatternVariable x σ) -> Just (x, σ)
  _ -> Nothing

patternOfCourse = Prism PatternOfCourse $ \case
  (PatternOfCourse pm) -> Just pm
  _ -> Nothing

instance Bifunctor PatternF where
  bimap f _ (PatternVariable x σ) = PatternVariable x (f σ)
  bimap f g (PatternOfCourse pm) = PatternOfCourse (bimap f g pm)

data Pattern σ p = CorePattern p (PatternF σ p) deriving (Show)

corePattern = Isomorph (uncurry CorePattern) $ \(CorePattern p pm) -> (p, pm)

instance Bifunctor Pattern where
  bimap f g (CorePattern p pm) = CorePattern (g p) (bimap f g pm)

type PatternInternal = Pattern TypeInternal Internal

projectPattern ::
  PatternF σ p ->
  Either
    (TypeSystem.PatternVariable KindInternal KindInternal σ)
    (TypeSystem.PatternOfCourse (Pattern σ p))
projectPattern (PatternVariable x σ) = Left $ TypeSystem.PatternVariable x σ
projectPattern (PatternOfCourse pm) = Right $ TypeSystem.PatternOfCourse pm

instance TypeSystem.EmbedPatternVariable TypeInternal PatternInternal where
  patternVariable x σ = CorePattern Internal $ PatternVariable x σ

instance TypeSystem.EmbedPatternOfCourse PatternInternal where
  patternOfCourse pm = CorePattern Internal $ PatternOfCourse pm

instance InternalType (Pattern TypeInternal p) TypeInternal where
  internalType (CorePattern _ pm) = internalType $ projectPattern pm

instance Semigroup p => FreeVariables (Type p) p (Pattern (Type p) p) where
  freeVariables (CorePattern p pm) = freeVariablesImpl @(Type p) p $ projectPattern pm

instance Semigroup p => FreeVariables (Kind p) p (Pattern (Type p) p) where
  freeVariables (CorePattern p pm) = freeVariablesImpl @(Kind p) p $ projectPattern pm

instance Bindings (Pattern (Type p) p) where
  bindings (CorePattern _ pm) = bindings $ projectPattern pm

instance Semigroup p => ModifyVariables (Type p) p (Pattern (Type p) p) where
  modifyVariables (CorePattern p pm) free = freeVariablesImpl @(Type p) p (projectPattern pm) <> free

instance Semigroup p => ModifyVariables (Kind p) p (Pattern (Type p) p) where
  modifyVariables (CorePattern p pm) free = freeVariablesImpl @(Kind p) p (projectPattern pm) <> free

instance Substitute TypeInternal PatternInternal where
  substitute σx x (CorePattern Internal pm) = substituteImpl σx x $ projectPattern pm

instance Substitute KindInternal PatternInternal where
  substitute sx x (CorePattern Internal pm) = substituteImpl sx x $ projectPattern pm

instance ConvertPattern PatternInternal PatternInternal where
  convertPattern ix x (CorePattern Internal pm) = convertPattern ix x $ projectPattern pm

instance Reduce PatternInternal where
  reduce (CorePattern Internal pm) = reduceImpl $ projectPattern pm
