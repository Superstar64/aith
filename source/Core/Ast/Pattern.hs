module Core.Ast.Pattern where

import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Type
import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier
import TypeSystem.Methods
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

projectPattern ::
  PatternF σ p ->
  Either
    (TypeSystem.PatternVariable KindInternal KindInternal σ)
    (TypeSystem.PatternOfCourse (Pattern σ p))
projectPattern (PatternVariable x σ) = Left $ TypeSystem.PatternVariable x σ
projectPattern (PatternOfCourse pm) = Right $ TypeSystem.PatternOfCourse pm

instance TypeSystem.EmbedPatternVariable TypeInternal (Pattern TypeInternal Internal) where
  patternVariable x σ = CorePattern Internal $ PatternVariable x σ

instance TypeSystem.EmbedPatternOfCourse (Pattern TypeInternal Internal) where
  patternOfCourse pm = CorePattern Internal $ PatternOfCourse pm

instance InternalType (Pattern TypeInternal p) TypeInternal where
  internalType (CorePattern _ pm) = internalType $ projectPattern pm

instance FreeVariables TypeInternal (Pattern TypeInternal Internal) where
  freeVariables (CorePattern Internal pm) = freeVariables @TypeInternal $ projectPattern pm

instance FreeVariables KindInternal (Pattern TypeInternal Internal) where
  freeVariables (CorePattern Internal pm) = freeVariables @KindInternal $ projectPattern pm

instance Bindings (Pattern TypeInternal Internal) where
  bindings (CorePattern Internal pm) = bindings $ projectPattern pm

instance ModifyVariables TypeInternal (Pattern TypeInternal Internal) where
  modifyVariables (CorePattern Internal pm) free = freeVariables @TypeInternal (projectPattern pm) <> free

instance ModifyVariables KindInternal (Pattern TypeInternal Internal) where
  modifyVariables (CorePattern Internal pm) free = freeVariables @KindInternal (projectPattern pm) <> free

instance Substitute TypeInternal (Pattern TypeInternal Internal) where
  substitute σx x (CorePattern Internal pm) = substituteImpl σx x $ projectPattern pm

instance Substitute KindInternal (Pattern TypeInternal Internal) where
  substitute sx x (CorePattern Internal pm) = substituteImpl sx x $ projectPattern pm

instance ConvertPattern (Pattern TypeInternal Internal) (Pattern TypeInternal Internal) where
  convertPattern ix x (CorePattern Internal pm) = convertPattern ix x $ projectPattern pm

instance Reduce (Pattern TypeInternal Internal) where
  reduce (CorePattern Internal pm) = reduceImpl $ projectPattern pm
