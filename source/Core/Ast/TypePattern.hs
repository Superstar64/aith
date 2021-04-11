module Core.Ast.TypePattern where

import Core.Ast.Common
import Core.Ast.Kind
import Data.Bifunctor (Bifunctor, bimap)
import Misc.Identifier (Identifier)
import Misc.Isomorph
import qualified Misc.Variables as Variables

data TypePatternF p' p = TypePatternVariable Identifier (Kind p') deriving (Functor, Show)

typePatternVariable = Isomorph (uncurry TypePatternVariable) $ \(TypePatternVariable x κ) -> (x, κ)

instance Bifunctor TypePatternF where
  bimap f _ (TypePatternVariable x κ) = TypePatternVariable x (fmap f κ)

data TypePattern p' p = CoreTypePattern p (TypePatternF p' p) deriving (Functor, Show)

coreTypePattern = Isomorph (uncurry CoreTypePattern) $ \(CoreTypePattern p pm) -> (p, pm)

type TypePatternInternal = TypePattern Internal Internal

instance Bifunctor TypePattern where
  bimap f g (CoreTypePattern p pm) = CoreTypePattern (g p) (bimap f g pm)

instance Bindings p (TypePattern p p) where
  bindings (CoreTypePattern p (TypePatternVariable x _)) = Variables.singleton x p

instance Rename TypePatternInternal where
  rename ux x (CoreTypePattern p (TypePatternVariable x' κ)) | x == x' = (CoreTypePattern p (TypePatternVariable ux κ))
  rename _ _ pm = pm

instance (Semigroup p, FreeVariables u p (Kind p)) => FreeVariables u p (TypePattern p p') where
  freeVariables (CoreTypePattern _ (TypePatternVariable _ κ)) = freeVariables @u κ

instance Substitute u (Kind Internal) => Substitute u TypePatternInternal where
  substitute ux x (CoreTypePattern Internal (TypePatternVariable x' κ)) = CoreTypePattern Internal $ (TypePatternVariable x' (substitute ux x κ))

instance Reduce TypePatternInternal where
  reduce (CoreTypePattern Internal (TypePatternVariable x κ)) = CoreTypePattern Internal $ (TypePatternVariable x (reduce κ))
