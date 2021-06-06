module Core.Ast.RuntimePattern where

import Control.Category (id, (.))
import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Type
import Data.Bifunctor (Bifunctor, bimap)
import Data.Functor.Const (Const (..), getConst)
import Data.Functor.Identity (Identity (..), runIdentity)
import Misc.Identifier
import Misc.Isomorph
import Misc.Prism
import qualified Misc.Variables as Variables
import Prelude hiding (id, (.))

data PatternCommon σ pm
  = RuntimePatternVariable Identifier σ
  | RuntimePatternPair pm pm
  deriving (Show)

data RuntimePatternF p' p
  = PatternCommon (PatternCommon (Type p') (RuntimePattern p' p))
  deriving (Show)

traverseRuntimePattern pattern typex = go
  where
    go (PatternCommon (RuntimePatternVariable x σ)) = PatternCommon <$> (pure RuntimePatternVariable <*> pure x <*> typex σ)
    go (PatternCommon (RuntimePatternPair pm pm')) = PatternCommon <$> (pure RuntimePatternPair <*> pattern pm <*> pattern pm')

mapRuntimePattern pattern typex = runIdentity . traverseRuntimePattern (Identity . pattern) (Identity . typex)

foldRuntimePattern pattern typex = getConst . traverseRuntimePattern (Const . pattern) (Const . typex)

patternCommon = Prism PatternCommon $ \case
  (PatternCommon pm) -> Just pm

runtimePatternVariable = (patternCommon .) $
  Prism (uncurry RuntimePatternVariable) $ \case
    (RuntimePatternVariable x σ) -> Just (x, σ)
    _ -> Nothing

runtimePatternPair = (patternCommon .) $
  Prism (uncurry RuntimePatternPair) $ \case
    (RuntimePatternPair pm pm') -> Just (pm, pm')
    _ -> Nothing

data RuntimePattern p' p = CoreRuntimePattern p (RuntimePatternF p' p) deriving (Show)

coreRuntimePattern = Isomorph (uncurry $ CoreRuntimePattern) $ \(CoreRuntimePattern p pm) -> (p, pm)

instance Bifunctor RuntimePatternF where
  bimap f g pm = mapRuntimePattern (bimap f g) (fmap f) pm

instance Bifunctor RuntimePattern where
  bimap f g (CoreRuntimePattern p pm) = CoreRuntimePattern (g p) (bimap f g pm)

instance Semigroup p => Binder p (RuntimePattern p p) where
  bindings (CoreRuntimePattern p (PatternCommon (RuntimePatternVariable x _))) = Variables.singleton x p
  bindings (CoreRuntimePattern _ pm) = foldRuntimePattern bindings mempty pm
  rename ux x (CoreRuntimePattern p (PatternCommon (RuntimePatternVariable x' σ))) | x == x' = CoreRuntimePattern p (PatternCommon (RuntimePatternVariable ux σ))
  rename ux x (CoreRuntimePattern p pm) = CoreRuntimePattern p $ mapRuntimePattern (rename ux x) id pm

instance Algebra u p (Type p) => Algebra u p (RuntimePattern p p) where
  freeVariables (CoreRuntimePattern _ pm) = foldRuntimePattern (freeVariables @u) (freeVariables @u) pm
  convert ix x (CoreRuntimePattern p pm) = CoreRuntimePattern p (mapRuntimePattern (convert @u ix x) (convert @u ix x) pm)
  substitute ux x (CoreRuntimePattern p pm) = CoreRuntimePattern p (mapRuntimePattern (substitute ux x) (substitute ux x) pm)

instance Algebra (Type p) p u => Algebra (Type p) p (Bound (RuntimePattern p p) u) where
  freeVariables (Bound pm e) = freeVariables @(Type p) pm <> freeVariables @(Type p) e
  substitute ux x (Bound pm σ) = Bound (substitute ux x pm) (substitute ux x σ)
  convert = substituteHigher (convert @(Type p)) (convert @(Type p))

instance Algebra (Kind p) p u => Algebra (Kind p) p (Bound (RuntimePattern p p) u) where
  freeVariables (Bound pm e) = freeVariables @(Kind p) pm <> freeVariables @(Kind p) e
  substitute ux x (Bound pm σ) = Bound (substitute ux x pm) (substitute ux x σ)
  convert = substituteHigher (convert @(Kind p)) (convert @(Kind p))

instance Semigroup p => Reduce (RuntimePattern p p) where
  reduce (CoreRuntimePattern p pm) = CoreRuntimePattern p (mapRuntimePattern reduce reduce pm)

instance Location (RuntimePattern p') where
  location (CoreRuntimePattern p _) = p
