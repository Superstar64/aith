module Core.Ast.KindPattern where

import Core.Ast.Common
import Core.Ast.Sort
import Misc.Identifier (Identifier)
import Misc.Isomorph
import qualified Misc.Variables as Variables

data KindPatternF p = KindPatternVariable Identifier Sort deriving (Show, Functor)

kindPatternVariable = Isomorph (uncurry KindPatternVariable) $ \(KindPatternVariable x μ) -> (x, μ)

data KindPattern p = CoreKindPattern p (KindPatternF p) deriving (Show, Functor)

coreKindPattern = Isomorph (uncurry CoreKindPattern) $ \(CoreKindPattern p pm) -> (p, pm)

type KindPatternInternal = KindPattern Internal

instance Rename KindPatternInternal where
  rename ux x (CoreKindPattern Internal (KindPatternVariable x' κ)) | x == x' = CoreKindPattern Internal (KindPatternVariable ux κ)
  rename _ _ pm = pm

instance Bindings p (KindPattern p) where
  bindings (CoreKindPattern p (KindPatternVariable x _)) = Variables.singleton x p

instance Reduce KindPatternInternal where
  reduce = id
