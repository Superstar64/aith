module Core.Ast.KindPattern where

import Core.Ast.Common
import Core.Ast.Sort
import Misc.Identifier (Identifier)
import Misc.Isomorph
import TypeSystem.Methods
import qualified TypeSystem.PatternVariable as TypeSystem

data KindPatternF p = KindPatternVariable Identifier Sort deriving (Show, Functor)

kindPatternVariable = Isomorph (uncurry KindPatternVariable) $ \(KindPatternVariable x μ) -> (x, μ)

data KindPattern p = CoreKindPattern p (KindPatternF p) deriving (Show, Functor)

coreKindPattern = Isomorph (uncurry CoreKindPattern) $ \(CoreKindPattern p pm) -> (p, pm)

type KindPatternInternal = KindPattern Internal

projectKindPattern :: KindPatternF p -> TypeSystem.PatternVariable () () Sort
projectKindPattern (KindPatternVariable x μ) = TypeSystem.PatternVariable x μ

instance Bindings KindPatternInternal where
  bindings (CoreKindPattern Internal pm) = bindings $ projectKindPattern pm

instance TypeSystem.EmbedPatternVariable Sort KindPatternInternal where
  patternVariable x μ = CoreKindPattern Internal $ KindPatternVariable x μ

instance InternalType (KindPattern Internal) Sort where
  internalType (CoreKindPattern Internal pm) = internalType $ projectKindPattern pm

instance ConvertPattern KindPatternInternal KindPatternInternal where
  convertPattern ix x (CoreKindPattern Internal pm) = convertPattern ix x $ projectKindPattern pm

instance Reduce KindPatternInternal where
  reduce = id

instance Strip (KindPattern p) KindPatternInternal where
  strip pm = Internal <$ pm
