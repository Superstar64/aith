module Ast.Type.Convert where

import Ast.Common.Variable
import Ast.Type.Algebra hiding (Type)
import qualified Ast.Type.Core as Core
import qualified Ast.Type.Surface as Surface
import Data.Void (absurd)

nameType :: Core.TypeUnify -> Surface.Type ()
nameType = sourceType . Core.substituteLogical name
  where
    name (TypeLogicalRaw i) = Core.Type $ TypeConstant $ TypeVariable $ TypeIdentifier $ show i

sourceType :: Core.TypeInfer -> Surface.Type ()
sourceType (Core.Type σ) = Surface.Type () $ mapTypeF (\v -> absurd v) absurd sourceTypeScheme sourceType σ

sourceTypeScheme :: Core.TypeSchemeInfer -> Surface.TypeScheme ()
sourceTypeScheme (Core.MonoType σ) = Surface.TypeScheme () $ Surface.MonoType (sourceType σ)
sourceTypeScheme (Core.TypeForall pm σ) =
  Surface.TypeScheme () $ Surface.TypeForall (sourceTypePattern pm) (sourceTypeScheme σ)

sourceTypePattern :: Core.TypePatternInfer -> Surface.TypePattern ()
sourceTypePattern (Core.TypePattern x π σ) = Surface.TypePattern () x π (sourceType σ)

sourceInstanciation :: Core.InstantiationInfer -> Surface.Instantiation ()
sourceInstanciation θ = Surface.Instantiation (map sourceType $ go θ)
  where
    go Core.InstantiateEmpty = []
    go (Core.InstantiateType σ θ) = σ : go θ
