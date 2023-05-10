module Ast.Module.Convert where

import Ast.Module.Algebra
import qualified Ast.Module.Core as Core
import qualified Ast.Module.Surface as Surface
import Ast.Term.Convert
import qualified Ast.Term.Surface as Surface
import Ast.Type.Convert

sourceGlobal :: Core.Global p -> Surface.Global ()
sourceGlobal (Core.Global (Inline e)) = Surface.Global $ Inline (Surface.TermManual $ sourceTermScheme e)
sourceGlobal (Core.Global (Text e)) = Surface.Global $ Text (Surface.TermManual $ sourceTermScheme e)
sourceGlobal (Core.Global (Synonym σ)) = Surface.Global $ Synonym (sourceType σ)
sourceGlobal (Core.Global (NewType σ)) = Surface.Global $ NewType (sourceType σ)
sourceGlobal (Core.Global (ForwardNewType σ)) = Surface.Global $ ForwardNewType (sourceType σ)
sourceGlobal (Core.Global (ForwardText ς)) = Surface.Global $ ForwardText (sourceTypeScheme ς)
