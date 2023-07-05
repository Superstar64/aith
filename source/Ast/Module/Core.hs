module Ast.Module.Core where

import Ast.Common.Variable
import Ast.Module.Algebra
import Ast.Term.Core
import Ast.Type.Core
import Data.Map (Map)
import qualified Data.Map as Map
import Misc.Path (Path)

newtype Global p = Global (GlobalF TypeInfer TypeSchemeInfer (TermSchemeInfer p))

reduceModule ::
  Map TermGlobalIdentifier (TermSchemeInfer p) ->
  [(Path, Global p)] ->
  [(Path, Global p)]
reduceModule _ [] = []
reduceModule globals ((path, item) : nodes) =
  (path, item') : reduceModule globals' nodes
  where
    (item', binding) = case item of
      Global (Inline e) ->
        let e' = reduce $ applyGlobalTerms e
         in (Global $ Inline e', Just e')
      Global (Text e@(TermScheme p _)) ->
        let e' = reduce $ applyGlobalTerms e
         in (Global $ Text e', Just (makeExtern path p $ textType e))
      Global (Synonym σ) ->
        (Global $ Synonym σ, Nothing)
      Global (ForwardNewType κ) ->
        (Global $ ForwardNewType κ, Nothing)
      Global (ForwardText σ) ->
        let p = error "todo use actual position"
         in (Global $ ForwardText σ, Just (makeExtern path p σ))

    globals' = case binding of
      Nothing -> globals
      Just e -> Map.insert (TermGlobalIdentifier path) e globals
    applyGlobalTerms e = foldr applyTermGlobal e (freeVariablesGlobalTerm e)
    applyTermGlobal x e = substituteGlobalTerm (globals Map.! x) x e
