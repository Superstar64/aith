module Core.Ast.Common where

import qualified Data.Set as Set
import Misc.Identifier
import TypeSystem.Methods
import qualified TypeSystem.Variable as TypeSystem

data Internal = Internal deriving (Show)

avoidCaptureImpl ::
  forall σ u e pm pm' pm''.
  ( FreeVariables σ u,
    Bindings pm'',
    Substitute σ e,
    TypeSystem.EmbedVariable σ,
    ConvertPattern pm' pm'
  ) =>
  (pm -> pm'') ->
  (pm -> pm') ->
  u ->
  (pm, e) ->
  (pm', e)
avoidCaptureImpl project inject ex (pm, e) = (pm', e')
  where
    disallowed = freeVariables @σ ex
    bound = bindings (project pm)
    replace x = substitute (TypeSystem.variable @σ $ fresh disallowed x) x :: e -> e
    replacePattern x = convertPattern (fresh disallowed x) x
    e' = foldr replace e bound
    pm' = foldr replacePattern (inject pm) bound

substituteShadowImpl pm _ x e | x `Set.member` bindings pm = e
substituteShadowImpl _ ux x e = substitute ux x e
