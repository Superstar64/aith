{-# LANGUAGE StandaloneDeriving #-}

module Ast.Module.Surface where

import Ast.Common.Surface
import Ast.Common.Variable
import Ast.Module.Algebra
import Ast.Term.Surface
import Ast.Type.Surface
import Control.Category ((.))
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (for)
import Misc.Path (Path)
import qualified Misc.Path as Path
import Misc.Prism
import Misc.Util (sortTopological)
import Prelude hiding (id, (.))

data Global p = Global (GlobalF (Type p) (TypeScheme p) (TermControl p))

instance Functor Global where
  fmap f (Global (Inline e)) = Global (Inline (fmap f e))
  fmap f (Global (Text e)) = Global (Text (fmap f e))
  fmap f (Global (Synonym e)) = Global (Synonym (fmap f e))
  fmap f (Global (ForwardText e)) = Global (ForwardText (fmap f e))
  fmap f (Global (ForwardNewType e)) = Global (ForwardNewType (fmap f e))

inline = Prism (Global . Inline) $ \case
  Global (Inline e) -> Just e
  _ -> Nothing

text = Prism (Global . Text) $ \case
  Global (Text e) -> Just (e)
  _ -> Nothing

synonym = Prism (Global . Synonym) $ \case
  Global (Synonym σ) -> Just σ
  _ -> Nothing

forwardText = Prism (Global . ForwardText) $ \case
  Global (ForwardText σ) -> Just σ
  _ -> Nothing

forwardNewtype = Prism (Global . ForwardNewType) $ \case
  Global (ForwardNewType σ) -> Just σ
  _ -> Nothing

positionGlobal :: Global p -> p
positionGlobal (Global e) = case e of
  Inline (TermAuto (Term p _)) -> p
  Inline (TermManual (TermScheme p _)) -> p
  Text (TermAuto (Term p _)) -> p
  Text (TermManual (TermScheme p _)) -> p
  Synonym (Type p _) -> p
  ForwardText (TypeScheme p _) -> p
  ForwardNewType (Type p _) -> p

data Origin = Manual | Auto

data ModuleError p
  = IllegalPath p Path
  | Cycle p Path
  | Duplicate p Path
  deriving (Show)

removeInserted :: [(Origin, a, b)] -> [(a, b)]
removeInserted items = do
  (existance, a, b) <- items
  case existance of
    Manual -> [(a, b)]
    Auto -> []

validateDuplicates :: Map Path (NonEmpty (Global p)) -> Either (ModuleError p) ()
validateDuplicates code = Map.traverseWithKey check code >> pure ()
  where
    check _ (_ :| []) = Right ()
    check path (global :| _) = Left (Duplicate (positionGlobal global) path)

order :: Semigroup p => Map Path (NonEmpty (Global p)) -> Either (ModuleError p) [(Origin, Path, Global p)]
order code = sortTopological key quit children globals
  where
    key (_, path, item) = (forward, path)
      where
        forward = case item of
          Global (ForwardNewType _) -> True
          Global (ForwardText _) -> True
          _ -> False
    quit (_, path, item) = Left $ Cycle (positionGlobal item) path
    children (_, path, item) = fmap concat $
      for (Map.toList $ depend path item) $ \(path, p) -> do
        case Map.lookup path code of
          Nothing -> Left $ IllegalPath p path
          Just (Global (Text e) :| [])
            | Just σ <- annotated e ->
              pure [(Auto, path, Global (ForwardText σ))]
          Just (global :| []) -> pure [(Manual, path, global)]
          Just (_ :| _) -> error "unexpected module item"
    globals =
      Map.toList code >>= \(path, items) -> do
        item <- NonEmpty.toList items
        pure (Manual, path, item)

    depend path item = case item of
      Global (Inline e) -> free e
      Global (Text e) -> free e
      Global (Synonym σ) -> free σ
      Global (ForwardNewType σ) -> free σ
      Global (ForwardText ς) -> free ς
      where
        scope = Map.mapKeysMonotonic (Path.combine (Path.directory path))
        free e =
          let (Variables {termLocals, termGlobals, typeLocals, typeGlobals}) = freeVariables e
              termLocals' = scope $ Map.mapKeysMonotonic runTermIdentifier termLocals
              termGlobals' = Map.mapKeysMonotonic runTermGlobalIdentifier termGlobals
              typeLocals' = scope $ Map.mapKeysMonotonic runTypeIdentifier typeLocals
              typeGlobals' = Map.mapKeysMonotonic runTypeGlobalIdentifier typeGlobals
           in foldr (Map.unionWith (<>)) (Map.empty) [termLocals', termGlobals', typeLocals', typeGlobals']
