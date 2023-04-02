module Ast.Module where

import Ast.Common
import Ast.Term
import Ast.Type hiding (Inline)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (for)
import Misc.Isomorph
import Misc.Path
import Misc.Prism
import Misc.Symbol
import Misc.Util

newtype Module g = CoreModule (Map String (Item g)) deriving (Show, Functor, Foldable, Traversable)

data Item g
  = Module (Module g)
  | Global g
  deriving (Show, Functor, Foldable, Traversable)

data GlobalF τ σ e
  = Inline e
  | Text e
  | Synonym τ
  | NewType σ σ
  deriving (Show)

data ForwardF σ ς
  = ForwardNewtype σ
  | ForwardText ς

data GlobalSource p = GlobalSource (GlobalF (TypeSource p) (TypeSource p) (TermControlSource p))

data DeclareSource p
  = DefinitionSource (GlobalSource p)
  | DeclarationSource (ForwardF (TypeSource p) (TypeSchemeSource p))

data GlobalInfer p = GlobalInfer (GlobalF TypeInfer TypeInfer (TermSchemeInfer p))

data DeclareInfer p
  = DefinitionInfer (GlobalInfer p)
  | DeclarationInfer p (ForwardF TypeInfer TypeSchemeInfer)

data ModuleError p
  = IllegalPath p Path
  | IncompletePath p Path
  | IndexingGlobal p Path
  | Cycle p Path
  deriving (Show)

positionGlobal (GlobalSource (Inline (TermManualSource (TermScheme p _)))) = p
positionGlobal (GlobalSource (Inline (TermAutoSource (Term p _)))) = p
positionGlobal (GlobalSource (Text (TermManualSource (TermScheme p _)))) = p
positionGlobal (GlobalSource (Text (TermAutoSource (Term p _)))) = p
positionGlobal (GlobalSource (Synonym (TypeAst p _))) = p
positionGlobal (GlobalSource (NewType _ (TypeAst p _))) = p

mapGlobalPosition :: (p -> p') -> GlobalSource p -> GlobalSource p'
mapGlobalPosition f (GlobalSource (Inline e)) = GlobalSource (Inline (mapTermPosition f e))
mapGlobalPosition f (GlobalSource (Text e)) = GlobalSource (Text (mapTermPosition f e))
mapGlobalPosition f (GlobalSource (Synonym σ)) = GlobalSource (Synonym (mapTypePosition f σ))
mapGlobalPosition f (GlobalSource (NewType κ σ)) = GlobalSource (NewType (mapTypePosition f κ) (mapTypePosition f σ))

positionDeclaration (DefinitionSource global) = positionGlobal global
positionDeclaration (DeclarationSource (ForwardNewtype (TypeAst p _))) = p
positionDeclaration (DeclarationSource (ForwardText (TypeScheme p _))) = p

coreModule = Isomorph CoreModule $ \(CoreModule code) -> code

modulex = Prism Module $ \case
  (Module code) -> Just code
  _ -> Nothing

global = Prism (Global . GlobalSource) $ \case
  (Global (GlobalSource global)) -> Just global
  _ -> Nothing

inline = Prism (Inline) $ \case
  (Inline e) -> Just (e)
  _ -> Nothing

text = Prism (Text) $ \case
  (Text e) -> Just (e)
  _ -> Nothing

synonym = Prism Synonym $ \case
  Synonym σ -> Just σ
  _ -> Nothing

newtypex = Prism (uncurry NewType) $ \case
  NewType σ τ -> Just (σ, τ)
  _ -> Nothing

mapMaybe :: (g -> Maybe g') -> Module g -> Module g'
mapMaybe f (CoreModule code) = CoreModule $ Map.mapMaybe map code
  where
    map (Global g) = Global <$> f g
    map (Module g) | CoreModule m <- mapMaybe f g, Map.null m = Nothing
    map (Module g) = Just $ Module $ mapMaybe f g

flatten :: Module g -> Map Path g
flatten = Map.fromList . go
  where
    go :: Module g -> [(Path, g)]
    go (CoreModule map) =
      Map.toList map >>= \case
        (name, Global item) -> pure (Path [] name, item)
        (root, Module code) -> do
          (Path path name, item) <- go code
          pure (Path (root : path) name, item)

sourceGlobal :: GlobalInfer p -> GlobalSource ()
sourceGlobal (GlobalInfer (Inline e)) = GlobalSource $ Inline (TermManualSource $ sourceTermScheme e)
sourceGlobal (GlobalInfer (Text e)) = GlobalSource $ Text (TermManualSource $ sourceTermScheme e)
sourceGlobal (GlobalInfer (Synonym σ)) = GlobalSource $ Synonym (sourceType σ)
sourceGlobal (GlobalInfer (NewType σ τ)) = GlobalSource $ NewType (sourceType σ) (sourceType τ)

resolve :: p -> Module (GlobalSource p) -> Path -> Either (ModuleError p) (GlobalSource p)
resolve p (CoreModule code) path = go code path
  where
    go code (Path [] name) = case Map.lookup name code of
      Nothing -> Left $ IllegalPath p path
      Just (Global global) -> pure global
      Just (Module _) -> Left $ IncompletePath p path
    go code (Path (first : remainder) name) = case Map.lookup first code of
      Nothing -> Left $ IllegalPath p path
      Just (Global _) -> Left $ IndexingGlobal p path
      Just (Module (CoreModule code')) -> go code' (Path remainder name)

-- nodes without dependencies are at the start of the list
order :: Semigroup p => Module (GlobalSource p) -> Either (ModuleError p) [(Path, DeclareSource p)]
order code = sortTopological view quit children globals
  where
    globals = Map.toList $ DefinitionSource <$> flatten code
    view (path, DefinitionSource _) = (True, path)
    view (path, DeclarationSource _) = (False, path)
    quit (path, global) = Left $ Cycle (positionDeclaration global) path

    children (path, global) = for (Map.toList $ depend global path) $ \(path, p) -> do
      global <- resolve p code path
      case global of
        GlobalSource (Text e) | Just ς <- annotated e -> pure (path, DeclarationSource (ForwardText ς))
        GlobalSource (NewType σ _) | isType -> pure (path, DeclarationSource (ForwardNewtype σ))
        _ -> pure (path, DefinitionSource global)
      where
        isType = case global of
          DefinitionSource (GlobalSource (Inline _)) -> False
          DefinitionSource (GlobalSource (Text _)) -> False
          _ -> True

    depend :: Semigroup p => DeclareSource p -> Path -> Map Path p
    depend item (Path heading _)
      | (DefinitionSource (GlobalSource (Inline e))) <- item = freeTerm e <> freeType e
      | (DefinitionSource (GlobalSource (Text e))) <- item = freeTerm e <> freeType e
      | (DefinitionSource (GlobalSource (Synonym σ))) <- item = freeType σ
      | (DefinitionSource (GlobalSource (NewType σ τ))) <- item = freeType σ <> freeType τ
      | (DeclarationSource (ForwardNewtype σ)) <- item = freeType σ
      | (DeclarationSource (ForwardText ς)) <- item = freeType ς
      where
        scope = Map.mapKeysMonotonic (Path heading)
        freeTerm e =
          Map.unionWith
            (<>)
            (scope $ extractTerm $ runVariables $ freeVariablesTermSource e)
            (extractGlobalTerm $ runVariables $ freeVariablesGlobalTermSource e)
          where
            extractTerm = Map.mapKeysMonotonic (\(TermIdentifier x) -> x)
            extractGlobalTerm = Map.mapKeysMonotonic (\(TermGlobalIdentifier x) -> x)
        freeType σ =
          Map.unionWith
            (<>)
            (scope $ extractType $ runVariables $ freeVariablesTypeSource σ)
            (extractGlobalType $ runVariables $ freeVariablesGlobalTypeSource σ)
          where
            extractType = Map.mapKeysMonotonic (\(TypeIdentifier x) -> x)
            extractGlobalType = Map.mapKeysMonotonic (\(TypeGlobalIdentifier x) -> x)

unorder :: [(Path, DeclareInfer p)] -> Module (GlobalInfer p)
unorder code =
  unorder' $
    code >>= \case
      (path, DefinitionInfer global) -> [(path, global)]
      _ -> []

unorder' :: [(Path, p)] -> Module p
unorder' [] = CoreModule Map.empty
unorder' (item : remaining) = insert item (unorder' remaining)
  where
    insert (Path [] name, global) (CoreModule code) = CoreModule $ Map.insert name (Global global) code
    insert (Path (first : remainder) name, global) (CoreModule code) = case Map.findWithDefault (Module $ CoreModule Map.empty) first code of
      (Module innerCode) -> CoreModule $ Map.insert first innerCode' code
        where
          innerCode' = Module $ insert (Path remainder name, global) innerCode
      _ -> error "unorder error"

mangle :: Path -> Symbol
mangle (Path path name) = Symbol $ (concat $ map (++ "_") $ extract <$> path) ++ name
  where
    extract x = x

makeExtern ::
  Path ->
  p ->
  TypeSchemeInfer ->
  TermSchemeInfer p
makeExtern path p ς = case ς of
  TypeScheme () (MonoType (TypeAst () (FunctionLiteralType σ π τ))) ->
    ( TermScheme p $
        MonoTerm
          (Term p (TermRuntime $ Extern (mangle path) (Core σ) (Core π) (Core τ)))
    )
  TypeScheme () (TypeForall (Bound (TypePattern () x κ) e)) ->
    TermScheme p (TypeAbstraction (Bound (TypePattern () x κ) $ makeExtern path p e))
  _ -> error "not function literal"

reduceModule ::
  Map TermGlobalIdentifier (TermSchemeInfer p) ->
  [(Path, DeclareInfer p)] ->
  [(Path, DeclareInfer p)]
reduceModule _ [] = []
reduceModule globals ((path, item) : nodes) =
  (path, item') : reduceModule globals' nodes
  where
    (item', binding) = case item of
      DefinitionInfer (GlobalInfer (Inline e)) ->
        let e' = reduce $ applyGlobalTerms e
         in (DefinitionInfer $ GlobalInfer $ Inline e', Just e')
      DefinitionInfer (GlobalInfer (Text e@(TermScheme p _))) ->
        let e' = reduce $ applyGlobalTerms e
         in (DefinitionInfer $ GlobalInfer $ Text e', Just (makeExtern path p $ textType e))
      DefinitionInfer (GlobalInfer (Synonym σ)) ->
        (DefinitionInfer $ GlobalInfer $ Synonym σ, Nothing)
      DefinitionInfer (GlobalInfer (NewType κ σ)) ->
        (DefinitionInfer $ GlobalInfer $ NewType κ σ, Nothing)
      DeclarationInfer p (ForwardNewtype κ) ->
        (DeclarationInfer p $ ForwardNewtype κ, Nothing)
      DeclarationInfer p (ForwardText σ) ->
        (DeclarationInfer p $ ForwardText σ, Just (makeExtern path p σ))

    globals' = case binding of
      Nothing -> globals
      Just e -> Map.insert (TermGlobalIdentifier path) e globals
    applyGlobalTerms e = foldr applyTermGlobal e (freeVariablesGlobalTerm e)
    applyTermGlobal x e = substituteGlobalTerm (globals Map.! x) x e
