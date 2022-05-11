module Module where

import Ast.Common
import Ast.Kind
import Ast.Term
import Ast.Type hiding (Inline)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (for)
import Misc.Isomorph
import Misc.Path
import Misc.Prism
import Misc.Symbol
import Misc.Util
import TypeCheck
import TypeCheck.Core

newtype Module g = CoreModule (Map String (Item g)) deriving (Show, Functor, Foldable, Traversable)

data Item g
  = Module (Module g)
  | Global g
  deriving (Show, Functor, Foldable, Traversable)

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

data GlobalF ς p e
  = Inline ς e
  | Import p Path
  | Text ς e
  deriving (Show)

data GlobalSource p = GlobalSource (GlobalF (TypeSchemeAuto p) p (TermSchemeSource p))

instance Location GlobalSource where
  location (GlobalSource (Inline _ (TermSchemeSource p _))) = p
  location (GlobalSource (Import p _)) = p
  location (GlobalSource (Text _ (TermSchemeSource p _))) = p

instance Functor GlobalSource where
  fmap f (GlobalSource (Inline ς e)) = GlobalSource $ Inline (fmap (fmap f) ς) (fmap f e)
  fmap f (GlobalSource (Import p path)) = GlobalSource $ Import (f p) path
  fmap f (GlobalSource (Text ς e)) = GlobalSource $ Text (fmap (fmap f) ς) (fmap f e)

data GlobalInfer p = GlobalInfer (GlobalF TypeSchemeInfer p (TermSchemeInfer p))

coreModule = Isomorph CoreModule $ \(CoreModule code) -> code

modulex = Prism Module $ \case
  (Module code) -> Just code
  _ -> Nothing

global = Prism (Global . GlobalSource) $ \case
  (Global (GlobalSource global)) -> Just global
  _ -> Nothing

inline = Prism (uncurry Inline) $ \case
  (Inline σ e) -> Just (σ, e)
  _ -> Nothing

importx = Prism (uncurry Import) $ \case
  (Import p path) -> Just (p, path)
  _ -> Nothing

text = Prism (uncurry Text) $ \case
  (Text σ e) -> Just (σ, e)
  _ -> Nothing

data ModuleError p
  = IllegalPath p Path
  | IncompletePath p Path
  | IndexingGlobal p Path
  | Cycle p Path
  deriving (Show)

-- nodes without dependencies are at the start of the list
order :: Semigroup p => Module (GlobalSource p) -> Either (ModuleError p) [(Path, GlobalSource p)]
order code = sortTopological view quit children globals
  where
    globals = items [] code
    view (path, _) = path
    quit (path, global) = Left $ Cycle (location global) path
    children (path, global) = fmap concat $ for (Map.toList $ depend global path) $ \(path, p) -> do
      global <- resolve p code path
      case global of
        GlobalSource (Text (Just _) _) -> pure []
        _ -> pure [(path, global)]

    extractTerm (TermIdentifier x) = x

    depend :: Semigroup p => GlobalSource p -> Path -> Map Path p
    depend (GlobalSource (Inline _ e)) (Path location _) = Map.mapKeysMonotonic (Path location) (freeTerm)
      where
        freeTerm = Map.mapKeysMonotonic extractTerm $ runVariables $ freeVariablesTermSource e
    depend (GlobalSource (Text _ e)) (Path location _) = Map.mapKeysMonotonic (Path location) (freeTerm)
      where
        freeTerm = Map.mapKeysMonotonic extractTerm $ runVariables $ freeVariablesTermSource e
    depend (GlobalSource (Import p path)) _ = Map.singleton path p

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

    items :: [String] -> Module (GlobalSource p) -> [(Path, GlobalSource p)]
    items heading (CoreModule code) = do
      (name, item) <- Map.toList code
      case item of
        Module inner -> items (heading ++ [name]) inner
        Global global -> pure $ (Path heading name, global)

unorder :: [(Path, p)] -> Module p
unorder [] = CoreModule Map.empty
unorder (item : remaining) = insert item (unorder remaining)
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

prepareContext = curryMap . monotonic (inverse path) . flatten

forwardDeclarations :: Module (GlobalSource p) -> Module (TypeSchemeSource p)
forwardDeclarations = mapMaybe forward
  where
    forward (GlobalSource (Text (Just σ) _)) = Just σ
    forward _ = Nothing

validateDeclarations :: Module (TypeSchemeSource p) -> Either (TypeError p) (Module (p, TypeSchemeInfer))
validateDeclarations = traverse $ \ς@(TypeSchemeSource p _) -> do
  ς <- runCore (do (ς, _) <- kindCheckScheme ς; finish ς) emptyEnvironment emptyState
  pure (p, ς)

forwardDeclare :: Module (p, TypeSchemeInfer) -> Map [String] (CoreEnvironment p)
forwardDeclare = fmap basic . prepareContext
  where
    basic declerations =
      emptyEnvironment
        { typeEnvironment = types $ identifers declerations }
      where
        identifers = Map.mapKeysMonotonic TermIdentifier
        types = fmap (\(p, ς) -> (p, Unrestricted, convertFunctionLiteral $ flexibleType $ flexibleKind ς))

convertFunctionLiteral ς = case ς of
  TypeSchemeCore (MonoType (TypeCore (FunctionLiteralType σ π τ))) -> polyEffect "R" (TypeCore $ FunctionPointer σ π τ)
  TypeSchemeCore (ImplicitForall (Bound pm ς) c π) -> TypeSchemeCore $ ImplicitForall (Bound pm $ convertFunctionLiteral ς) c π
  _ -> error "not function literal"

forwardDefine :: Module (p, TypeSchemeInfer) -> Map [String] (Map TermIdentifier (TermSchemeInfer p, TypeSchemeInfer))
forwardDefine =
  Map.mapWithKey (\heading -> identifers . Map.mapWithKey (make heading)) . prepareContext
  where
    identifers = Map.mapKeysMonotonic TermIdentifier 
    make heading name (p, ς) = (makeExtern path p ς, ς)
      where
        path = Path heading name

makeExtern ::
  Path ->
  p ->
  TypeSchemeInfer ->
  TermSchemeInfer p
makeExtern path p ς = case ς of
  TypeSchemeCore (MonoType (TypeCore (FunctionLiteralType σ π τ))) ->
    TermSchemeCore p $
      ImplicitTypeAbstraction
        ( Bound (TypePatternCore (TypeIdentifier "R") $ KindCore Region) (TermSchemeCore p $ MonoTerm $ TermCore p (TermRuntime $ Extern (mangle path) σ π τ))
        )
        Set.empty
        []
  TypeSchemeCore (ImplicitForall (Bound (TypePatternCore x κ) e) c π) ->
    TermSchemeCore p (ImplicitTypeAbstraction (Bound (TypePatternCore x κ) $ makeExtern path p e) c π)
  _ -> error "not function literal"

typeCheckModule ::
  Map [String] (CoreEnvironment p) ->
  [(Path, GlobalSource p)] ->
  Either (TypeError p) [(Path, GlobalInfer p)]
typeCheckModule _ [] = pure []
typeCheckModule environments ((path@(Path heading name), item) : nodes) = do
  let environment = Map.findWithDefault emptyEnvironment heading environments
  (item', σ) <- case item of
    GlobalSource (Inline Nothing (TermSchemeSource _ (MonoTerm e))) -> do
      (e, σ) <- runCore (typeCheckGlobalAuto True e) environment emptyState
      pure (GlobalInfer $ Inline σ e, flexibleType $ flexibleKind σ)
    GlobalSource (Inline σ e) -> do
      (e, σ) <- runCore (typeCheckGlobalManual e σ) environment emptyState
      pure (GlobalInfer $ Inline σ e, flexibleType $ flexibleKind σ)
    GlobalSource (Text Nothing (TermSchemeSource _ (MonoTerm e))) -> do
      (e, σ) <- runCore (typeCheckGlobalAuto False e >>= syntaticCheck) environment emptyState
      pure (GlobalInfer $ Text σ e, convertFunctionLiteral $ flexibleType $ flexibleKind σ)
    GlobalSource (Text σ e) -> do
      (e, σ) <- runCore (typeCheckGlobalManual e σ >>= syntaticCheck) environment emptyState
      pure (GlobalInfer $ Text σ e, convertFunctionLiteral $ flexibleType $ flexibleKind σ)
    GlobalSource (Import p sym@(Path heading name)) -> do
      let environment = Map.findWithDefault emptyEnvironment heading environments
      let (_, _, σ) = typeEnvironment environment Map.! (TermIdentifier name)
      pure (GlobalInfer $ Import p sym, σ)
  let augmented =
        environment
          { typeEnvironment = Map.insert (TermIdentifier name) (location item, Unrestricted, σ) $ typeEnvironment environment
          }
  let environment' = Map.insert heading augmented environments
  ((path, item') :) <$> typeCheckModule environment' nodes

reduceModule ::
  Map [String] (Map TermIdentifier (TermSchemeInfer p, TypeSchemeInfer)) ->
  [(Path, GlobalInfer p)] ->
  [(Path, GlobalInfer p)]
reduceModule _ [] = []
reduceModule globals ((path@(Path heading name), item) : nodes) =
  (path, item') : reduceModule globals' nodes
  where
    scope = Map.findWithDefault Map.empty heading globals
    reduceGlobal e = reduce $ foldr (\(x, (ex, _)) -> substituteTerm ex x) e $ Map.toList $ scope
    (item', (σ', e')) = case item of
      GlobalInfer (Inline σ e) ->
        let e' = reduceGlobal e
         in (GlobalInfer (Inline σ e'), (σ, e'))
      GlobalInfer (Text σ e@(TermSchemeCore p _)) ->
        let e' = reduceGlobal e
         in (GlobalInfer (Text σ e'), (convertFunctionLiteral σ, makeExtern path p σ))
      GlobalInfer (Import _ (Path heading name)) ->
        let (e', σ) = globals Map.! heading Map.! (TermIdentifier name)
         in (GlobalInfer (Inline σ e'), (σ, e'))
    globals' = Map.insert heading (Map.insert (TermIdentifier name) (e', σ') scope) globals
