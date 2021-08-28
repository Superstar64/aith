module Module where

import Control.Monad.State (StateT, evalStateT, execStateT, get, modify)
import Control.Monad.Trans (lift)
import Data.Bifunctor (second)
import Data.Functor.Identity
import Data.List (find)
import Data.Traversable (for)
import Data.Void
import Language.Ast.Common
import Language.Ast.Kind (mapKind)
import Language.Ast.Multiplicity
import Language.Ast.Term
import Language.Ast.Type
import Language.TypeCheck
import Language.TypeCheck.Core
import Misc.Isomorph
import Misc.MonoidMap (Map, (!))
import qualified Misc.MonoidMap as Map
import Misc.Path
import Misc.Prism
import Misc.Symbol

data ModuleError p
  = IllegalPath p Path
  | IncompletePath p Path
  | IndexingGlobal p Path
  | Cycle p Path
  deriving (Show)

class (TypeErrorQuit p m, Semigroup p) => ModuleErrorQuit p m where
  moduleQuit :: ModuleError p -> m a

instance ModuleErrorQuit Internal Identity where
  moduleQuit e = error $ "internal module error:" ++ show e

instance ModuleErrorQuit p m => ModuleErrorQuit p (StateT s m) where
  moduleQuit = lift . moduleQuit

newtype Module ς θ σ p = CoreModule (Map String (Item ς θ σ p)) deriving (Show)

type ModuleAuto p = Module (TypeSchemeAuto p) () (TypeAuto p) p

mapModuleAuto :: (p -> p') -> ModuleAuto p -> ModuleAuto p'
mapModuleAuto f (CoreModule m) = CoreModule $ fmap (mapItemAuto f) m

coreModule = Isomorph CoreModule $ \(CoreModule code) -> code

data Item ς θ σ p
  = Module (Module ς θ σ p)
  | Global (Global ς θ σ p)
  deriving (Show)

mapItemAuto :: (p -> p') -> ItemAuto p -> ItemAuto p'
mapItemAuto f (Module m) = Module $ mapModuleAuto f m
mapItemAuto f (Global g) = Global $ mapGlobal (fmap $ mapTypeScheme (fmap $ mapKind absurd f) absurd f f) id (fmap $ mapType (fmap $ mapKind absurd f) absurd f) f g

type ItemAuto p = Item (TypeSchemeAuto p) () (TypeAuto p) p

modulex = Prism Module $ \case
  (Module code) -> Just code
  _ -> Nothing

global = Prism Global $ \case
  (Global global) -> Just global
  _ -> Nothing

data Global ς θ σ p
  = Inline ς (Term θ σ p)
  | Import p Path
  | Text ς (Term θ σ p)
  deriving (Show)

type GlobalAuto p = Global (TypeSchemeAuto p) () (TypeAuto p) p

mapGlobal ::
  (ς -> ς') ->
  (θ -> θ') ->
  (σ -> σ') ->
  (p -> p') ->
  Global ς θ σ p ->
  Global ς' θ' σ' p'
mapGlobal f g h i global = case global of
  Inline ς e -> Inline (f ς) (mapTerm g h i e)
  Text ς e -> Text (f ς) (mapTerm g h i e)
  Import p path -> Import (i p) path

inline = Prism (uncurry Inline) $ \case
  (Inline σ e) -> Just (σ, e)
  _ -> Nothing

importx = Prism (uncurry Import) $ \case
  (Import p path) -> Just (p, path)
  _ -> Nothing

text = Prism (uncurry Text) $ \case
  (Text σ e) -> Just (σ, e)
  _ -> Nothing

resolve :: ModuleErrorQuit p m => p -> ModuleAuto p -> Path -> m (GlobalAuto p)
resolve p (CoreModule code) path = go code path
  where
    go code (Path [] name) = case Map.lookup name code of
      Nothing -> moduleQuit $ IllegalPath p path
      Just (Global global) -> pure global
      Just (Module _) -> moduleQuit $ IncompletePath p path
    go code (Path (first : remainder) name) = case Map.lookup first code of
      Nothing -> moduleQuit $ IllegalPath p path
      Just (Global _) -> moduleQuit $ IndexingGlobal p path
      Just (Module (CoreModule code')) -> go code' (Path remainder name)

extractTerm (TermIdentifier x) = x

extractType (TypeIdentifier x) = x

depend :: forall p. Semigroup p => GlobalAuto p -> Path -> Map Path p
depend (Inline σ e) (Path location _) = Map.mapKeysMonotonic (Path location) (annotation <> freeTerm)
  where
    annotation = Map.mapKeysMonotonic extractType $ case σ of
      Nothing -> mempty
      Just σ -> freeVariables @TypeIdentifier σ
    freeTerm = Map.mapKeysMonotonic extractTerm $ freeVariables @TermIdentifier e
depend (Text σ e) (Path location _) = Map.mapKeysMonotonic (Path location) (annotation <> freeTerm)
  where
    annotation = Map.mapKeysMonotonic extractType $ case σ of
      Nothing -> mempty
      Just σ -> freeVariables @TypeIdentifier σ
    freeTerm = Map.mapKeysMonotonic extractTerm $ freeVariables @TermIdentifier e
depend (Import p path) _ = Map.singleton path p

-- nodes without dependencies are at the end of the list
data ModuleOrder ς θ σ p = Ordering [(Path, Global ς θ σ p)] deriving (Show)

type ModuleOrderAuto p = ModuleOrder (TypeSchemeAuto p) () (TypeAuto p) p

instance
  ( UnInfer σ (TypeAuto Internal),
    UnInfer ς (TypeSchemeAuto Internal)
  ) =>
  UnInfer (ModuleOrder ς θ σ p) (ModuleOrderAuto Internal)
  where
  unInfer = mapOrder unInfer (const ()) unInfer (const Internal)

mapOrder ::
  (ς -> ς') ->
  (θ -> θ') ->
  (σ -> σ') ->
  (p -> p') ->
  ModuleOrder ς θ σ p ->
  ModuleOrder ς' θ' σ' p'
mapOrder f g h i (Ordering nodes) = Ordering $ map (second (mapGlobal f g h i)) nodes

items :: [String] -> ModuleAuto p -> [(Path, GlobalAuto p)]
items heading (CoreModule code) = do
  (name, item) <- Map.toList code
  case item of
    Module inner -> items (heading ++ [name]) inner
    Global global -> pure $ (Path heading name, global)

data Mark = Unmarked | Temporary | Permanent deriving (Eq)

-- https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search

visit ::
  ModuleErrorQuit p m =>
  ModuleAuto p ->
  (Maybe p, Path, GlobalAuto p) ->
  StateT (Map Path Mark) (StateT [(Path, GlobalAuto p)] m) ()
visit code (p, path, global) = do
  marks <- get
  case marks ! path of
    Permanent -> pure ()
    Temporary -> case p of
      Just p -> moduleQuit $ Cycle p path
      Nothing -> error "temporary mark on top level"
    Unmarked -> do
      modify $ Map.insert path Temporary
      let dependencies = depend global path
      children <- for (Map.toList dependencies) $ \(path, p) -> do
        global <- resolve p code path
        pure (Just p, path, global)
      for children (visit code)
      modify $ Map.insert path Permanent
      lift $ modify $ ((path, global) :)

order code = Ordering <$> execStateT (evalStateT go (const Unmarked <$> globals)) []
  where
    globals = Map.fromList $ (\(path, global) -> (path, global)) <$> items [] code
    go = do
      this <- get
      let item = find (\(_, mark) -> mark /= Permanent) (Map.toList this)
      case item of
        Nothing -> pure ()
        Just (path, _) -> do
          let global = globals ! path
          visit code (mempty, path, global)
          go

unorder (Ordering []) = CoreModule Map.empty
unorder (Ordering (item : remaining)) = insert item (unorder $ Ordering remaining)
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

searchUnsafe ::
  ModuleOrder TypeSchemeInfer InstantiationInfer TypeInfer p ->
  Path ->
  Global TypeSchemeInfer InstantiationInfer TypeInfer p
searchUnsafe (Ordering []) _ = error "bad search"
searchUnsafe (Ordering ((path, e) : _)) path' | path == path' = e
searchUnsafe (Ordering (_ : items)) path' = searchUnsafe (Ordering items) path'

typeCheckModule :: ModuleErrorQuit p m => ModuleOrderAuto p -> m (ModuleOrder TypeSchemeInfer InstantiationInfer TypeInfer p)
typeCheckModule (Ordering []) = pure $ Ordering []
typeCheckModule (Ordering ((path@(Path heading _), item) : nodes)) = do
  Ordering nodes' <- typeCheckModule $ Ordering nodes
  let env = foldr (inject $ searchUnsafe $ Ordering nodes') emptyEnvironment nodes'
  case item of
    Inline Nothing e -> do
      ((e, σ), _) <- runCore (generalize e) env emptyState
      pure $ Ordering ((path, Inline σ e) : nodes')
    Inline (Just σ) e -> do
      ((e, σ), _) <- runCore (generalizeAnnotate e σ) env emptyState
      pure $ Ordering ((path, Inline σ e) : nodes')
    Text Nothing e -> do
      ((e, σ), _) <- runCore (generalizeText e) env emptyState
      pure $ Ordering ((path, Text σ e) : nodes')
    Text (Just σ) e -> do
      ((e, σ), _) <- runCore (generalizeAnnotateText e σ) env emptyState
      pure $ Ordering ((path, Text σ e) : nodes')
    Import p sym -> pure $ Ordering ((path, Import p sym) : nodes')
  where
    inject ::
      (Path -> Global TypeSchemeInfer InstantiationInfer TypeInfer p) ->
      (Path, Global TypeSchemeInfer InstantiationInfer TypeInfer p) ->
      CoreEnvironment p ->
      CoreEnvironment p
    inject _ (Path heading' name, Inline σ (CoreTerm p _)) env
      | heading == heading' =
        env {typeEnvironment = Map.insert (TermIdentifier name) (p, Unrestricted, mapTypeScheme (mapKind absurd id) absurd id id σ) $ typeEnvironment env}
    inject _ (_, Inline _ _) e = e
    inject _ (Path heading' name, Text σ (CoreTerm p _)) env
      | heading == heading' =
        env {typeEnvironment = Map.insert (TermIdentifier name) (p, Unrestricted, mapTypeScheme (mapKind absurd id) absurd id id σ) $ typeEnvironment env}
    inject _ (_, Text _ _) e = e
    inject search (path@(Path heading' _), Import _ path') e
      | heading == heading' = inject search (path, search path') e
    inject _ (_, Import _ _) e = e

makeExtern ::
  Path ->
  p ->
  TypeSchemeInfer ->
  Term InstantiationInfer TypeInfer p
makeExtern path p (CoreTypeScheme _ (MonoType σ)) = go σ
  where
    go (CoreType _ (FunctionPointer σ τ)) = CoreTerm p (TermRuntime $ Extern (mangle path) σ τ)
    go (CoreType _ (Implied σ τ)) = CoreTerm p (ImplicationAbstraction (Bound (CoreTermPattern p (PatternCommon $ PatternVariable (TermIdentifier $ "x") σ)) $ go τ))
    go _ = error "extern of non function pointer"
makeExtern _ _ (CoreTypeScheme _ (KindForall _)) = error "extern of kind forall"
makeExtern path p (CoreTypeScheme _ (Forall (Bound _ σ))) = makeExtern path p σ

reduceModule ::
  ModuleOrder TypeSchemeInfer InstantiationInfer TypeInfer p ->
  ModuleOrder TypeSchemeInfer InstantiationInfer TypeInfer p
reduceModule (Ordering []) = Ordering []
reduceModule (Ordering ((path@(Path heading _), item) : nodes)) = case item of
  Inline σ e ->
    let e' = reduce $ foldr inject e nodes'
     in Ordering ((path, Inline σ e') : nodes')
  Text σ e ->
    let e' = reduce $ foldr inject e nodes'
     in Ordering ((path, Text σ e') : nodes')
  Import _ path' -> Ordering ((path, searchUnsafe (Ordering nodes') path') : nodes')
  where
    Ordering nodes' = reduceModule $ Ordering nodes
    inject (Path heading' x, Inline _ ex) e
      | heading == heading' = substitute ex (TermIdentifier x) e
    inject (_, Inline _ _) e = e
    inject (path@(Path heading' x), Text σ (CoreTerm p _)) e
      | heading == heading' = substitute (makeExtern path p σ) (TermIdentifier x) e
    inject (_, Text _ _) e = e
    inject (_, Import _ _) _ = error "import in reduction results"
