module Module where

import Ast.Common
import Ast.Kind (KindAuto, KindInfer, mapKind)
import Ast.Term
import Ast.Type hiding (Inline)
import Control.Monad.State.Strict (StateT, evalStateT, execStateT)
import Control.Monad.Trans (lift)
import Data.Bifunctor (second)
import Data.Functor.Identity
import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Void
import Misc.Isomorph
import Misc.Path
import Misc.Prism
import Misc.Symbol
import Misc.Util
import TypeCheck
import TypeCheck.Core

data ModuleError p
  = IllegalPath p Path
  | IncompletePath p Path
  | IndexingGlobal p Path
  | Cycle p Path
  deriving (Show)

class (Monad m, Semigroup p) => ModuleQuit p m where
  moduleQuit :: ModuleError p -> m a
  typeQuit :: TypeError p -> m a

instance ModuleQuit Internal Identity where
  moduleQuit e = error $ "module error:" ++ show e
  typeQuit e = error $ "type error:" ++ show e

instance ModuleQuit p m => ModuleQuit p (StateT s m) where
  moduleQuit = lift . moduleQuit
  typeQuit = lift . typeQuit

runCoreModule :: ModuleQuit p m => Core p a -> CoreEnvironment p -> CoreState p -> m a
runCoreModule m enviroment state = case runCore m enviroment state of
  Right (e, _) -> pure e
  Left err -> typeQuit err

newtype Module ς θ κ σ p = CoreModule (Map String (Item ς θ κ σ p)) deriving (Show)

type ModuleAuto p = Module (TypeSchemeAuto p) () (KindAuto p) (TypeAuto p) p

mapModuleAuto :: (p -> p') -> ModuleAuto p -> ModuleAuto p'
mapModuleAuto f (CoreModule m) = CoreModule $ fmap (mapItemAuto f) m

coreModule = Isomorph CoreModule $ \(CoreModule code) -> code

data Item ς θ κ σ p
  = Module (Module ς θ κ σ p)
  | Global (Global ς θ κ σ p)
  deriving (Show)

mapItemAuto :: (p -> p') -> ItemAuto p -> ItemAuto p'
mapItemAuto f (Module m) = Module $ mapModuleAuto f m
mapItemAuto f (Global g) = Global $ mapGlobal (fmap $ mapTypeScheme (fmap $ mapKind absurd f) absurd f f) id (fmap $ fmap f) (fmap $ mapType (fmap $ mapKind absurd f) absurd f) f g

type ItemAuto p = Item (TypeSchemeAuto p) () (KindAuto p) (TypeAuto p) p

modulex = Prism Module $ \case
  (Module code) -> Just code
  _ -> Nothing

global = Prism Global $ \case
  (Global global) -> Just global
  _ -> Nothing

data Global ς θ κ σ p
  = Inline ς (Term θ κ σ p)
  | Import p Path
  | Text ς (Term θ κ σ p)
  deriving (Show)

type GlobalAuto p = Global (TypeSchemeAuto p) () (KindAuto p) (TypeAuto p) p

mapGlobal ::
  (ς -> ς') ->
  (θ -> θ') ->
  (κ -> κ') ->
  (σ -> σ') ->
  (p -> p') ->
  Global ς θ κ σ p ->
  Global ς' θ' κ' σ' p'
mapGlobal f g j h i global = case global of
  Inline ς e -> Inline (f ς) (mapTerm g j h i e)
  Text ς e -> Text (f ς) (mapTerm g j h i e)
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

resolve :: ModuleQuit p m => p -> ModuleAuto p -> Path -> m (GlobalAuto p)
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
depend (Inline _ e) (Path location _) = Map.mapKeysMonotonic (Path location) (freeTerm)
  where
    freeTerm = Map.mapKeysMonotonic extractTerm $ runVariables $ freeVariablesPositioned @TermIdentifier e
depend (Text _ e) (Path location _) = Map.mapKeysMonotonic (Path location) (freeTerm)
  where
    freeTerm = Map.mapKeysMonotonic extractTerm $ runVariables $ freeVariablesPositioned @TermIdentifier e
depend (Import p path) _ = Map.singleton path p

-- nodes without dependencies are at the end of the list
data ModuleOrder ς θ κ σ p = Ordering [(Path, Global ς θ κ σ p)] deriving (Show)

type ModuleOrderAuto p = ModuleOrder (TypeSchemeAuto p) () (KindAuto p) (TypeAuto p) p

instance
  ( UnInfer σ (TypeAuto Internal),
    UnInfer ς (TypeSchemeAuto Internal),
    UnInfer κ (KindAuto Internal)
  ) =>
  UnInfer (ModuleOrder ς θ κ σ p) (ModuleOrderAuto Internal)
  where
  unInfer = mapOrder unInfer (const ()) unInfer unInfer (const Internal)

mapOrder ::
  (ς -> ς') ->
  (θ -> θ') ->
  (κ -> κ') ->
  (σ -> σ') ->
  (p -> p') ->
  ModuleOrder ς θ κ σ p ->
  ModuleOrder ς' θ' κ' σ' p'
mapOrder f j g h i (Ordering nodes) = Ordering $ map (second (mapGlobal f j g h i)) nodes

items :: [String] -> ModuleAuto p -> [(Path, GlobalAuto p)]
items heading (CoreModule code) = do
  (name, item) <- Map.toList code
  case item of
    Module inner -> items (heading ++ [name]) inner
    Global global -> pure $ (Path heading name, global)

order code = Ordering <$> execStateT (evalStateT go (const Unmarked <$> globals)) []
  where
    globals = Map.fromList $ items [] code
    go = sortTopological index finish view quit children
      where
        index path = (mempty, path, globals ! path)
        finish (_, path, global) = (path, global)
        view (_, path, _) = path
        quit (p, path, _) = case p of
          Just p -> moduleQuit $ Cycle p path
          Nothing -> error "temporary mark on top level"
        children (_, path, global) = for (Map.toList $ depend global path) $ \(path, p) -> do
          global <- resolve p code path
          pure (Just p, path, global)

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
  ModuleOrder TypeSchemeInfer InstantiationInfer KindInfer TypeInfer p ->
  Path ->
  Global TypeSchemeInfer InstantiationInfer KindInfer TypeInfer p
searchUnsafe (Ordering []) _ = error "bad search"
searchUnsafe (Ordering ((path, e) : _)) path' | path == path' = e
searchUnsafe (Ordering (_ : items)) path' = searchUnsafe (Ordering items) path'

typeCheckModule :: ModuleQuit p m => ModuleOrderAuto p -> m (ModuleOrder TypeSchemeInfer InstantiationInfer KindInfer TypeInfer p)
typeCheckModule (Ordering []) = pure $ Ordering []
typeCheckModule (Ordering ((path@(Path heading _), item) : nodes)) = do
  Ordering nodes' <- typeCheckModule $ Ordering nodes
  let env = foldr (inject $ searchUnsafe $ Ordering nodes') emptyEnvironment nodes'
  case item of
    Inline Nothing e -> do
      (e, σ) <- runCoreModule (typeCheckGlobal e) env emptyState
      pure $ Ordering ((path, Inline σ e) : nodes')
    Inline (Just σ) e -> do
      (e, σ) <- runCoreModule (typeCheckGlobalAnnotate e σ) env emptyState
      pure $ Ordering ((path, Inline σ e) : nodes')
    Text Nothing e -> do
      (e, σ) <- runCoreModule (typeCheckGlobalText e) env emptyState
      pure $ Ordering ((path, Text σ e) : nodes')
    Text (Just σ) e -> do
      (e, σ) <- runCoreModule (typeCheckGlobalAnnotateText e σ) env emptyState
      pure $ Ordering ((path, Text σ e) : nodes')
    Import p sym -> pure $ Ordering ((path, Import p sym) : nodes')
  where
    inject ::
      (Path -> Global TypeSchemeInfer InstantiationInfer KindInfer TypeInfer p) ->
      (Path, Global TypeSchemeInfer InstantiationInfer KindInfer TypeInfer p) ->
      CoreEnvironment p ->
      CoreEnvironment p
    inject _ (Path heading' _, _) e | heading /= heading' = e
    inject _ (Path _ name, Inline σ (CoreTerm p _)) env =
      env {typeEnvironment = Map.insert (TermIdentifier name) (p, Unrestricted, mapTypeScheme (mapKind absurd id) absurd id id σ) $ typeEnvironment env}
    inject _ (Path _ name, Text σ (CoreTerm p _)) env =
      env {typeEnvironment = Map.insert (TermIdentifier name) (p, Unrestricted, transform σ) $ typeEnvironment env}
      where
        transform = convertFunctionLiteral . mapTypeScheme (mapKind absurd id) absurd id id
    inject search (path, Import _ path') e =
      inject search (path, search path') e

convertFunctionLiteral ς = case ς of
  CoreTypeScheme _ (MonoType (CoreType p (FunctionLiteralType σ π τ))) -> polyEffect id (CoreType p $ FunctionPointer σ π τ)
  CoreTypeScheme p (ImplicitForall (Bound pm ς) c π) -> CoreTypeScheme p $ ImplicitForall (Bound pm $ convertFunctionLiteral ς) c π
  _ -> error "not function literal"

makeExtern ::
  Path ->
  p ->
  TypeSchemeInfer ->
  Term InstantiationInfer KindInfer TypeInfer p
makeExtern path p ς = case ς of
  CoreTypeScheme _ (MonoType (CoreType _ (FunctionLiteralType σ π τ))) -> CoreTerm p (TermRuntime $ Extern (mangle path) σ π τ)
  CoreTypeScheme _ (ImplicitForall (Bound _ σ) _ _) -> makeExtern path p σ
  _ -> error "not function literal"

reduceModule ::
  ModuleOrder TypeSchemeInfer InstantiationInfer KindInfer TypeInfer p ->
  ModuleOrder TypeSchemeInfer InstantiationInfer KindInfer TypeInfer p
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
    inject (Path heading' _, _) e | heading /= heading' = e
    inject (Path _ x, Inline _ ex) e
      | (TermIdentifier x) `Set.member` freeVariables @TermIdentifier e = substitute ex (TermIdentifier x) e
    inject (_, Inline _ _) e = e
    inject (path@(Path _ x), Text σ (CoreTerm p _)) e
      | (TermIdentifier x) `Set.member` freeVariables @TermIdentifier e = substitute (makeExtern path p σ) (TermIdentifier x) e
    inject (_, Text _ _) e = e
    inject (_, Import _ _) _ = error "import in reduction results"
