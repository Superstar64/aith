module Module where

import Ast.Common
import Ast.Kind
import Ast.Term
import Ast.Type hiding (Inline)
import Control.Monad.Trans.State.Strict (evalStateT, execStateT)
import Data.Map (Map, (!))
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

data ModuleError p
  = IllegalPath p Path
  | IncompletePath p Path
  | IndexingGlobal p Path
  | Cycle p Path
  deriving (Show)

newtype Module g = CoreModule (Map String (Item g)) deriving (Show, Functor)

coreModule = Isomorph CoreModule $ \(CoreModule code) -> code

data Item g
  = Module (Module g)
  | Global g
  deriving (Show, Functor)

modulex = Prism Module $ \case
  (Module code) -> Just code
  _ -> Nothing

data GlobalF ς p e
  = Inline ς e
  | Import p Path
  | Text ς e
  deriving (Show)

data GlobalSource p = GlobalSource (GlobalF (TypeSchemeAuto p) p (TermSchemeSource p))

instance Functor GlobalSource where
  fmap f (GlobalSource (Inline ς e)) = GlobalSource $ Inline (fmap (fmap f) ς) (fmap f e)
  fmap f (GlobalSource (Import p path)) = GlobalSource $ Import (f p) path
  fmap f (GlobalSource (Text ς e)) = GlobalSource $ Text (fmap (fmap f) ς) (fmap f e)

global = Prism (Global . GlobalSource) $ \case
  (Global (GlobalSource global)) -> Just global
  _ -> Nothing

data GlobalInfer p = GlobalInfer (GlobalF TypeSchemeInfer p (TermSchemeInfer p))

inline = Prism (uncurry Inline) $ \case
  (Inline σ e) -> Just (σ, e)
  _ -> Nothing

importx = Prism (uncurry Import) $ \case
  (Import p path) -> Just (p, path)
  _ -> Nothing

text = Prism (uncurry Text) $ \case
  (Text σ e) -> Just (σ, e)
  _ -> Nothing

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

extractTerm (TermIdentifier x) = x

extractType (TypeIdentifier x) = x

depend :: forall p. Semigroup p => GlobalSource p -> Path -> Map Path p
depend (GlobalSource (Inline _ e)) (Path location _) = Map.mapKeysMonotonic (Path location) (freeTerm)
  where
    freeTerm = Map.mapKeysMonotonic extractTerm $ runVariables $ freeVariablesTermSource e
depend (GlobalSource (Text _ e)) (Path location _) = Map.mapKeysMonotonic (Path location) (freeTerm)
  where
    freeTerm = Map.mapKeysMonotonic extractTerm $ runVariables $ freeVariablesTermSource e
depend (GlobalSource (Import p path)) _ = Map.singleton path p

-- nodes without dependencies are at the end of the list
data ModuleOrder g = Ordering [(Path, g)] deriving (Show, Functor)

items :: [String] -> Module (GlobalSource p) -> [(Path, GlobalSource p)]
items heading (CoreModule code) = do
  (name, item) <- Map.toList code
  case item of
    Module inner -> items (heading ++ [name]) inner
    Global global -> pure $ (Path heading name, global)

order :: Semigroup p => Module (GlobalSource p) -> Either (ModuleError p) (ModuleOrder (GlobalSource p))
order code = Ordering <$> execStateT (evalStateT go (const Unmarked <$> globals)) []
  where
    globals = Map.fromList $ items [] code
    go = sortTopological index finish view quit children
      where
        index path = (mempty, path, globals ! path)
        finish (_, path, global) = (path, global)
        view (_, path, _) = path
        quit (p, path, _) = case p of
          Just p -> Left $ Cycle p path
          Nothing -> error "temporary mark on top level"
        children (_, path, global) = for (Map.toList $ depend global path) $ \(path, p) -> do
          global <- resolve p code path
          pure (Just p, path, global)

unorder :: ModuleOrder g -> Module g
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
  ModuleOrder (GlobalInfer p) ->
  Path ->
  GlobalInfer p
searchUnsafe (Ordering []) _ = error "bad search"
searchUnsafe (Ordering ((path, e) : _)) path' | path == path' = e
searchUnsafe (Ordering (_ : items)) path' = searchUnsafe (Ordering items) path'

typeCheckModule :: ModuleOrder (GlobalSource p) -> Either (TypeError p) (ModuleOrder (GlobalInfer p))
typeCheckModule (Ordering []) = pure $ Ordering []
typeCheckModule (Ordering ((path@(Path heading _), item) : nodes)) = do
  Ordering nodes' <- typeCheckModule $ Ordering nodes
  let env = foldr (inject $ searchUnsafe $ Ordering nodes') emptyEnvironment nodes'
  case item of
    GlobalSource (Inline Nothing (TermSchemeSource _ (MonoTerm e))) -> do
      (e, σ) <- runCore (typeCheckGlobalAuto e) env emptyState
      pure $ Ordering ((path, GlobalInfer $ Inline σ e) : nodes')
    GlobalSource (Inline σ e) -> do
      (e, σ) <- runCore (typeCheckGlobalManual e σ) env emptyState
      pure $ Ordering ((path, GlobalInfer $ Inline σ e) : nodes')
    GlobalSource (Text Nothing (TermSchemeSource _ (MonoTerm e))) -> do
      (e, σ) <- runCore (typeCheckGlobalAuto e >>= syntaticCheck) env emptyState
      pure $ Ordering ((path, GlobalInfer $ Text σ e) : nodes')
    GlobalSource (Text σ e) -> do
      (e, σ) <- runCore (typeCheckGlobalManual e σ >>= syntaticCheck) env emptyState
      pure $ Ordering ((path, GlobalInfer $ Text σ e) : nodes')
    GlobalSource (Import p sym) -> pure $ Ordering ((path, GlobalInfer $ Import p sym) : nodes')
  where
    inject ::
      (Path -> GlobalInfer p) ->
      (Path, GlobalInfer p) ->
      CoreEnvironment p ->
      CoreEnvironment p
    inject _ (Path heading' _, _) e | heading /= heading' = e
    inject _ (Path _ name, (GlobalInfer (Inline σ (TermSchemeCore p _)))) env =
      env
        { typeEnvironment =
            Map.insert (TermIdentifier name) (p, Unrestricted, flexibleType $ flexibleKind σ) $ typeEnvironment env
        }
    inject _ (Path _ name, (GlobalInfer (Text σ (TermSchemeCore p _)))) env =
      env
        { typeEnvironment =
            Map.insert (TermIdentifier name) (p, Unrestricted, convertFunctionLiteral $ flexibleType $ flexibleKind σ) $ typeEnvironment env
        }
    inject search (path, (GlobalInfer (Import _ path'))) e =
      inject search (path, search path') e

convertFunctionLiteral ς = case ς of
  TypeSchemeCore (MonoType (TypeCore (FunctionLiteralType σ π τ))) -> polyEffect "R" (TypeCore $ FunctionPointer σ π τ)
  TypeSchemeCore (ImplicitForall (Bound pm ς) c π) -> TypeSchemeCore $ ImplicitForall (Bound pm $ convertFunctionLiteral ς) c π
  _ -> error "not function literal"

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

reduceModule ::
  ModuleOrder (GlobalInfer p) ->
  ModuleOrder (GlobalInfer p)
reduceModule (Ordering []) = Ordering []
reduceModule (Ordering ((path@(Path heading _), item) : nodes)) = case item of
  GlobalInfer (Inline σ e) ->
    let e' = reduce $ foldr inject e nodes'
     in Ordering ((path, GlobalInfer (Inline σ e')) : nodes')
  GlobalInfer (Text σ e) ->
    let e' = reduce $ foldr inject e nodes'
     in Ordering ((path, GlobalInfer (Text σ e')) : nodes')
  GlobalInfer (Import _ path') -> Ordering ((path, searchUnsafe (Ordering nodes') path') : nodes')
  where
    Ordering nodes' = reduceModule $ Ordering nodes
    inject (Path heading' _, _) e | heading /= heading' = e
    inject (Path _ x, GlobalInfer (Inline _ ex)) e
      | (TermIdentifier x) `Set.member` freeVariablesTerm e = substituteTerm ex (TermIdentifier x) e
    inject (_, GlobalInfer (Inline _ _)) e = e
    inject (path@(Path _ x), (GlobalInfer (Text σ (TermSchemeCore p _)))) e
      | (TermIdentifier x) `Set.member` freeVariablesTerm e = substituteTerm (makeExtern path p σ) (TermIdentifier x) e
    inject (_, GlobalInfer (Text _ _)) e = e
    inject (_, GlobalInfer (Import _ _)) _ = error "import in reduction results"
