module Module where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (StateT, evalState, evalStateT, execStateT, get, modify)
import Core.Ast.Common
import Core.Ast.Multiplicity
import Core.Ast.Term
import Core.TypeCheck
import Data.Bifunctor (first)
import Data.List (find)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Traversable (for)
import Error
import Misc.Identifier (Identifier)
import Misc.Isomorph
import Misc.Path
import Misc.Prism
import qualified Misc.Variables as Variables

newtype Module p = CoreModule (Map Identifier (Item p)) deriving (Show, Functor)

coreModule = Isomorph CoreModule $ \(CoreModule code) -> code

data ItemF p
  = Module (Module p)
  | Global (Global p)
  deriving (Show, Functor)

modulex = Prism Module $ \case
  (Module code) -> Just code
  _ -> Nothing

global = Prism Global $ \case
  (Global global) -> Just global
  _ -> Nothing

data Item p = CoreItem p (ItemF p) deriving (Show, Functor)

item = Isomorph (uncurry CoreItem) $ \(CoreItem p item) -> (p, item)

data Global p
  = Inline (Term p)
  | Import p Path
  deriving (Show, Functor)

inline = Prism Inline $ \case
  (Inline e) -> Just e
  _ -> Nothing

importx = Prism (uncurry Import) $ \case
  (Import p path) -> Just (p, path)
  _ -> Nothing

resolve :: Base p m => p -> Module p -> Path -> m (Global p)
resolve p (CoreModule code) path = go code path
  where
    go code (Path [] name) = case Map.lookup name code of
      Nothing -> moduleQuit $ IllegalPath p path
      Just (CoreItem _ (Global global)) -> pure global
      Just (CoreItem p' (Module _)) -> moduleQuit $ IncompletePath p p' path
    go code (Path (first : remainder) name) = case Map.lookup first code of
      Nothing -> moduleQuit $ IllegalPath p path
      Just (CoreItem p' (Global _)) -> moduleQuit $ IndexingGlobal p p' path
      Just (CoreItem _ (Module (CoreModule code'))) -> go code' (Path remainder name)

depend :: forall p. Semigroup p => Global p -> Path -> [(Path, p)]
depend (Inline e) (Path location _) = first (Path location) <$> (Variables.toList $ freeVariables @(Term p) e)
depend (Import p path) _ = [(path, p)]

data ModuleOrder p = Ordering [(p, Path, Global p)] deriving (Show, Functor)

items :: [Identifier] -> Module a -> [(a, Path, Global a)]
items heading (CoreModule code) = do
  (name, CoreItem p item) <- Map.toList code
  case item of
    Module inner -> items (heading ++ [name]) inner
    Global global -> pure $ (p, Path heading name, global)

data Mark = Unmarked | Temporary | Permanent deriving (Eq)

-- https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search

visit ::
  Base a m =>
  Module a ->
  (a, Path, Global a) ->
  StateT (Map Path Mark) (StateT [(a, Path, Global a)] m) ()
visit code (p, path, global) = do
  marks <- get
  case marks ! path of
    Permanent -> pure ()
    Temporary -> lift $ lift $ moduleQuit $ Cycle p path
    Unmarked -> do
      modify $ Map.insert path Temporary
      let dependencies = depend global path
      children <- for dependencies $ \(path, p) -> do
        global <- lift $ lift $ resolve p code path
        pure (p, path, global)
      for children (visit code)
      modify $ Map.insert path Permanent
      lift $ modify $ ((p, path, global) :)

order :: Base p m => Module p -> m (ModuleOrder p)
order code = Ordering <$> execStateT (evalStateT go (const Unmarked <$> globals)) []
  where
    globals = Map.fromList $ (\(p, path, global) -> (path, (p, global))) <$> items [] code
    go = do
      this <- get
      let item = find (\(_, mark) -> mark /= Permanent) (Map.toList this)
      case item of
        Nothing -> pure ()
        Just (path, _) -> do
          let (p, global) = globals ! path
          visit code (p, path, global)
          go

unorder :: ModuleOrder Internal -> Module Internal
unorder (Ordering []) = CoreModule Map.empty
unorder (Ordering (item : remaining)) = insert item (unorder $ Ordering remaining)
  where
    insert (Internal, Path [] name, global) (CoreModule code) = CoreModule $ Map.insert name (CoreItem Internal $ Global global) code
    insert (Internal, Path (first : remainder) name, global) (CoreModule code) = case Map.findWithDefault (CoreItem Internal $ Module $ CoreModule Map.empty) first code of
      (CoreItem Internal (Module innerCode)) -> CoreModule $ Map.insert first innerCode' code
        where
          innerCode' = CoreItem Internal $ Module $ insert (Internal, Path remainder name, global) innerCode
      _ -> error "unorder error"

typeCheckModule :: Base p m => ModuleOrder p -> m (Map [Identifier] (CoreState p))
typeCheckModule (Ordering code) = execStateT (go code) mempty
  where
    go [] = pure ()
    go ((p, Path heading name, Inline e) : require) = do
      go require
      this <- get
      let enviroment = Map.findWithDefault emptyState heading this
      σ <- lift $ runCore (typeCheck e) enviroment
      let enviroment' = enviroment {typeEnvironment = Map.insert name (p, CoreMultiplicity Internal Unrestricted, σ) $ typeEnvironment enviroment}
      modify $ Map.insert heading enviroment'
    go ((p, Path heading name, Import _ (Path targetHeading targetName)) : require) = do
      go require
      this <- get
      let enviroment = Map.findWithDefault emptyState heading this
      let (_, _, σ) = typeEnvironment (this ! targetHeading) ! targetName
      let enviroment' = enviroment {typeEnvironment = Map.insert name (p, CoreMultiplicity Internal Unrestricted, σ) $ typeEnvironment enviroment}
      modify $ Map.insert heading enviroment'

reduceModule :: ModuleOrder Internal -> ModuleOrder Internal
reduceModule (Ordering code) = Ordering $ evalState (go code) Map.empty
  where
    go [] = pure []
    go ((Internal, Path heading name, Inline e) : require) = do
      completed <- go require
      this <- get
      let replacements = Map.findWithDefault [] heading this
      let e' = reduce $ foldr (\(x, e') -> substitute e' x) e replacements
      modify $ Map.insert heading ((name, e') : replacements)
      pure $ (Internal, Path heading name, Inline e') : completed
    go ((Internal, Path heading name, Import _ (Path targetHeading targetName)) : require) = do
      completed <- go require
      this <- get
      let replacements = Map.findWithDefault [] heading this
      let e' = fromJust $ lookup targetName (this ! targetHeading)
      modify $ Map.insert heading ((name, e') : replacements)
      pure $ (Internal, Path heading name, Inline e') : completed
