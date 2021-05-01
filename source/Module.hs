module Module where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (StateT, evalState, evalStateT, execStateT, get, modify)
import Core.Ast.Common
import Core.Ast.Multiplicity
import Core.Ast.Term
import Core.Ast.Type
import Core.TypeCheck
import Data.Bifunctor (bimap, first)
import Data.Functor.Identity (Identity)
import Data.List (find)
import Data.Map (Map, (!), (!?))
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Traversable (for)
import Error
import Misc.Identifier (Identifier (..))
import Misc.Isomorph
import Misc.Path
import Misc.Prism
import Misc.Silent
import Misc.Symbol
import qualified Misc.Variables as Variables

newtype Module d p = CoreModule (Map Identifier (Item d p)) deriving (Functor)

deriving instance (Show (d Identity), Show (d []), Show p, Show (d Erased)) => Show (Module d p)

coreModule = Isomorph CoreModule $ \(CoreModule code) -> code

data Item d p
  = Module (Module d p)
  | Global (Global d p)
  deriving (Functor)

deriving instance (Show (d Identity), Show (d []), Show p, Show (d Erased)) => Show (Item d p)

modulex = Prism Module $ \case
  (Module code) -> Just code
  _ -> Nothing

global = Prism Global $ \case
  (Global global) -> Just global
  _ -> Nothing

data Global d p
  = Inline (Term d p)
  | Import p Path
  | Text (Term d p)
  | Synonym (Type p)
  deriving (Functor)

deriving instance (Show (d Identity), Show (d []), Show p, Show (d Erased)) => Show (Global d p)

inline = Prism Inline $ \case
  (Inline e) -> Just e
  _ -> Nothing

importx = Prism (uncurry Import) $ \case
  (Import p path) -> Just (p, path)
  _ -> Nothing

text = Prism Text $ \case
  (Text e) -> Just e
  _ -> Nothing

synonym = Prism Synonym $ \case
  (Synonym σ) -> Just σ
  _ -> Nothing

resolve :: Base p m => p -> Module d p -> Path -> m (Global d p)
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

depend :: forall p d. Semigroup p => Global d p -> Path -> [(Path, p)]
depend (Inline e) (Path location _) = first (Path location) <$> (Variables.toList $ freeVariables @(Term d p) e <> freeVariables @(Type p) e)
depend (Text e) (Path location _) = first (Path location) <$> (Variables.toList $ freeVariables @(Term d p) e <> freeVariables @(Type p) e)
depend (Synonym σ) (Path location _) = first (Path location) <$> (Variables.toList $ freeVariables @(Type p) σ)
depend (Import p path) _ = [(path, p)]

data ModuleOrder d p = Ordering [(Path, Global d p)] deriving (Functor)

deriving instance (Show (d Identity), Show (d []), Show p, Show (d Erased)) => Show (ModuleOrder d p)

items :: [Identifier] -> Module d p -> [(Path, Global d p)]
items heading (CoreModule code) = do
  (name, item) <- Map.toList code
  case item of
    Module inner -> items (heading ++ [name]) inner
    Global global -> pure $ (Path heading name, global)

data Mark = Unmarked | Temporary | Permanent deriving (Eq)

-- https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search

visit ::
  Base p m =>
  Module d p ->
  (Maybe p, Path, Global d p) ->
  StateT (Map Path Mark) (StateT [(Path, Global d p)] m) ()
visit code (p, path, global) = do
  marks <- get
  case marks ! path of
    Permanent -> pure ()
    Temporary -> case p of
      Just p -> lift $ lift $ moduleQuit $ Cycle p path
      Nothing -> error "temporary mark on top level"
    Unmarked -> do
      modify $ Map.insert path Temporary
      let dependencies = depend global path
      children <- for dependencies $ \(path, p) -> do
        global <- lift $ lift $ resolve p code path
        pure (Just p, path, global)
      for children (visit code)
      modify $ Map.insert path Permanent
      lift $ modify $ ((path, global) :)

order :: Base p m => Module d p -> m (ModuleOrder d p)
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

unorder :: ModuleOrder d p -> Module d p
unorder (Ordering []) = CoreModule Map.empty
unorder (Ordering (item : remaining)) = insert item (unorder $ Ordering remaining)
  where
    insert (Path [] name, global) (CoreModule code) = CoreModule $ Map.insert name (Global global) code
    insert (Path (first : remainder) name, global) (CoreModule code) = case Map.findWithDefault (Module $ CoreModule Map.empty) first code of
      (Module innerCode) -> CoreModule $ Map.insert first innerCode' code
        where
          innerCode' = Module $ insert (Path remainder name, global) innerCode
      _ -> error "unorder error"

typeCheckModule :: Base p m => ModuleOrder d p -> m (Map [Identifier] (CoreState p))
typeCheckModule (Ordering code) = execStateT (go code) mempty
  where
    goCommon heading name p require f = do
      go require
      this <- get
      let environment = Map.findWithDefault emptyState heading this
      bound <- lift $ f environment this
      let environment' = case bound of
            Right σ -> environment {typeEnvironment = Map.insert name (p, Unrestricted, σ) $ typeEnvironment environment}
            Left (σ, κ) -> environment {kindEnvironment = Map.insert name (p, κ, Just σ) $ kindEnvironment environment}

      modify $ Map.insert heading environment'
    go [] = pure ()
    go ((Path heading name, Inline e@(CoreTerm p _)) : require) = goCommon heading name p require $ \environment _ -> do
      σ <- runCore (typeCheck e) environment
      pure (Right σ)
    go ((Path heading name, Text e@(CoreTerm p _)) : require) = goCommon heading name p require $ \environment _ -> do
      σ' <- runCore (typeCheck e) environment
      runCore (checkText p =<< checkType p =<< typeCheckInternal σ') environment
      pure $ Right $ convert σ'
    go ((Path heading name, Import p (Path targetHeading targetName)) : require) = goCommon heading name p require $ \_ this -> do
      case typeEnvironment (this ! targetHeading) !? targetName of
        Just (_, _, σ) -> pure (Right σ)
        Nothing -> case kindEnvironment (this ! targetHeading) !? targetName of
          Just (_, κ, Just σ) -> pure (Left (σ, κ))
          _ -> error "import error"
    go ((Path heading name, Synonym σ'@(CoreType p _)) : require) = goCommon heading name p require $ \environment _ -> do
      (σ, κ) <- runCore (typeCheckInstantiate σ') environment
      pure (Left (σ, κ))
    convert (CoreType p (FunctionLiteralType σ τs)) = CoreType p $ FunctionPointer σ τs
    convert (CoreType p σ) = CoreType p $ mapType convert id bound bound σ
      where
        bound (Bound pm σ) = Bound pm $ convert σ

mangle :: Path -> Symbol
mangle (Path path (Identifier name)) = Symbol $ (concat $ map (++ "_") $ extract <$> path) ++ name
  where
    extract (Identifier x) = x

reduceModule :: Semigroup p => Map [Identifier] (CoreState p) -> ModuleOrder Silent p -> ModuleOrder Silent p
reduceModule environment (Ordering code) = Ordering $ evalState (go code) Map.empty
  where
    goCommon heading name require f = do
      completed <- go require
      this <- get
      let replacements = Map.findWithDefault [] heading this
      let (e', global') = f replacements this
      modify $ Map.insert heading ((name, e') : replacements)
      pure $ (Path heading name, global') : completed
    go [] = pure []
    go ((Path heading name, Inline e) : require) = goCommon heading name require $ \replacements _ ->
      let e' = reduce $ foldr substituteGlobal e replacements
       in (Right e', Inline e')
    go ((path@(Path heading name), Text e) : require) = goCommon heading name require $ \replacements _ ->
      let e' = reduce $ foldr substituteGlobal e replacements
          (p, _, σ) = typeEnvironment (environment ! heading) ! name
          ref = convert p (mangle path) σ
       in (Right ref, Text e')
    go ((Path heading name, Import _ (Path targetHeading targetName)) : require) = goCommon heading name require $ \_ this ->
      let e' = fromJust $ lookup targetName (this ! targetHeading)
       in (e', either Synonym Inline e')
    go ((Path heading name, Synonym σ) : require) = goCommon heading name require $ \replacements _ ->
      let σ' = reduce $ foldr substituteGlobal σ replacements
       in (Left σ', Synonym σ')
    substituteGlobal (x, Right e) = substitute e x
    substituteGlobal (x, Left σ) = substitute σ x
    convert p name (CoreType _ (FunctionPointer σ τs)) = CoreTerm p $ Extern Silent Silent name (p <$ σ) (fmap (p <$) τs)
    convert p name (CoreType _ (Forall (Bound pm σ))) = CoreTerm p $ TypeAbstraction Silent $ Bound (bimap (const p) (const p) pm) (convert p name σ)
    convert p name (CoreType _ (ErasedQualified τ σ)) = CoreTerm p $ ErasedQualifiedAssume Silent (p <$ τ) (convert p name σ)
    convert _ _ _ = error "unable to convert type to extern"
