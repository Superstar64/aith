module Module where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (StateT, evalState, evalStateT, execStateT, get, modify)
import Core.Ast.Common
import Core.Ast.Multiplicity
import Core.Ast.Term
import Core.Ast.Type
import Core.TypeCheck
import Data.Bifunctor (bimap)
import Data.Foldable (foldrM)
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
import Misc.Symbol
import qualified Misc.Variables as Variables

newtype Module p = CoreModule (Map Identifier (Item p)) deriving (Functor, Show)

coreModule = Isomorph CoreModule $ \(CoreModule code) -> code

data Item p
  = Module (Module p)
  | Global (Global p)
  deriving (Functor, Show)

modulex = Prism Module $ \case
  (Module code) -> Just code
  _ -> Nothing

global = Prism Global $ \case
  (Global global) -> Just global
  _ -> Nothing

data Global p
  = Inline (Maybe (Type p)) (Term p)
  | Import p Path
  | Text (Maybe (Type p)) (Term p)
  | Synonym (Type p)
  deriving (Functor, Show)

inline = Prism (uncurry Inline) $ \case
  (Inline σ e) -> Just (σ, e)
  _ -> Nothing

importx = Prism (uncurry Import) $ \case
  (Import p path) -> Just (p, path)
  _ -> Nothing

text = Prism (uncurry Text) $ \case
  (Text σ e) -> Just (σ, e)
  _ -> Nothing

synonym = Prism Synonym $ \case
  (Synonym σ) -> Just σ
  _ -> Nothing

resolve :: Base p m => p -> Module p -> Path -> m (Global p)
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

depend :: forall p. Semigroup p => Global p -> Path -> Map Path p
depend (Inline σ e) (Path location _) = Map.mapKeysMonotonic (Path location) (Variables.toMap $ annotation <> freeVariables @(Term p) e <> freeVariables @(Type p) e)
  where
    annotation = case σ of
      Nothing -> mempty
      Just σ -> freeVariables @(Type p) σ
depend (Text σ e) (Path location _) = Map.mapKeysMonotonic (Path location) (Variables.toMap $ annotation <> freeVariables @(Term p) e <> freeVariables @(Type p) e)
  where
    annotation = case σ of
      Nothing -> mempty
      Just σ -> freeVariables @(Type p) σ
depend (Synonym σ) (Path location _) = Map.mapKeysMonotonic (Path location) (Variables.toMap $ freeVariables @(Type p) σ)
depend (Import p path) _ = Map.singleton path p

-- nodes without dependencies are at the end of the list
data ModuleOrder p = Ordering [(Path, Global p)] deriving (Functor)

items :: [Identifier] -> Module p -> [(Path, Global p)]
items heading (CoreModule code) = do
  (name, item) <- Map.toList code
  case item of
    Module inner -> items (heading ++ [name]) inner
    Global global -> pure $ (Path heading name, global)

data Mark = Unmarked | Temporary | Permanent deriving (Eq)

-- https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search

visit ::
  Base p m =>
  Module p ->
  (Maybe p, Path, Global p) ->
  StateT (Map Path Mark) (StateT [(Path, Global p)] m) ()
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

order :: Base p m => Module p -> m (ModuleOrder p)
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

unorder :: ModuleOrder p -> Module p
unorder (Ordering []) = CoreModule Map.empty
unorder (Ordering (item : remaining)) = insert item (unorder $ Ordering remaining)
  where
    insert (Path [] name, global) (CoreModule code) = CoreModule $ Map.insert name (Global global) code
    insert (Path (first : remainder) name, global) (CoreModule code) = case Map.findWithDefault (Module $ CoreModule Map.empty) first code of
      (Module innerCode) -> CoreModule $ Map.insert first innerCode' code
        where
          innerCode' = Module $ insert (Path remainder name, global) innerCode
      _ -> error "unorder error"

convertFunctionLiteral (CoreType p (FunctionLiteralType σ τs)) = CoreType p $ FunctionPointer σ τs
convertFunctionLiteral (CoreType p (Forall (Bound pm σ))) = CoreType p $ Forall (Bound pm (convertFunctionLiteral σ))
convertFunctionLiteral (CoreType p (Qualified π σ)) = CoreType p $ Qualified π (convertFunctionLiteral σ)
convertFunctionLiteral _ = error "unable to convert function literal"

typeCheckModule :: Base p m => ModuleOrder p -> m (Map [Identifier] (CoreState p))
typeCheckModule (Ordering code) = foldrM (execStateT . uncurry typeCheckItem) Map.empty code
  where
    getModuleEnviroments = get
    modifyModuleEnvironments = modify

    getEnvironment (Path heading _) = do
      environments <- getModuleEnviroments
      pure $ Map.findWithDefault emptyState heading environments

    insertGlobalTerm path@(Path heading name) p σ = do
      environment <- getEnvironment path
      modifyModuleEnvironments $ Map.insert heading environment {typeEnvironment = Map.insert name (p, Unrestricted, σ) $ typeEnvironment environment}

    insertGlobalSynonym path@(Path heading name) p κ σ = do
      environment <- getEnvironment path
      modifyModuleEnvironments $ Map.insert heading environment {kindEnvironment = Map.insert name (p, κ, Just σ) $ kindEnvironment environment}

    validateAnnotation _ _ _ Nothing = pure ()
    validateAnnotation environment p σ1 (Just σ2') = do
      σ2 <- runCore (instantiate σ2') environment
      match p σ1 σ2

    typeCheckItem path (Inline σ' e@(CoreTerm p _)) = do
      environment <- getEnvironment path
      σ <- runCore (typeCheck e) environment
      validateAnnotation environment p σ σ'
      insertGlobalTerm path p σ
    typeCheckItem path (Text σ' e@(CoreTerm p _)) = do
      environment <- getEnvironment path
      σ <- runCore (typeCheck e) environment
      runCore (checkText p =<< checkType p =<< typeCheckInternal σ) environment
      validateAnnotation environment p (convertFunctionLiteral σ) σ'
      insertGlobalTerm path p $ convertFunctionLiteral σ
    typeCheckItem path (Import p (Path heading name)) = do
      environments <- getModuleEnviroments
      case typeEnvironment (environments ! heading) !? name of
        Just (_, _, σ) -> insertGlobalTerm path p σ
        Nothing -> case kindEnvironment (environments ! heading) !? name of
          Just (_, κ, Just σ) -> insertGlobalSynonym path p κ σ
          _ -> error "import error"
    typeCheckItem path (Synonym σ'@(CoreType p _)) = do
      environment <- getEnvironment path
      (σ, κ) <- runCore (typeCheckInstantiate σ') environment
      insertGlobalSynonym path p κ σ

mangle :: Path -> Symbol
mangle (Path path (Identifier name)) = Symbol $ (concat $ map (++ "_") $ extract <$> path) ++ name
  where
    extract (Identifier x) = x

convertExtern p name (CoreType _ (FunctionPointer σ τs)) = CoreTerm p $ TermCommon $ Extern () () name (p <$ σ) (p <$ τs)
convertExtern p name (CoreType _ (Forall (Bound pm σ))) = CoreTerm p $ TypeAbstraction $ Bound (bimap (const p) (const p) pm) (convertExtern p name σ)
convertExtern p name (CoreType _ (Qualified τ σ)) = CoreTerm p $ QualifiedAssume (p <$ τ) (convertExtern p name σ)
convertExtern _ _ _ = error "unable to convert type to extern"

reduceModule :: Semigroup p => Map [Identifier] (CoreState p) -> ModuleOrder p -> ModuleOrder p
reduceModule environment (Ordering code) = Ordering $ evalState (foldrM go' [] code) Map.empty
  where
    getReplacements (Path heading _) = do
      this <- get
      pure $ Map.findWithDefault [] heading this
    insertGlobal path@(Path heading name) e = do
      replacements <- getReplacements path
      modify $ Map.insert heading ((name, e) : replacements)
    annotate (Path heading name) Nothing = do
      let (p, _, σ) = typeEnvironment (environment ! heading) ! name
      pure $ Just $ p <$ σ
    annotate path (Just σ) = do
      replacements <- getReplacements path
      pure $ Just $ reduce $ foldr substituteGlobal σ replacements

    go' item@(path, _) completed = do
      x <- go item
      pure ((path, x) : completed)
    go (path, Inline σ e) = do
      replacements <- getReplacements path
      let e' = reduce $ foldr substituteGlobal e replacements
      insertGlobal path (Right e')
      σ' <- annotate path σ
      pure (Inline σ' e')
    go (path@(Path heading name), Text τ e) = do
      replacements <- getReplacements path
      let e' = reduce $ foldr substituteGlobal e replacements
      let (p, _, σ) = typeEnvironment (environment ! heading) ! name
      let ref = convertExtern p (mangle path) σ
      insertGlobal path (Right ref)
      τ' <- annotate path τ
      pure (Text τ' e')
    go (path, Import _ (Path heading name)) = do
      this <- get
      let e = fromJust $ lookup name (this ! heading)
      insertGlobal path e
      case e of
        Left σ -> pure $ Synonym σ
        Right e -> do
          σ <- annotate path Nothing
          pure $ Inline σ e
    go (path, Synonym σ) = do
      replacements <- getReplacements path
      let σ' = reduce $ foldr substituteGlobal σ replacements
      insertGlobal path (Left σ')
      pure (Synonym σ')
    substituteGlobal (x, Right e) = substitute e x
    substituteGlobal (x, Left σ) = substitute σ x
