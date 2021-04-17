module Module where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (State, StateT, evalState, evalStateT, execStateT, get, modify)
import Core.Ast.Common
import Core.Ast.Multiplicity
import Core.Ast.Pattern
import Core.Ast.Term
import Core.Ast.Type
import Core.TypeCheck
import Data.Bifunctor (first)
import Data.Functor.Identity (Identity)
import Data.List (find, intercalate)
import Data.Map (Map, (!))
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
depend (Inline e) (Path location _) = first (Path location) <$> (Variables.toList $ freeVariables @(Term d p) e)
depend (Text e) (Path location _) = first (Path location) <$> (Variables.toList $ freeVariables @(Term d p) e)
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
    go [] = pure ()
    go ((Path heading name, Inline e@(CoreTerm p _)) : require) = do
      go require
      this <- get
      let enviroment = Map.findWithDefault emptyState heading this
      σ <- lift $ runCore (typeCheck e) enviroment
      let enviroment' = enviroment {typeEnvironment = Map.insert name (p, CoreMultiplicity Internal Unrestricted, σ) $ typeEnvironment enviroment}
      modify $ Map.insert heading enviroment'
    go ((Path heading name, Text e@(CoreTerm p _)) : require) = do
      go require
      this <- get
      let enviroment = Map.findWithDefault emptyState heading this
      σ' <- lift $ runCore (typeCheck e) enviroment
      lift $ runCore (checkText p =<< checkType p =<< typeCheckInternal σ') enviroment
      let σ = convert σ'
      let enviroment' = enviroment {typeEnvironment = Map.insert name (p, CoreMultiplicity Internal Unrestricted, σ) $ typeEnvironment enviroment}
      modify $ Map.insert heading enviroment'
    go ((Path heading name, Import p (Path targetHeading targetName)) : require) = do
      go require
      this <- get
      let enviroment = Map.findWithDefault emptyState heading this
      let (_, _, σ) = typeEnvironment (this ! targetHeading) ! targetName
      let enviroment' = enviroment {typeEnvironment = Map.insert name (p, CoreMultiplicity Internal Unrestricted, σ) $ typeEnvironment enviroment}
      modify $ Map.insert heading enviroment'
    convert (CoreType p (FunctionLiteralType σ τs)) = CoreType p $ FunctionPointer σ τs
    convert (CoreType p σ) = CoreType p $ mapType convert bound bound σ
      where
        bound (Bound pm σ) = Bound pm $ convert σ

mangle :: Path -> Symbol
mangle (Path path (Identifier name)) = Symbol $ (intercalate "_" $ extract <$> path) ++ name
  where
    extract (Identifier x) = x

reduceModule :: Semigroup p => ModuleOrder Silent p -> ModuleOrder Silent p
reduceModule (Ordering code) = Ordering $ evalState (go code) Map.empty
  where
    go :: Semigroup p => [(Path, Global Silent p)] -> State (Map [Identifier] [(Identifier, Term Silent p)]) [(Path, Global Silent p)]
    go [] = pure []
    go ((Path heading name, Inline e) : require) = do
      completed <- go require
      this <- get
      let replacements = Map.findWithDefault [] heading this
      let e' = reduce $ foldr (\(x, e') -> substitute e' x) e replacements
      modify $ Map.insert heading ((name, e') : replacements)
      pure $ (Path heading name, Inline e') : completed
    go ((path@(Path heading name), Text e) : require) = do
      completed <- go require
      this <- get
      let replacements = Map.findWithDefault [] heading this
      let e' = reduce $ foldr (\(x, e') -> substitute e' x) e replacements
      let ref = makeRef path e
      modify $ Map.insert heading ((name, ref) : replacements)
      pure $ (Path heading name, Text e') : completed
    go ((Path heading name, Import _ (Path targetHeading targetName)) : require) = do
      completed <- go require
      this <- get
      let replacements = Map.findWithDefault [] heading this
      let e' = fromJust $ lookup targetName (this ! targetHeading)
      modify $ Map.insert heading ((name, e') : replacements)
      pure $ (Path heading name, Inline e') : completed
    extract (CorePattern _ (PatternVariable _ σ)) = σ
    extract (CorePattern _ (PatternOfCourse _)) = error "of course in function pattern"
    makeRef :: Path -> Term Silent p -> Term Silent p
    makeRef path (CoreTerm p (FunctionLiteral _ _ τ (Bound pms _))) = CoreTerm p $ Extern Silent Silent (mangle path) τ (extract <$> pms)
    makeRef path (CoreTerm p e) = CoreTerm p $ mapTerm (makeRef path) id id bound bound bound bound e
      where
        bound (Bound pm e) = Bound pm (makeRef path e)
