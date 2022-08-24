module Module where

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
  | Text ς e
  deriving (Show)

data GlobalSource p = GlobalSource (GlobalF (TypeSchemeAuto p) p (TermControlSource p)) deriving (Show)

instance Location GlobalSource where
  location (GlobalSource (Inline _ (TermManualSource (TermSchemeSource p _)))) = p
  location (GlobalSource (Inline _ (TermAutoSource (TermSource p _)))) = p
  location (GlobalSource (Text _ (TermManualSource (TermSchemeSource p _)))) = p
  location (GlobalSource (Text _ (TermAutoSource (TermSource p _)))) = p

instance Functor GlobalSource where
  fmap f (GlobalSource (Inline ς e)) = GlobalSource $ Inline (fmap (fmap f) ς) (fmap f e)
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
    children (path, global) = fmap concat $
      for (Map.toList $ depend global path) $ \(path, p) -> do
        global <- resolve p code path
        case global of
          GlobalSource (Text (Just _) _) -> pure []
          _ -> pure [(path, global)]

    extractTerm (TermIdentifier x) = x
    extractGlobalTerm (TermGlobalIdentifier x) = x

    depend :: Semigroup p => GlobalSource p -> Path -> Map Path p
    depend (GlobalSource (Inline _ e)) (Path location _) = Map.unionWith (<>) freeTerm freeGlobalTerm
      where
        freeTerm = Map.mapKeysMonotonic (Path location) freeTerm'
        freeTerm' = Map.mapKeysMonotonic extractTerm $ runVariables $ freeVariablesTermSource e
        freeGlobalTerm = Map.mapKeysMonotonic extractGlobalTerm $ runVariables $ freeVariablesGlobalTermSource e
    depend (GlobalSource (Text _ e)) (Path location _) = Map.unionWith (<>) freeTerm freeGlobalTerm
      where
        freeTerm = Map.mapKeysMonotonic (Path location) freeTerm'
        freeTerm' = Map.mapKeysMonotonic extractTerm $ runVariables $ freeVariablesTermSource e
        freeGlobalTerm = Map.mapKeysMonotonic extractGlobalTerm $ runVariables $ freeVariablesGlobalTermSource e

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

forwardDeclarations :: Module (GlobalSource p) -> Module (TypeSchemeSource p)
forwardDeclarations = mapMaybe forward
  where
    forward (GlobalSource (Text (Just σ) _)) = Just σ
    forward _ = Nothing

validateDeclarations :: Module (TypeSchemeSource p) -> Either (TypeError p) (Module (p, TypeSchemeInfer))
validateDeclarations = traverse $ \ς@(TypeSchemeSource p _) -> do
  ς <- runCore (fst <$> kindCheckScheme SymbolMode ς) emptyEnvironment emptyState
  pure (p, ς)

forwardDeclare :: Module (p, TypeSchemeInfer) -> CoreEnvironment p
forwardDeclare declarations = emptyEnvironment {typeGlobalEnviroment = globals}
  where
    globals = Map.mapKeysMonotonic TermGlobalIdentifier $ Map.map (\(p, ς) -> TermBinding p (TypeCore $ TypeSub Unrestricted) $ convertFunctionLiteral $ flexible ς) $ flatten declarations

convertFunctionLiteral ς = case ς of
  TypeSchemeCore (MonoType (TypeCore (FunctionLiteralType σ π τ))) -> polyEffect "R" (TypeCore $ FunctionPointer σ π τ)
  TypeSchemeCore (TypeForall (Bound pm ς)) -> TypeSchemeCore $ TypeForall (Bound pm $ convertFunctionLiteral ς)
  _ -> error "not function literal"

forwardDefine :: Module (p, TypeSchemeInfer) -> Map TermGlobalIdentifier (TermSchemeInfer p, TypeSchemeInfer)
forwardDefine = Map.mapKeysMonotonic TermGlobalIdentifier . Map.mapWithKey definition . flatten
  where
    definition path (p, ς) = (makeExtern path p ς, ς)

makeExtern ::
  Path ->
  p ->
  TypeSchemeInfer ->
  TermSchemeInfer p
makeExtern path p ς = case ς of
  TypeSchemeCore (MonoType (TypeCore (FunctionLiteralType σ π τ))) ->
    TermSchemeCore p $
      TypeAbstraction
        ( Bound (TypePattern (TypeIdentifier "R") (TypeCore Region) []) (TermSchemeCore p $ MonoTerm $ TermCore p (TermRuntime $ Extern (mangle path) σ π τ))
        )
  TypeSchemeCore (TypeForall (Bound (TypePattern x κ π) e)) ->
    TermSchemeCore p (TypeAbstraction (Bound (TypePattern x κ π) $ makeExtern path p e))
  _ -> error "not function literal"

bindMembers :: [String] -> CoreEnvironment p -> CoreEnvironment p
bindMembers heading environment = environment {typeEnvironment = Map.foldrWithKey bind Map.empty (typeGlobalEnviroment environment)}
  where
    bind (TermGlobalIdentifier (Path heading' name)) e σΓ | heading == heading' = Map.insert (TermIdentifier name) e σΓ
    bind _ _ σΓ = σΓ

typeCheckModule ::
  CoreEnvironment p ->
  [(Path, GlobalSource p)] ->
  Either (TypeError p) [(Path, GlobalInfer p)]
typeCheckModule _ [] = pure []
typeCheckModule environment ((path@(Path heading _), item) : nodes) = do
  environment <- pure $ bindMembers heading environment
  (item', σ) <- case item of
    GlobalSource (Inline Nothing (TermAutoSource e)) -> do
      (e, σ) <- runCore (typeCheckGlobalAuto InlineMode e) environment emptyState
      pure (GlobalInfer $ Inline σ e, flexible σ)
    GlobalSource (Inline (Just σ) (TermAutoSource e)) -> do
      (e, σ) <- runCore (typeCheckGlobalScope InlineMode e σ) environment emptyState
      pure (GlobalInfer $ Inline σ e, flexible σ)
    GlobalSource (Inline Nothing (TermManualSource e)) -> do
      (e, σ) <- runCore (typeCheckGlobalSemi InlineMode e) environment emptyState
      pure (GlobalInfer $ Inline σ e, flexible σ)
    GlobalSource (Inline (Just σ) (TermManualSource e)) -> do
      (e, σ) <- runCore (typeCheckGlobalManual InlineMode e σ) environment emptyState
      pure (GlobalInfer $ Inline σ e, flexible σ)
    GlobalSource (Text Nothing (TermAutoSource e)) -> do
      (e, σ) <- runCore (typeCheckGlobalAuto SymbolMode e >>= syntaticCheck) environment emptyState
      pure (GlobalInfer $ Text σ e, convertFunctionLiteral $ flexible σ)
    GlobalSource (Text (Just σ) (TermAutoSource e)) -> do
      (e, σ) <- runCore (typeCheckGlobalScope SymbolMode e σ) environment emptyState
      pure (GlobalInfer $ Text σ e, convertFunctionLiteral $ flexible σ)
    GlobalSource (Text (Just σ) (TermManualSource e)) -> do
      (e, σ) <- runCore (typeCheckGlobalManual SymbolMode e σ >>= syntaticCheck) environment emptyState
      pure (GlobalInfer $ Text σ e, convertFunctionLiteral $ flexible σ)
    GlobalSource (Text Nothing (TermManualSource e)) -> do
      (e, σ) <- runCore (typeCheckGlobalSemi SymbolMode e >>= syntaticCheck) environment emptyState
      pure (GlobalInfer $ Text σ e, convertFunctionLiteral $ flexible σ)
  let environment' =
        environment
          { typeGlobalEnviroment = Map.insert (TermGlobalIdentifier path) (TermBinding (location item) (TypeCore $ TypeSub Unrestricted) σ) $ typeGlobalEnviroment environment
          }
  ((path, item') :) <$> typeCheckModule environment' nodes

reduceModule ::
  Map TermGlobalIdentifier (TermSchemeInfer p, TypeSchemeInfer) ->
  [(Path, GlobalInfer p)] ->
  [(Path, GlobalInfer p)]
reduceModule _ [] = []
reduceModule globals ((path@(Path heading _), item) : nodes) =
  (path, item') : reduceModule globals' nodes
  where
    reduceGlobal e = reduce $ foldr substitute e $ Map.toList $ globals
    substitute (x@(TermGlobalIdentifier (Path heading' name')), (ex, _))
      | heading == heading' =
        substituteTerm ex (TermIdentifier name') . substituteGlobalTerm ex x
      | otherwise = substituteGlobalTerm ex x
    (item', (σ', e')) = case item of
      GlobalInfer (Inline σ e) ->
        let e' = reduceGlobal e
         in (GlobalInfer (Inline σ e'), (σ, e'))
      GlobalInfer (Text σ e@(TermSchemeCore p _)) ->
        let e' = reduceGlobal e
         in (GlobalInfer (Text σ e'), (convertFunctionLiteral σ, makeExtern path p σ))
    globals' = Map.insert (TermGlobalIdentifier path) (e', σ') globals
