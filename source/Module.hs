module Module where

import Ast.Common
import Ast.Term
import Ast.Type hiding (Inline)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (StateT, get, modify)
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

data GlobalF σ ς e
  = Inline ς e
  | Text ς e
  | Synonym σ
  deriving (Show)

data GlobalSource p = GlobalSource (GlobalF (TypeSource p) (TypeSchemeAuto p) (TermControlSource p)) deriving (Show)

instance Location GlobalSource where
  location (GlobalSource (Inline _ (TermManualSource (TermSchemeSource p _)))) = p
  location (GlobalSource (Inline _ (TermAutoSource (TermSource p _)))) = p
  location (GlobalSource (Text _ (TermManualSource (TermSchemeSource p _)))) = p
  location (GlobalSource (Text _ (TermAutoSource (TermSource p _)))) = p
  location (GlobalSource (Synonym (TypeSource p _))) = p

instance Functor GlobalSource where
  fmap f (GlobalSource (Inline ς e)) = GlobalSource $ Inline (fmap (fmap f) ς) (fmap f e)
  fmap f (GlobalSource (Text ς e)) = GlobalSource $ Text (fmap (fmap f) ς) (fmap f e)
  fmap f (GlobalSource (Synonym σ)) = GlobalSource $ Synonym (fmap f σ)

data GlobalInfer p = GlobalInfer (GlobalF TypeInfer TypeSchemeInfer (TermSchemeInfer p))

coreModule = Isomorph CoreModule $ \(CoreModule code) -> code

data ForwardGlobalF σ ς
  = ForwardText ς
  | ForwardSymonym σ
  deriving (Show)

data ForwardGlobalSource p = ForwardGlobalSource (ForwardGlobalF (TypeSource p) (TypeSchemeSource p)) deriving (Show)

instance Location ForwardGlobalSource where
  location (ForwardGlobalSource (ForwardSymonym (TypeSource p _))) = p
  location (ForwardGlobalSource (ForwardText (TypeSchemeSource p _))) = p

instance Functor ForwardGlobalSource where
  fmap f (ForwardGlobalSource (ForwardSymonym σ)) = ForwardGlobalSource (ForwardSymonym (fmap f σ))
  fmap f (ForwardGlobalSource (ForwardText σ)) = ForwardGlobalSource (ForwardText (fmap f σ))

data ForwardGlobalInfer = ForwardGlobalInfer (ForwardGlobalF TypeInfer TypeSchemeInfer) deriving (Show)

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

synonym = Prism Synonym $ \case
  Synonym σ -> Just σ
  _ -> Nothing

data ModuleError p
  = IllegalPath p Path
  | IncompletePath p Path
  | IndexingGlobal p Path
  | Cycle p Path
  deriving (Show)

cleanScheme :: GlobalSource p -> GlobalSource p
cleanScheme i
  | (GlobalSource (Inline (Just ς) (TermManualSource e))) <- i,
    Just e' <- matchSchemes ς e =
    GlobalSource (Inline (Just ς) (TermAutoSource e'))
  | (GlobalSource (Text (Just ς) (TermManualSource e))) <- i,
    Just e' <- matchSchemes ς e =
    GlobalSource (Text (Just ς) (TermAutoSource e'))
  | otherwise = i
  where
    matchSchemes (TypeSchemeSource _ (MonoType _)) (TermSchemeSource _ (MonoTerm e)) = Just e
    matchSchemes
      (TypeSchemeSource _ (TypeForall (Bound (TypePatternSource _ x _ _) σ)))
      (TermSchemeSource _ (TypeAbstraction (Bound (TypePatternSource _ x' _ _) e)))
        | x == x' =
          matchSchemes σ e
    matchSchemes _ _ = Nothing

-- nodes without dependencies are at the start of the list
order :: Semigroup p => Module (GlobalSource p) -> Either (ModuleError p) [(Path, GlobalSource p)]
order = order' forward depend
  where
    extractTerm = Map.mapKeysMonotonic (\(TermIdentifier x) -> x)
    extractType = Map.mapKeysMonotonic (\(TypeIdentifier x) -> x)
    extractGlobalTerm = Map.mapKeysMonotonic (\(TermGlobalIdentifier x) -> x)
    extractGlobalType = Map.mapKeysMonotonic (\(TypeGlobalIdentifier x) -> x)

    forward (GlobalSource (Text (Just _) _)) = True
    forward _ = False

    depend :: Semigroup p => GlobalSource p -> Path -> Map Path p
    depend item (Path heading _)
      | (GlobalSource (Inline ς e)) <- item = freeTerm ς e
      | (GlobalSource (Text ς e)) <- item = freeTerm ς e
      | (GlobalSource (Synonym σ)) <- item = freeType σ
      where
        scope = Map.mapKeysMonotonic (Path heading)
        freeTerm ς e
          | (Just ς') <- ς, (TermAutoSource _) <- e = Map.unionWith (<>) common (remove ς' freeTVars)
          | otherwise = Map.unionWith (<>) common freeTVars
          where
            common =
              foldr
                (Map.unionWith (<>))
                Map.empty
                [freeVars, freeGlobalVars, freeTVarsAnn, freeGlobalTVarsAnn, freeGlobalTVars]
            freeVars = scope $ extractTerm $ runVariables $ freeVariablesTermSource e
            freeGlobalVars = extractGlobalTerm $ runVariables $ freeVariablesGlobalTermSource e
            freeTVarsAnn = case ς of
              Nothing -> Map.empty
              Just ς -> scope $ extractType $ runVariables $ freeVariablesTypeSource ς
            freeTVars = scope $ extractType $ runVariables $ freeVariablesTypeSource e
            freeGlobalTVarsAnn = case ς of
              Just ς -> extractGlobalType $ runVariables $ freeVariablesGlobalTypeSource ς
              Nothing -> Map.empty
            freeGlobalTVars = extractGlobalType $ runVariables $ freeVariablesGlobalTypeSource e
            remove (TypeSchemeSource _ (MonoType _)) vars = vars
            remove (TypeSchemeSource _ (TypeForall (Bound (TypePatternSource _ (TypeIdentifier x) _ _) σ))) vars =
              Map.delete (Path heading x) $ remove σ vars
        freeType σ = dependType heading σ

dependType heading σ =
  Map.unionWith
    (<>)
    (scope $ extractType $ runVariables $ freeVariablesTypeSource σ)
    (extractGlobalType $ runVariables $ freeVariablesGlobalTypeSource σ)
  where
    scope = Map.mapKeysMonotonic (Path heading)
    extractType = Map.mapKeysMonotonic (\(TypeIdentifier x) -> x)
    extractGlobalType = Map.mapKeysMonotonic (\(TypeGlobalIdentifier x) -> x)

order' forward depend code = sortTopological view quit children globals
  where
    globals = items [] code
    view (path, _) = path
    quit (path, global) = Left $ Cycle (location global) path
    children (path, global) =
      fmap (filter $ Prelude.not . forward . snd) $
        for (Map.toList $ depend global path) $ \(path, p) -> do
          global <- resolve p code path
          pure (path, global)

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

forwardDeclarations :: Module (GlobalSource p) -> Module (ForwardGlobalSource p)
forwardDeclarations = mapMaybe forward
  where
    forward (GlobalSource (Text (Just σ) _)) = Just $ ForwardGlobalSource $ ForwardText σ
    forward (GlobalSource (Synonym σ)) = Just $ ForwardGlobalSource $ ForwardSymonym σ
    forward _ = Nothing

orderForward :: Semigroup p => Module (ForwardGlobalSource p) -> Either (ModuleError p) [(Path, ForwardGlobalSource p)]
orderForward = order' (const False) depend
  where
    depend (ForwardGlobalSource (ForwardSymonym σ)) (Path heading _) = dependType heading σ
    depend (ForwardGlobalSource (ForwardText σ)) (Path heading _) = dependType heading σ

typeCheckModuleForward ::
  [(Path, ForwardGlobalSource p)] ->
  StateT
    (CoreEnvironment p)
    (Either (TypeError p))
    [(Path, (p, ForwardGlobalInfer))]
typeCheckModuleForward [] = pure []
typeCheckModuleForward ((path@(Path heading _), item) : nodes) = do
  environment <- bindMembers heading <$> get
  (item', σ) <- case item of
    ForwardGlobalSource (ForwardText σ) -> do
      (σ, _) <- lift $ runCore (kindCheckScheme SymbolMode σ) environment emptyState
      pure (ForwardGlobalInfer $ ForwardText σ, Right $ flexible $ convertFunctionLiteral σ)
    ForwardGlobalSource (ForwardSymonym σ) -> do
      (σ, _) <- lift $ runCore (kindCheck σ) environment emptyState
      pure (ForwardGlobalInfer $ ForwardSymonym σ, Left σ)
  modify (updateEnvironment path (location item) σ)
  ((path, (location item, item')) :) <$> typeCheckModuleForward nodes

convertFunctionLiteral ς = case ς of
  TypeSchemeCore (MonoType (TypeCore (FunctionLiteralType σ π τ))) -> polyEffect "R" (TypeCore $ FunctionPointer σ π τ)
  TypeSchemeCore (TypeForall (Bound pm ς)) -> TypeSchemeCore $ TypeForall (Bound pm $ convertFunctionLiteral ς)
  _ -> error "not function literal"

reduceModuleForword :: [(Path, (p, ForwardGlobalInfer))] -> (Reducer p)
reduceModuleForword [] = Reducer Map.empty Map.empty
reduceModuleForword ((path, (p, item)) : nodes) = case item of
  ForwardGlobalInfer (ForwardSymonym σ) ->
    reducer
      { reducerTypes = Map.insert (TypeGlobalIdentifier path) σ $ reducerTypes reducer
      }
  ForwardGlobalInfer (ForwardText σ) ->
    reducer
      { reducerTerms = Map.insert (TermGlobalIdentifier path) (makeExtern path p σ) $ reducerTerms reducer
      }
  where
    reducer = reduceModuleForword nodes


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
bindMembers heading environment =
  environment
    { typeEnvironment = Map.foldrWithKey bind Map.empty (typeGlobalEnvironment environment),
      kindEnvironment = Map.foldrWithKey bindType Map.empty (kindGlobalEnvironment environment)
    }
  where
    bind (TermGlobalIdentifier (Path heading' name)) e σΓ | heading == heading' = Map.insert (TermIdentifier name) e σΓ
    bind _ _ σΓ = σΓ
    bindType (TypeGlobalIdentifier (Path heading' name)) e σΓ | heading == heading' = Map.insert (TypeIdentifier name) e σΓ
    bindType _ _ σΓ = σΓ

updateEnvironment path p σ environment = case σ of
  Right σ ->
    environment
      { typeGlobalEnvironment =
          Map.insert
            (TermGlobalIdentifier path)
            (TermBinding p (TypeCore $ TypeSub Unrestricted) σ)
            $ typeGlobalEnvironment environment
      }
  Left σ ->
    environment
      { kindGlobalEnvironment =
          Map.insert
            (TypeGlobalIdentifier path)
            (LinkTypeBinding σ)
            $ kindGlobalEnvironment environment
      }

typeCheckModule ::
  [(Path, GlobalSource p)] ->
  StateT
    (CoreEnvironment p)
    (Either (TypeError p))
    [(Path, GlobalInfer p)]
typeCheckModule [] = pure []
typeCheckModule ((path@(Path heading _), item) : nodes) = do
  environment <- bindMembers heading <$> get
  (item', σ) <- case item of
    GlobalSource (Inline Nothing (TermAutoSource e)) -> do
      (e, σ) <- lift $ runCore (typeCheckGlobalAuto InlineMode e) environment emptyState
      pure (GlobalInfer $ Inline σ e, Right $ flexible σ)
    GlobalSource (Inline (Just σ) (TermAutoSource e)) -> do
      (e, σ) <- lift $ runCore (typeCheckGlobalScope InlineMode e σ) environment emptyState
      pure (GlobalInfer $ Inline σ e, Right $ flexible σ)
    GlobalSource (Inline Nothing (TermManualSource e)) -> do
      (e, σ) <- lift $ runCore (typeCheckGlobalSemi InlineMode e) environment emptyState
      pure (GlobalInfer $ Inline σ e, Right $ flexible σ)
    GlobalSource (Inline (Just σ) (TermManualSource e)) -> do
      (e, σ) <- lift $ runCore (typeCheckGlobalManual InlineMode e σ) environment emptyState
      pure (GlobalInfer $ Inline σ e, Right $ flexible σ)
    GlobalSource (Text Nothing (TermAutoSource e)) -> do
      (e, σ) <- lift $ runCore (typeCheckGlobalAuto SymbolMode e >>= syntaticCheck) environment emptyState
      pure (GlobalInfer $ Text σ e, Right $ convertFunctionLiteral $ flexible σ)
    GlobalSource (Text (Just σ) (TermAutoSource e)) -> do
      (e, σ) <- lift $ runCore (typeCheckGlobalScope SymbolMode e σ) environment emptyState
      pure (GlobalInfer $ Text σ e, Right $ convertFunctionLiteral $ flexible σ)
    GlobalSource (Text (Just σ) (TermManualSource e)) -> do
      (e, σ) <- lift $ runCore (typeCheckGlobalManual SymbolMode e σ >>= syntaticCheck) environment emptyState
      pure (GlobalInfer $ Text σ e, Right $ convertFunctionLiteral $ flexible σ)
    GlobalSource (Text Nothing (TermManualSource e)) -> do
      (e, σ) <- lift $ runCore (typeCheckGlobalSemi SymbolMode e >>= syntaticCheck) environment emptyState
      pure (GlobalInfer $ Text σ e, Right $ convertFunctionLiteral $ flexible σ)
    GlobalSource (Synonym σ) -> do
      (σ, _) <- lift $ runCore (kindCheck σ) environment emptyState
      pure (GlobalInfer $ Synonym σ, Left σ)

  modify (updateEnvironment path (location item) σ)
  ((path, item') :) <$> typeCheckModule nodes

data Reducer p = Reducer
  { reducerTerms :: Map TermGlobalIdentifier (TermSchemeInfer p),
    reducerTypes :: Map TypeGlobalIdentifier TypeInfer
  }
  deriving (Show)

reduceModule ::
  Reducer p ->
  [(Path, GlobalInfer p)] ->
  [(Path, GlobalInfer p)]
reduceModule _ [] = []
reduceModule globals ((path@(Path heading _), item) : nodes) =
  (path, item') : reduceModule globals' nodes
  where
    (item', binding) = case item of
      GlobalInfer (Inline σ e) ->
        let
           e' = reduce $ applyGlobalTypes $ applyGlobalTerms e
           σ' = applyGlobalTypes σ
         in (GlobalInfer (Inline σ' e'), Right e')
      GlobalInfer (Text σ e@(TermSchemeCore p _)) ->
        let
           e' = reduce $ applyGlobalTypes $ applyGlobalTerms e
           σ' = applyGlobalTypes σ
         in (GlobalInfer (Text σ' e'), Right (makeExtern path p σ))
      -- todo reduce synonyms
      GlobalInfer (Synonym σ) ->
        let σ' = applyGlobalTypes σ
         in (GlobalInfer (Synonym σ'), Left σ')

    applyGlobalTerms e = foldr applyTermGlobal (foldr applyTerm e (freeVariablesTerm e)) (freeVariablesGlobalTerm e)
    applyGlobalTypes σ = foldr applyTypeGlobal (foldr applyType σ (freeVariablesType σ)) (freeVariablesGlobalType σ)

    applyTerm x@(TermIdentifier name) e = case Map.lookup (TermGlobalIdentifier (Path heading name)) (reducerTerms globals) of
      Just ex -> substituteTerm ex x e
      Nothing -> e

    applyTermGlobal x e = case Map.lookup x (reducerTerms globals) of
      Just ex -> substituteGlobalTerm ex x e
      Nothing -> e

    applyType x@(TypeIdentifier name) e = case Map.lookup (TypeGlobalIdentifier (Path heading name)) (reducerTypes globals) of
      Just σx -> substituteType σx x e
      Nothing -> e

    applyTypeGlobal x e = case Map.lookup x (reducerTypes globals) of
      Just ex -> substituteGlobalType ex x e
      Nothing -> e

    globals' = case binding of
      Right e ->
        globals
          { reducerTerms = Map.insert (TermGlobalIdentifier path) e $ reducerTerms globals
          }
      Left σ ->
        globals
          { reducerTypes = Map.insert (TypeGlobalIdentifier path) σ $ reducerTypes globals
          }
