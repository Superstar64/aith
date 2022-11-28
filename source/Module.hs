module Module where

import Ast.Common
import Ast.Term
import Ast.Type hiding (Inline)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (StateT, get, modify)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Void (absurd)
import Misc.Isomorph
import Misc.Path
import Misc.Prism
import Misc.Symbol
import Misc.Util
import TypeCheck
import TypeCheck.Core
import TypeCheck.Unify (checkPretype, matchType)

newtype Module g = CoreModule (Map String (Item g)) deriving (Show, Functor, Foldable, Traversable)

data Item g
  = Module (Module g)
  | Global g
  deriving (Show, Functor, Foldable, Traversable)

data GlobalF σ ς e
  = Inline ς e
  | Text ς e
  | Synonym σ
  | NewType σ σ
  deriving (Show)

data ForwardF σ ς
  = ForwardNewtype σ
  | ForwardText ς

data GlobalSource p = GlobalSource (GlobalF (TypeSource p) (TypeSchemeAuto p) (TermControlSource p))

data DeclareSource p
  = DefinitionSource (GlobalSource p)
  | DeclarationSource (ForwardF (TypeSource p) (TypeSchemeSource p))

data GlobalInfer p = GlobalInfer (GlobalF TypeInfer TypeSchemeInfer (TermSchemeInfer p))

data DeclareInfer p
  = DefinitionInfer (GlobalInfer p)
  | DeclarationInfer p (ForwardF TypeInfer TypeSchemeInfer)

data ModuleError p
  = IllegalPath p Path
  | IncompletePath p Path
  | IndexingGlobal p Path
  | Cycle p Path
  deriving (Show)

positionGlobal (GlobalSource (Inline _ (TermManualSource (TermScheme p _)))) = p
positionGlobal (GlobalSource (Inline _ (TermAutoSource (Term p _)))) = p
positionGlobal (GlobalSource (Text _ (TermManualSource (TermScheme p _)))) = p
positionGlobal (GlobalSource (Text _ (TermAutoSource (Term p _)))) = p
positionGlobal (GlobalSource (Synonym (TypeAst p _))) = p
positionGlobal (GlobalSource (NewType _ (TypeAst p _))) = p

mapGlobalPosition :: (p -> p') -> GlobalSource p -> GlobalSource p'
mapGlobalPosition f (GlobalSource (Inline σ e)) = GlobalSource (Inline (fmap (mapTypePosition f) σ) (mapTermPosition f e))
mapGlobalPosition f (GlobalSource (Text σ e)) = GlobalSource (Text (fmap (mapTypePosition f) σ) (mapTermPosition f e))
mapGlobalPosition f (GlobalSource (Synonym σ)) = GlobalSource (Synonym (mapTypePosition f σ))
mapGlobalPosition f (GlobalSource (NewType κ σ)) = GlobalSource (NewType (mapTypePosition f κ) (mapTypePosition f σ))

positionDeclaration (DefinitionSource global) = positionGlobal global
positionDeclaration (DeclarationSource (ForwardNewtype (TypeAst p _))) = p
positionDeclaration (DeclarationSource (ForwardText (TypeScheme p _))) = p

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

synonym = Prism Synonym $ \case
  Synonym σ -> Just σ
  _ -> Nothing

newtypex = Prism (uncurry NewType) $ \case
  NewType σ τ -> Just (σ, τ)
  _ -> Nothing

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

sourceGlobal :: GlobalInfer p -> GlobalSource ()
sourceGlobal (GlobalInfer (Inline ς e)) = GlobalSource $ Inline (Just $ sourceTypeScheme ς) (TermManualSource $ sourceTermScheme False e)
sourceGlobal (GlobalInfer (Text ς e)) = GlobalSource $ Text (Just $ sourceTypeScheme ς) (TermManualSource $ sourceTermScheme False e)
sourceGlobal (GlobalInfer (Synonym σ)) = GlobalSource $ Synonym (sourceType σ)
sourceGlobal (GlobalInfer (NewType σ τ)) = GlobalSource $ NewType (sourceType σ) (sourceType τ)

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

-- nodes without dependencies are at the start of the list
order :: Semigroup p => Module (GlobalSource p) -> Either (ModuleError p) [(Path, DeclareSource p)]
order code = sortTopological view quit children globals
  where
    globals = Map.toList $ DefinitionSource <$> flatten code
    view (path, DefinitionSource _) = (True, path)
    view (path, DeclarationSource _) = (False, path)
    quit (path, global) = Left $ Cycle (positionDeclaration global) path

    children (path, global) = for (Map.toList $ depend global path) $ \(path, p) -> do
      global <- resolve p code path
      case global of
        (GlobalSource (Text (Just ς) _)) -> pure (path, DeclarationSource (ForwardText ς))
        (GlobalSource (NewType σ _)) | isType -> pure (path, DeclarationSource (ForwardNewtype σ))
        _ -> pure (path, DefinitionSource global)
      where
        isType = case global of
          DefinitionSource (GlobalSource (Inline _ _)) -> False
          DefinitionSource (GlobalSource (Text _ _)) -> False
          _ -> True

    depend :: Semigroup p => DeclareSource p -> Path -> Map Path p
    depend item (Path heading _)
      | (DefinitionSource (GlobalSource (Inline ς e))) <- item = freeTerm ς e
      | (DefinitionSource (GlobalSource (Text ς e))) <- item = freeTerm ς e
      | (DefinitionSource (GlobalSource (Synonym σ))) <- item = freeType σ
      | (DefinitionSource (GlobalSource (NewType σ τ))) <- item = freeType σ <> freeType τ
      | (DeclarationSource (ForwardNewtype σ)) <- item = freeType σ
      | (DeclarationSource (ForwardText ς)) <- item = freeType ς
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
            remove (TypeScheme _ (MonoType _)) vars = vars
            remove (TypeScheme _ (TypeForall (Bound (TypePattern _ (TypeIdentifier x) _ _) σ))) vars =
              Map.delete (Path heading x) $ remove σ vars
        freeType σ =
          Map.unionWith
            (<>)
            (scope $ extractType $ runVariables $ freeVariablesTypeSource σ)
            (extractGlobalType $ runVariables $ freeVariablesGlobalTypeSource σ)
          where
            scope = Map.mapKeysMonotonic (Path heading)
            extractType = Map.mapKeysMonotonic (\(TypeIdentifier x) -> x)
            extractGlobalType = Map.mapKeysMonotonic (\(TypeGlobalIdentifier x) -> x)
        extractTerm = Map.mapKeysMonotonic (\(TermIdentifier x) -> x)
        extractType = Map.mapKeysMonotonic (\(TypeIdentifier x) -> x)
        extractGlobalTerm = Map.mapKeysMonotonic (\(TermGlobalIdentifier x) -> x)
        extractGlobalType = Map.mapKeysMonotonic (\(TypeGlobalIdentifier x) -> x)

unorder :: [(Path, DeclareInfer p)] -> Module (GlobalInfer p)
unorder code =
  unorder' $
    code >>= \case
      (path, DefinitionInfer global) -> [(path, global)]
      _ -> []

unorder' :: [(Path, p)] -> Module p
unorder' [] = CoreModule Map.empty
unorder' (item : remaining) = insert item (unorder' remaining)
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

convertFunctionLiteral ς = case ς of
  TypeScheme () (MonoType (TypeAst () (FunctionLiteralType σ π τ))) -> polyEffect "R" (TypeAst () $ FunctionPointer σ π τ)
  TypeScheme () (TypeForall (Bound pm ς)) -> TypeScheme () $ TypeForall (Bound pm $ convertFunctionLiteral ς)
  _ -> error "not function literal"

makeExtern ::
  Path ->
  p ->
  TypeSchemeInfer ->
  TermSchemeInfer p
makeExtern path p ς = case ς of
  TypeScheme () (MonoType (TypeAst () (FunctionLiteralType σ π τ))) ->
    TermScheme p $
      TypeAbstraction
        ( Bound
            (TypePattern () (TypeIdentifier "R") (TypeAst () Region) [])
            ( TermScheme p $
                MonoTerm
                  (Term p (TermRuntime $ Extern (mangle path) (Core σ) (Core π) (Core τ)))
                  (Core $ TypeAst () (Effect (TypeAst () (FunctionPointer σ π τ)) (TypeAst () (TypeSub $ TypeVariable $ TypeIdentifier "R"))))
            )
        )
  TypeScheme () (TypeForall (Bound (TypePattern () x κ π) e)) ->
    TermScheme p (TypeAbstraction (Bound (TypePattern () x κ π) $ makeExtern path p e))
  _ -> error "not function literal"

bindMembers :: [String] -> CheckEnvironment p -> CheckEnvironment p
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

data Update e σ τ π
  = UpdateTerm e
  | UpdateSym σ
  | UpdateNewtype τ
  | UpdateNewtype' π

typeCheckModule ::
  [(Path, DeclareSource p)] ->
  StateT
    (CheckEnvironment p)
    (Either (TypeError p))
    [(Path, DeclareInfer p)]
typeCheckModule [] = pure []
typeCheckModule ((path@(Path heading _), item) : nodes) = do
  environment <- bindMembers heading <$> get
  let run f = lift $ runChecker f environment emptyState
  (item', σ) <- case item of
    DefinitionSource (GlobalSource e) -> case e of
      Inline Nothing (TermAutoSource e) -> do
        (e, σ) <- run (typeCheckGlobalAuto InlineMode e)
        pure (DefinitionInfer $ GlobalInfer $ Inline σ e, UpdateTerm $ flexible σ)
      Inline (Just σ) (TermAutoSource e) -> do
        (e, σ) <- run (typeCheckGlobalScope InlineMode e σ)
        pure (DefinitionInfer $ GlobalInfer $ Inline σ e, UpdateTerm $ flexible σ)
      Inline Nothing (TermManualSource e) -> do
        (e, σ) <- run (typeCheckGlobalSemi InlineMode e)
        pure (DefinitionInfer $ GlobalInfer $ Inline σ e, UpdateTerm $ flexible σ)
      Inline (Just σ) (TermManualSource e) -> do
        (e, σ) <- run (typeCheckGlobalManual InlineMode e σ)
        pure (DefinitionInfer $ GlobalInfer $ Inline σ e, UpdateTerm $ flexible σ)
      Text Nothing (TermAutoSource e) -> do
        (e, σ) <- run (typeCheckGlobalAuto SymbolMode e >>= syntaticCheck)
        pure (DefinitionInfer $ GlobalInfer $ Text σ e, UpdateTerm $ convertFunctionLiteral $ flexible σ)
      Text (Just σ) (TermAutoSource e) -> do
        (e, σ) <- run (typeCheckGlobalScope SymbolMode e σ)
        pure (DefinitionInfer $ GlobalInfer $ Text σ e, UpdateTerm $ convertFunctionLiteral $ flexible σ)
      Text (Just σ) (TermManualSource e) -> do
        (e, σ) <- run (typeCheckGlobalManual SymbolMode e σ >>= syntaticCheck)
        pure (DefinitionInfer $ GlobalInfer $ Text σ e, UpdateTerm $ convertFunctionLiteral $ flexible σ)
      Text Nothing (TermManualSource e) -> do
        (e, σ) <- run (typeCheckGlobalSemi SymbolMode e >>= syntaticCheck)
        pure (DefinitionInfer $ GlobalInfer $ Text σ e, UpdateTerm $ convertFunctionLiteral $ flexible σ)
      Synonym σ -> do
        (σ, _) <- run (kindCheck σ)
        pure (DefinitionInfer $ GlobalInfer $ Synonym σ, UpdateSym σ)
      NewType κ σ@(TypeAst p _) -> do
        (σ, κ) <- run $ do
          (κ', _) <- kindCheck κ
          checkPretype p (flexible κ')
          (σ, κ) <- kindCheck σ
          matchType p κ (flexible κ')
          pure (σ, κ')
        pure (DefinitionInfer $ GlobalInfer $ NewType κ σ, UpdateNewtype (flexible κ, σ))
    DeclarationSource (ForwardText ς@(TypeScheme p _)) -> do
      (ς, _) <- run (kindCheckScheme SymbolMode ς)
      pure (DeclarationInfer p $ ForwardText ς, UpdateTerm $ convertFunctionLiteral $ flexible $ ς)
    DeclarationSource (ForwardNewtype κ@(TypeAst p _)) -> do
      κ <- run $ do
        (κ, _) <- kindCheck κ
        checkPretype p (flexible κ)
        pure κ
      pure (DeclarationInfer p $ ForwardNewtype κ, UpdateNewtype' (flexible κ))
  let p = positionDeclaration item
  modify (update p σ)
  ((path, item') :) <$> typeCheckModule nodes
  where
    update p σ environment = case σ of
      UpdateTerm σ ->
        environment
          { typeGlobalEnvironment =
              Map.insert
                (TermGlobalIdentifier path)
                (TermBinding p (TypeAst () $ TypeSub Unrestricted) σ)
                $ typeGlobalEnvironment environment
          }
      UpdateSym σ ->
        environment
          { kindGlobalEnvironment =
              Map.insert
                (TypeGlobalIdentifier path)
                (LinkTypeBinding σ)
                $ kindGlobalEnvironment environment
          }
      UpdateNewtype (κ, σ) ->
        environment
          { kindGlobalEnvironment =
              Map.insert
                (TypeGlobalIdentifier path)
                (TypeBinding p κ Set.empty minBound (Named σ))
                $ kindGlobalEnvironment environment
          }
      UpdateNewtype' κ ->
        environment
          { kindGlobalEnvironment =
              Map.insertWith
                (\_ x -> x)
                (TypeGlobalIdentifier path)
                (TypeBinding p κ Set.empty minBound Unnamed)
                $ kindGlobalEnvironment environment
          }

data Reducer p = Reducer
  { reducerTerms :: Map TermGlobalIdentifier (TermSchemeInfer p),
    reducerTypes :: Map TypeGlobalIdentifier TypeInfer
  }

reduceModule ::
  Reducer p ->
  [(Path, DeclareInfer p)] ->
  [(Path, DeclareInfer p)]
reduceModule _ [] = []
reduceModule globals ((path@(Path heading _), item) : nodes) =
  (path, item') : reduceModule globals' nodes
  where
    (item', binding) = case item of
      DefinitionInfer (GlobalInfer (Inline σ e)) ->
        let e' = reduce $ applyGlobalTypes $ applyGlobalTerms e
            σ' = applyGlobalTypes σ
         in (DefinitionInfer $ GlobalInfer $ Inline σ' e', UpdateTerm e')
      DefinitionInfer (GlobalInfer (Text σ e@(TermScheme p _))) ->
        let e' = reduce $ applyGlobalTypes $ applyGlobalTerms e
            σ' = applyGlobalTypes σ
         in (DefinitionInfer $ GlobalInfer $ Text σ' e', UpdateTerm (makeExtern path p σ'))
      DefinitionInfer (GlobalInfer (Synonym σ)) ->
        let σ' = applyGlobalTypes σ
         in (DefinitionInfer $ GlobalInfer $ Synonym σ', UpdateSym σ')
      DefinitionInfer (GlobalInfer (NewType κ σ)) ->
        let κ' = applyGlobalTypes κ
            σ' = applyGlobalTypes σ
         in (DefinitionInfer $ GlobalInfer $ NewType κ' σ', UpdateSym self)
      DeclarationInfer p (ForwardNewtype κ) ->
        let κ' = applyGlobalTypes κ
         in (DeclarationInfer p $ ForwardNewtype κ', UpdateSym self)
      DeclarationInfer p (ForwardText σ) ->
        let σ' = applyGlobalTypes σ
         in (DeclarationInfer p $ ForwardText σ', UpdateTerm (makeExtern path p σ'))
    self = TypeAst () $ TypeSub $ TypeGlobalVariable $ TypeGlobalIdentifier path

    globals' = case binding of
      UpdateTerm e ->
        globals
          { reducerTerms = Map.insert (TermGlobalIdentifier path) e $ reducerTerms globals
          }
      UpdateSym σ ->
        globals
          { reducerTypes = Map.insert (TypeGlobalIdentifier path) σ $ reducerTypes globals
          }
      UpdateNewtype v -> absurd v
      UpdateNewtype' v -> absurd v
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
