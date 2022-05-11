module TypeCheck where

import Ast.Common
import Ast.Kind
import Ast.Sort
import Ast.Term
import Ast.Type
import Control.Monad ((<=<))
import Data.Foldable (foldrM, for_)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Void
import Environment
import Misc.Util (firstM, secondM, sortTopological, temporaries')
import TypeCheck.Core
import TypeCheck.Unify

freshTypeVariable p κ = (TypeCore . TypeLogical) <$> (Level <$> levelCounter <$> getState >>= freshTypeVariableRaw p κ Set.empty [] Nothing)

freshKindVariable p μ = (KindCore . KindLogical) <$> (Level <$> levelCounter <$> getState >>= freshKindVariableRaw p μ)

checkKind p μt = do
  matchSort p μt Kind
  pure ()

checkRepresentation p μ = do
  matchSort p μ Representation
  pure ()

checkSize p μ = do
  matchSort p μ Size
  pure ()

checkSignedness p μ = do
  matchSort p μ Signedness
  pure ()

checkType p κt = do
  matchKind p κt (KindCore Type)
  pure κt

checkPretype p κt = do
  κ <- freshKindVariable p Representation
  matchKind p κt (KindCore (Pretype κ))
  pure κ

checkRegion p κt = do
  matchKind p κt (KindCore Region)
  pure ()

freshMetaTypeVariable p = do
  freshTypeVariable p (KindCore Type)

freshPretypeTypeVariable p = do
  s <- freshKindVariable p Representation
  freshTypeVariable p (KindCore $ Pretype s)

freshRegionTypeVariable p = do
  freshTypeVariable p $ KindCore $ Region

enforcePretypeReal p σt = do
  σ <- freshPretypeTypeVariable p
  matchType p σt σ
  pure σ

checkInline p σt = do
  σ <- freshMetaTypeVariable p
  τ <- freshMetaTypeVariable p
  matchType p σt (TypeCore (Inline σ τ))
  pure (σ, τ)

checkFunctionPointer p σt = do
  σ <- freshPretypeTypeVariable p
  π <- freshRegionTypeVariable p
  τ <- freshPretypeTypeVariable p
  matchType p σt (TypeCore $ FunctionPointer σ π τ)
  pure (σ, π, τ)

checkFunctionLiteralType p σt = do
  σ <- freshPretypeTypeVariable p
  π <- freshRegionTypeVariable p
  τ <- freshPretypeTypeVariable p
  matchType p σt (TypeCore $ FunctionLiteralType σ π τ)
  pure (σ, π, τ)

checkReference p σt = do
  π <- freshRegionTypeVariable p
  σ <- freshPretypeTypeVariable p
  matchType p σt (TypeCore $ Reference π σ)
  pure (π, σ)

checkEffect p σt = do
  σ <- freshPretypeTypeVariable p
  π <- freshRegionTypeVariable p
  matchType p σt (TypeCore $ Effect σ π)
  pure (σ, π)

checkNumber p σt = do
  ρ1 <- freshKindVariable p Signedness
  ρ2 <- freshKindVariable p Size
  matchType p σt (TypeCore $ Number ρ1 ρ2)
  pure (ρ1, ρ2)

checkBoolean p σt = do
  matchType p σt (TypeCore $ Boolean)

augmentVariableLinear p x l ς check = do
  Checked e σ lΓ <- augmentTypeEnvironment x p l ς check
  case l of
    Unrestricted -> pure ()
    Linear -> case count x lΓ of
      Single -> pure ()
      _ -> quit $ InvalidUsage p x
    Automatic σ -> case count x lΓ of
      Single -> pure ()
      _ -> constrain p Copy σ
  pure $ Checked e σ (Remove x lΓ)

augmentMetaTermPattern pm = go Linear pm
  where
    go l (TermPatternCore p (PatternVariable x σ)) = augmentVariableLinear p x l (TypeSchemeCore $ MonoType σ)
    go _ (TermPatternCore _ (PatternOfCourse pm)) = go Unrestricted pm

polyEffect name σ = TypeSchemeCore $ ImplicitForall (Bound (TypePatternCore freshVar (KindCore Region)) bounded) Set.empty []
  where
    bounded = TypeSchemeCore $ MonoType $ TypeCore $ Effect σ (TypeCore $ TypeVariable freshVar)
    freshVar = fresh (freeVariablesType σ) (TypeIdentifier name)

augmentRuntimeTermPattern pm = go pm
  where
    go (TermRuntimePatternCore p (RuntimePatternVariable x σ)) = augmentVariableLinear p x (Automatic σ) (polyEffect "R" σ)
    go (TermRuntimePatternCore _ (RuntimePatternTuple pms)) = foldr (.) id (map go pms)

capture p lΓ = do
  let captures = variablesUsed lΓ
  for (Set.toList captures) $ \x -> do
    (_, l, _) <- fromJust <$> lookupTypeEnviroment x
    case l of
      Unrestricted -> pure ()
      Linear -> quit $ CaptureLinear p x
      Automatic σ -> constrain p Copy σ
  pure ()

checkConstraints :: p -> Set Constraint -> KindUnify -> Core p ()
checkConstraints p c κ = for_ (Set.toList c) $ \c -> do
  predicateKindCheck p c κ

typeCheckMetaPattern = \case
  (TermPatternSource p (PatternVariable x σ)) -> do
    σ' <- case σ of
      Nothing -> freshMetaTypeVariable p
      Just σ -> do
        (σ', κ) <- kindCheck σ
        checkType p κ
        pure σ'
    pure (TermPatternCore p $ (PatternVariable x σ'), σ')
  (TermPatternSource p (PatternOfCourse pm)) -> do
    (pm', σ) <- typeCheckMetaPattern pm
    pure (TermPatternCore p (PatternOfCourse pm'), TypeCore (OfCourse σ))

typeCheckRuntimePattern = \case
  (TermRuntimePatternSource p (RuntimePatternVariable x σ)) -> do
    σ' <- case σ of
      Nothing -> freshPretypeTypeVariable p
      Just σ -> do
        σ' <- fst <$> kindCheck σ
        enforcePretypeReal p σ'
    pure ((TermRuntimePatternCore p $ RuntimePatternVariable x σ', σ'))
  (TermRuntimePatternSource p (RuntimePatternTuple pms)) -> do
    (pms, σs) <- unzip <$> traverse typeCheckRuntimePattern pms
    pure ((TermRuntimePatternCore p $ RuntimePatternTuple pms, TypeCore $ Tuple σs))

sortCheckPattern :: Pattern KindIdentifier Sort p -> Core p (Pattern KindIdentifier Sort p, Sort)
sortCheckPattern (Pattern p x μ) = pure (Pattern p x μ, μ)

sortCheck :: KindSource p -> Core p (KindUnify, Sort)
sortCheck (KindSource p κ) = case κ of
  KindVariable x -> do
    μ <- lookupSortEnvironment x
    case μ of
      Just (_, μ, _) -> pure (KindCore $ KindVariable x, μ)
      Nothing -> quit $ UnknownKindIdentifier p x
  Type -> do
    pure (KindCore $ Type, Kind)
  Region -> pure (KindCore Region, Kind)
  KindRuntime PointerRep -> pure (KindCore $ KindRuntime PointerRep, Representation)
  KindRuntime (StructRep κs) -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< sortCheck) κs
    pure (KindCore (KindRuntime (StructRep κs')), Representation)
  KindRuntime (WordRep κ) -> do
    (κ', _) <- secondM (checkSize p) =<< sortCheck κ
    pure (KindCore (KindRuntime (WordRep κ')), Representation)
  KindSize κ -> pure (KindCore (KindSize κ), Size)
  KindSignedness κ -> pure (KindCore (KindSignedness κ), Signedness)
  Pretype κ -> do
    (κ', _) <- secondM (checkRepresentation p) =<< sortCheck κ
    pure (KindCore $ Pretype κ', Kind)
  KindLogical v -> absurd v

kindCheckScheme :: TypeSchemeSource p -> Core p (TypeSchemeUnify, KindUnify)
kindCheckScheme =
  \case
    TypeSchemeSource p (MonoType σ) -> do
      (σ', κ) <- kindCheck σ
      matchKind p κ (KindCore $ Type)
      pure (TypeSchemeCore (MonoType σ'), KindCore $ Type)
    TypeSchemeSource p (ImplicitForall (Bound pm σ) c π) -> do
      (pm', κ2) <- kindCheckPattern pm
      checkConstraints p c κ2
      (π, κ2') <- unzip <$> traverse kindCheck π
      traverse (matchKind p κ2) κ2'
      (σ', κ) <- augmentTypePatternBottom pm' $ kindCheckScheme σ
      matchKind p κ (KindCore $ Type)
      pure $ (TypeSchemeCore $ ImplicitForall (Bound (toTypePattern pm') σ') c π, KindCore $ Type)
    TypeSchemeSource p (ImplicitKindForall (Bound pm σ)) -> do
      (pm', _) <- sortCheckPattern pm
      augmentKindPatternLevel pm' $ do
        enterLevel
        (σ', κ) <- kindCheckScheme σ
        leaveLevel
        matchKind p κ (KindCore $ Type)
        pure (TypeSchemeCore $ ImplicitKindForall $ Bound (toKindPattern pm') σ', KindCore $ Type)

kindCheckPattern :: Pattern TypeIdentifier (KindAuto p) p -> Core p (Pattern TypeIdentifier KindUnify p, KindUnify)
kindCheckPattern (Pattern p x κ) = case κ of
  Just κ -> do
    (κ', μ) <- sortCheck κ
    matchSort p μ Kind
    pure (Pattern p x κ', κ')
  Nothing -> do
    κ <- freshKindVariable p Kind
    pure (Pattern p x κ, κ)

kindCheck :: TypeSource p -> Core p ((Type vσ KindLogical), KindUnify)
kindCheck (TypeSource p σ) = case σ of
  TypeVariable x -> do
    κ <- lookupKindEnvironment x
    case κ of
      Just (_, κ, _, _, _) -> pure (TypeCore (TypeVariable x), κ)
      Nothing -> quit $ UnknownTypeIdentifier p x
  Inline σ τ -> do
    (σ', _) <- secondM (checkType p) =<< kindCheck σ
    (τ', _) <- secondM (checkType p) =<< kindCheck τ
    pure (TypeCore $ Inline σ' τ', KindCore $ Type)
  Forall (Bound pm σ) c π -> do
    (pm', κ2) <- kindCheckPattern pm
    (π, κ2') <- unzip <$> traverse kindCheck π
    traverse (matchKind p κ2) κ2'
    checkConstraints p c κ2
    (σ', κ) <- augmentTypePatternBottom pm' $ kindCheck σ
    pure $ (TypeCore $ Forall (Bound (toTypePattern pm') σ') c π, κ)
  OfCourse σ -> do
    (σ', _) <- secondM (checkType p) =<< kindCheck σ
    pure (TypeCore $ OfCourse σ', KindCore $ Type)
  FunctionPointer σ π τ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (TypeCore $ FunctionPointer σ' π' τ', KindCore $ Pretype $ KindCore $ KindRuntime $ PointerRep)
  FunctionLiteralType σ π τ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (TypeCore $ FunctionLiteralType σ' π' τ', KindCore $ Type)
  Tuple σs -> do
    (σs, ρs) <- unzip <$> traverse (secondM (checkPretype p) <=< kindCheck) σs
    pure (TypeCore $ Tuple σs, KindCore $ Pretype $ KindCore $ KindRuntime $ StructRep ρs)
  Effect σ π -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    pure (TypeCore $ Effect σ' π', KindCore $ Type)
  Reference π σ -> do
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    pure (TypeCore $ Reference π' σ', KindCore $ Pretype $ KindCore $ KindRuntime $ PointerRep)
  Number ρ1 ρ2 -> do
    ρ1' <- case ρ1 of
      Nothing -> freshKindVariable p Signedness
      Just ρ1 -> fmap fst $ secondM (checkSignedness p) =<< sortCheck ρ1
    ρ2' <- case ρ2 of
      Nothing -> freshKindVariable p Size
      Just ρ2 -> fmap fst $ secondM (checkSize p) =<< sortCheck ρ2
    pure (TypeCore $ Number ρ1' ρ2', KindCore $ Pretype $ KindCore $ KindRuntime $ WordRep ρ2')
  Boolean -> do
    pure (TypeCore $ Boolean, KindCore $ Pretype $ KindCore $ KindRuntime $ WordRep $ KindCore $ KindSize $ Byte)
  TypeLogical v -> absurd v

instantiate p (TypeSchemeCore ς) = case ς of
  MonoType σ -> pure (σ, InstantiationCore InstantiateEmpty)
  ImplicitForall (Bound (TypePatternCore x κ) σ) c π -> do
    τ <- freshTypeVariable p κ
    -- todo constrain with π
    for (Set.toList c) $ \c -> do
      constrain p c τ
    for π $ \π -> do
      lessThen p π τ
    (ς, θ) <- instantiate p $ substituteType τ x σ
    pure (ς, InstantiationCore $ InstantiateType τ θ)
  ImplicitKindForall (Bound (KindPatternCore x μ) σ) -> do
    κ <- freshKindVariable p μ
    (ς, θ) <- instantiate p $ substituteKind κ x σ
    pure (ς, InstantiationCore $ InstantiateKind κ θ)

expectTypeAnnotation p Nothing = quit $ ExpectedTypeAnnotation p
expectTypeAnnotation _ (Just σ) = pure σ

validateType σ = fst <$> kindCheck σ

validateStrictlyVariables π = Set.fromList <$> traverse get π
  where
    get (TypeSource _ (TypeVariable x)) = pure x
    get (TypeSource p _) = quit $ ExpectedTypeVariable p

data Checked p σ = Checked (TermUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

typeCheckPlain :: TermSource p -> Core p (Checked p (Type vσ KindLogical))
typeCheckPlain (TermSource p e) = case e of
  TypeAnnotation e σ' () -> do
    Checked e σ lΓ <- typeCheck e
    σ' <- fst <$> (expectTypeAnnotation p σ' >>= kindCheck)
    let σ'' = flexibleType σ'
    matchType p σ σ''
    pure $ Checked e σ'' lΓ
  _ -> quit $ ExpectedTypeAnnotation p

typeCheck :: TermSource p -> Core p (Checked p TypeUnify)
typeCheck (TermSource p e) = case e of
  TermRuntime (Variable x ()) -> do
    mσ <- lookupTypeEnviroment x
    case mσ of
      Just (_, _, σ) -> do
        (τ, θ) <- instantiate p σ
        pure $ Checked (TermCore p $ TermRuntime $ Variable x θ) τ (Use x)
      Nothing -> quit $ UnknownIdentifier p x
  InlineAbstraction (Bound pm e) -> do
    (pm', σ) <- typeCheckMetaPattern pm
    Checked e' τ lΓ <- augmentMetaTermPattern pm' (typeCheck e)
    pure $ Checked (TermCore p $ InlineAbstraction $ Bound pm' e') (TypeCore $ Inline σ τ) lΓ
  InlineApplication e1 e2 () -> do
    Checked e1' (σ, τ) lΓ1 <- traverse (checkInline p) =<< typeCheck e1
    Checked e2' σ' lΓ2 <- typeCheck e2
    matchType p σ σ'
    pure $ Checked (TermCore p $ InlineApplication e1' e2' σ) τ (lΓ1 `combine` lΓ2)
  Bind e1 (Bound pm e2) -> do
    Checked e1' τ lΓ1 <- typeCheck e1
    (pm', τ') <- typeCheckMetaPattern pm
    matchType p τ τ'
    Checked e2' σ lΓ2 <- augmentMetaTermPattern pm' $ typeCheck e2
    pure $ Checked (TermCore p $ Bind e1' $ Bound pm' e2') σ (lΓ1 `combine` lΓ2)
  OfCourseIntroduction e -> do
    Checked e' σ lΓ <- typeCheck e
    capture p lΓ
    pure $ Checked (TermCore p $ OfCourseIntroduction e') (TypeCore $ OfCourse $ σ) lΓ
  TypeAbstraction (Bound (Pattern p' α κpm) e) c π -> do
    -- Shadowing type variables is prohibited
    vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
    let α' = fresh vars α
    let pm = Pattern p' α' κpm
    e <- pure $ convertType α' α e
    π <- pure $ map (convertType α' α) π

    (pm', κ) <- kindCheckPattern pm
    checkConstraints p c κ
    π <- traverse (expectTypeAnnotation p) π
    πx <- validateStrictlyVariables π
    (π, κ') <- unzip <$> traverse kindCheck π
    traverse (matchKind p κ) κ'
    augmentTypePatternLevel pm' c πx $ do
      enterLevel
      Checked e' σ' lΓ <- typeCheck e
      leaveLevel
      pure $
        Checked
          (TermCore p $ TypeAbstraction (Bound (toTypePattern pm') e') c π)
          (TypeCore $ Forall (Bound (toTypePattern pm') σ') c π)
          lΓ
  TypeApplication e τ () -> do
    -- todo constrain with π
    (τ, κ) <- case τ of
      Just τ -> kindCheck τ
      Nothing -> do
        κ <- freshKindVariable p Kind
        σ <- freshTypeVariable p κ
        pure (σ, κ)

    Checked e ς lΓ <- typeCheckPlain e
    case ς of
      (TypeCore (Forall (Bound (TypePatternCore α κ') σ) c π)) -> do
        for π $ \π -> lessThen p π τ
        for (Set.toList c) $ \c -> constrain p c τ
        matchKind p κ κ'
        pure $ Checked (TermCore p $ TypeApplication e τ ς) (substituteType τ α σ) lΓ
      _ -> quit $ ExpectedTypeAbstraction p
  TermRuntime (Alias e1 (Bound pm e2)) -> do
    (pm', τ) <- typeCheckRuntimePattern pm
    Checked e1' (τ', π) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p τ τ'
    Checked e2' (σ, π') lΓ2 <- traverse (checkEffect p) =<< augmentRuntimeTermPattern pm' (typeCheck e2)
    matchType p π π'
    pure $ Checked (TermCore p $ TermRuntime $ Alias e1' $ Bound pm' e2') (TypeCore $ Effect σ π) (lΓ1 `combine` lΓ2)
  TermRuntime (Extern sym σ π τ) -> do
    σ' <- case σ of
      Nothing -> freshPretypeTypeVariable p
      Just σ -> fmap fst $ secondM (checkPretype p) =<< kindCheck σ
    π' <- case π of
      Nothing -> freshRegionTypeVariable p
      Just π -> fmap fst $ secondM (checkRegion p) =<< kindCheck π
    τ' <- case τ of
      Nothing -> freshPretypeTypeVariable p
      Just τ -> fmap fst $ secondM (checkPretype p) =<< kindCheck τ
    r <- freshRegionTypeVariable p
    pure $
      Checked
        (TermCore p $ TermRuntime $ Extern sym σ' π' τ')
        (TypeCore $ Effect (TypeCore $ FunctionPointer σ' π' τ') r)
        useNothing
  TermRuntime (FunctionApplication e1 e2 ()) -> do
    Checked e1' ((σ, π, τ), π') lΓ1 <- traverse (firstM (checkFunctionPointer p) <=< checkEffect p) =<< typeCheck e1
    matchType p π π'
    Checked e2' (σ', π'') lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
    matchType p π π''
    matchType p σ σ'
    pure $ Checked (TermCore p $ TermRuntime $ FunctionApplication e1' e2' σ) (TypeCore $ Effect τ π) (lΓ1 `combine` lΓ2)
  TermRuntime (TupleIntroduction es) -> do
    checked <- traverse (traverse (checkEffect p) <=< typeCheck) es
    π <- freshRegionTypeVariable p

    (es, σs, lΓs) <- fmap unzip3 $
      for checked $ \(Checked e (σ, π') lΓ) -> do
        matchType p π π'
        σ <- enforcePretypeReal p σ
        pure (e, σ, lΓ)

    pure $
      Checked
        (TermCore p $ TermRuntime $ TupleIntroduction es)
        (TypeCore $ Effect (TypeCore $ Tuple σs) π)
        (combineAll lΓs)
  TermRuntime (ReadReference e) -> do
    Checked e' ((π2, σ), π) lΓ <- traverse (firstM (checkReference p) <=< checkEffect p) =<< typeCheck e
    constrain p Copy σ
    lessThen p π2 π
    pure $ Checked (TermCore p $ TermRuntime $ ReadReference e') (TypeCore $ Effect σ π) lΓ
  TermRuntime (WriteReference ep ev ()) -> do
    Checked ep ((π2, σ), π) lΓ1 <- traverse (firstM (checkReference p) <=< checkEffect p) =<< typeCheck ep
    Checked ev (σ', π') lΓ2 <- traverse (checkEffect p) =<< typeCheck ev
    matchType p σ σ'
    matchType p π π'
    lessThen p π2 π
    constrain p Copy σ
    pure $
      Checked
        (TermCore p $ TermRuntime $ WriteReference ep ev σ)
        (TypeCore $ Effect (TypeCore $ Tuple []) π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (NumberLiteral v) -> do
    π <- freshRegionTypeVariable p
    ρ1 <- freshKindVariable p Signedness
    ρ2 <- freshKindVariable p Size
    pure $
      Checked
        (TermCore p $ TermRuntime (NumberLiteral v))
        (TypeCore $ Effect (TypeCore $ Number ρ1 ρ2) π)
        useNothing
  TermRuntime (Arithmatic o e1 e2 ()) -> do
    Checked e1' ((ρ1, ρ2), π) lΓ1 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' ((ρ1', ρ2'), π') lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e2
    matchType p π π'
    matchKind p ρ1 ρ1'
    matchKind p ρ2 ρ2'
    pure $
      Checked
        (TermCore p $ TermRuntime $ Arithmatic o e1' e2' ρ1)
        (TypeCore $ Effect (TypeCore $ Number ρ1 ρ2) π)
        (lΓ1 `combine` lΓ2)
  FunctionLiteral (Bound pm e) -> do
    (pm', σ) <- typeCheckRuntimePattern pm
    Checked e' (τ, π) lΓ <- traverse (checkEffect p) =<< augmentRuntimeTermPattern pm' (typeCheck e)
    pure $ Checked (TermCore p $ FunctionLiteral $ Bound pm' e') (TypeCore $ FunctionLiteralType σ π τ) lΓ
  TypeAnnotation e σ' () -> do
    Checked e σ lΓ <- typeCheck e
    σ' <- expectTypeAnnotation p σ'
    σ' <- fst <$> kindCheck σ'
    matchType p σ σ'
    pure $ Checked e σ lΓ
  PretypeAnnotation e σ' () -> do
    Checked e τ lΓ <- typeCheck e
    (σ, _) <- checkEffect p τ
    σ' <- expectTypeAnnotation p σ'
    σ' <- fst <$> kindCheck σ'
    matchType p σ σ'
    pure $ Checked e τ lΓ
  TermRuntime (BooleanLiteral b) -> do
    π <- freshRegionTypeVariable p
    pure $ Checked (TermCore p $ TermRuntime $ BooleanLiteral b) (TypeCore $ Effect (TypeCore Boolean) π) useNothing
  TermRuntime (If eb et ef) -> do
    Checked eb' ((), π) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck eb
    Checked et' (σ, π') lΓ2 <- traverse (checkEffect p) =<< typeCheck et
    Checked ef' (σ', π'') lΓ3 <- traverse (checkEffect p) =<< typeCheck ef
    matchType p π π'
    matchType p π π''
    matchType p σ σ'
    pure $ Checked (TermCore p $ TermRuntime $ If eb' et' ef') (TypeCore $ Effect σ π) (lΓ1 `combine` (lΓ2 `branch` lΓ3))

topologicalBoundsSort :: [TypeLogical] -> Core p [TypeLogical]
topologicalBoundsSort vars = sortTopological id quit children vars
  where
    quit x = error $ "unexpected cycle: " ++ show x
    children x =
      indexTypeLogicalMap x >>= \case
        (LinkTypeLogical σ) -> do
          pure $ Set.toList $ freeTypeLogical σ
        (UnboundTypeLogical _ _ _ vars _ _) -> do
          pure $ vars >>= (Set.toList . freeTypeLogical)

defaultKind Kind = KindCore $ Type
defaultKind Representation = KindCore $ KindRuntime $ PointerRep
defaultKind Size = KindCore $ KindSize $ Int
defaultKind Signedness = KindCore $ KindSignedness $ Signed

finishType :: (ZonkType u) => u TypeLogical KindLogical -> Core p (u v KindLogical)
finishType σ = zonkType go σ
  where
    go x =
      indexTypeLogicalMap x >>= \case
        LinkTypeLogical σ -> finishType σ
        UnboundTypeLogical _ _ _ _ (Just upper) _ -> pure $ TypeCore $ TypeVariable upper
        UnboundTypeLogical p _ _ _ Nothing _ -> quit $ AmbiguousType p

finishKind :: (ZonkKind u) => u KindLogical -> Core p (u v)
finishKind κ = zonkKind go κ
  where
    go x =
      indexKindLogicalMap x >>= \case
        LinkKindLogical κ -> finishKind κ
        UnboundKindLogical _ μ _ -> pure $ defaultKind μ

finish :: (ZonkType u, ZonkKind (u vσ')) => u TypeLogical KindLogical -> Core p (u vσ' v')
finish e = do
  e <- finishType e
  e <- finishKind e
  pure e

unsolvedTypeLogical :: (ZonkType u) => u TypeLogical vκ -> Core p (Set TypeLogical)
unsolvedTypeLogical σ = do
  let α = Set.toList (freeTypeLogical σ)
  α <- for α $ \x ->
    indexTypeLogicalMap x >>= \case
      LinkTypeLogical σ -> unsolvedTypeLogical σ
      _ -> pure $ Set.singleton x
  pure $ Set.unions α

unsolvedKindLogical :: ZonkKind u => u KindLogical -> Core p (Set KindLogical)
unsolvedKindLogical σ = do
  let α = Set.toList (freeKindLogical σ)
  α <- for α $ \x ->
    indexKindLogicalMap x >>= \case
      LinkKindLogical σ -> unsolvedKindLogical σ
      _ -> pure $ Set.singleton x
  pure $ Set.unions α

generalize inline (e@(TermCore p _), σ) = do
  used <- usedVars <$> getState
  let typeNames = filter (`Set.notMember` used) $ temporaries' $ (: []) <$> ['A' .. 'M']
  let kindNames = filter (`Set.notMember` used) $ temporaries' $ (: []) <$> ['N' .. 'Z']

  e <- pure $ TermSchemeCore p $ MonoTerm e
  σ <- pure $ TypeSchemeCore $ MonoType σ

  α <- Set.toList <$> unsolvedTypeLogical σ
  α <- topologicalBoundsSort α
  -- todo actually use levels for generalization
  (e, σ) <- foldrMFlip (e, σ) (zip α typeNames) $ \(α, name') (e, σ) ->
    indexTypeLogicalMap α >>= \case
      (UnboundTypeLogical p κ c lower Nothing _) -> do
        let name = TypeIdentifier name'
        modifyState $ \state ->
          state
            { typeLogicalMap = Map.insert α (LinkTypeLogical (TypeCore $ TypeVariable $ name)) $ typeLogicalMap $ state
            }
        pure
          ( TermSchemeCore p $ ImplicitTypeAbstraction (Bound (TypePatternCore name κ) e) c lower,
            TypeSchemeCore $ ImplicitForall (Bound (TypePatternCore name κ) σ) c lower
          )
      _ -> error "unhandled type logical"

  e <- finishType e
  σ <- finishType σ

  κα <- if inline then Set.toList <$> unsolvedKindLogical σ else pure []

  (e, σ) <- foldrMFlip (e, σ) (zip κα kindNames) $ \(α, name') (e, σ) ->
    indexKindLogicalMap α >>= \case
      (UnboundKindLogical p μ _) -> do
        let name = KindIdentifier name'
        modifyState $ \state ->
          state
            { kindLogicalMap = Map.insert α (LinkKindLogical (KindCore $ KindVariable $ name)) $ kindLogicalMap $ state
            }
        pure
          ( TermSchemeCore p $ ImplicitKindAbstraction (Bound (KindPatternCore name μ) e),
            TypeSchemeCore $ ImplicitKindForall (Bound (KindPatternCore name μ) σ)
          )
      _ -> error "unhandled kind logical"

  e <- finishKind e
  σ <- finishKind σ

  pure (e, σ)
  where
    foldrMFlip a b f = foldrM f a b

-- todo readd ambigous types check
typeCheckGlobalAuto ::
  Bool ->
  TermSource p ->
  Core p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalAuto inline e = do
  enterLevel
  Checked e σ _ <- typeCheck e
  leaveLevel
  (e, ς) <- generalize inline (e, σ)
  pure (e, ς)

typeCheckGlobalManual ::
  forall p.
  TermSchemeSource p ->
  TypeSchemeAuto p ->
  Core p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalManual e@(TermSchemeSource p _) ς = case ς of
  Nothing -> error "todo handle type lambdas without annotation"
  Just ς -> do
    enterLevel
    (ς, _) <- kindCheckScheme ς
    zonkKind (const $ quit $ ExpectedFullAnnotation p) ς
    e <- go ς e
    e <- finish e
    ς <- finish ς
    pure (e, ς)
  where
    go (TypeSchemeCore (MonoType σ)) (TermSchemeSource p (MonoTerm e)) = do
      Checked e σ' _ <- typeCheck e
      matchType p σ σ'
      leaveLevel
      pure (TermSchemeCore p $ MonoTerm e)
    go
      (TypeSchemeCore (ImplicitForall (Bound (TypePatternCore x κ) ς) c π))
      (TermSchemeSource _ (ImplicitTypeAbstraction (Bound (Pattern p x' _) e) _ _)) = do
        -- todo handle constrains and bounds
        pure (TermSchemeCore p)
          <*> ( pure ImplicitTypeAbstraction
                  <*> ( pure (Bound (TypePatternCore x' κ))
                          <*> (augmentKindEnvironment x' p κ c (strictlyVariables π) minBound $ go (convertType x' x ς) e)
                      )
                  <*> pure c
                  <*> pure π
              )
    go
      (TypeSchemeCore (ImplicitKindForall (Bound (KindPatternCore x μ) ς)))
      (TermSchemeSource _ (ImplicitKindAbstraction (Bound (Pattern p x' _) e))) = do
        pure (TermSchemeCore p)
          <*> ( pure ImplicitKindAbstraction
                  <*> ( pure (Bound (KindPatternCore x' μ))
                          <*> (augmentSortEnvironment x' p μ minBound $ go (convertKind x' x ς) e)
                      )
              )
    go _ (TermSchemeSource p _) = quit $ MismatchedTypeLambdas p

syntaticCheck :: (TermSchemeInfer p, TypeSchemeInfer) -> Core p (TermSchemeInfer p, TypeSchemeInfer)
syntaticCheck (e@(TermSchemeCore p _), ς) = do
  syntaticFunctionCheck p ς
  pure (e, ς)

syntaticFunctionCheck _ (TypeSchemeCore (MonoType (TypeCore (FunctionLiteralType _ _ _)))) = pure ()
syntaticFunctionCheck p (TypeSchemeCore (ImplicitForall (Bound _ ς) _ _)) = syntaticFunctionCheck p ς
syntaticFunctionCheck p _ = quit $ ExpectedFunctionLiteral p
