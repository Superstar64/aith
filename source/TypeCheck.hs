module TypeCheck where

import Ast.Common
import Ast.Term
import Ast.Type
import Control.Monad (filterM, (<=<))
import Data.Foldable (for_)
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

freshKindVariable p μ = (TypeCore . TypeLogical) <$> (Level <$> levelCounter <$> getState >>= freshKindVariableRaw p μ)

freshSortVariable p = freshKindVariable p (TypeCore Sort)

freshSubstitutabilityKindVariable p = freshKindVariable p (TypeCore Substitutability)

freshRepresentationKindVariable p = freshKindVariable p (TypeCore Representation)

freshSizeKindVariable p = freshKindVariable p (TypeCore Size)

freshSignednessKindVariable p = freshKindVariable p (TypeCore Signedness)

checkSort p μt = do
  matchType p μt (TypeCore Sort)
  pure ()

checkKind p μt = do
  μ <- freshSubstitutabilityKindVariable p
  matchType p μt (TypeCore $ Kind $ μ)
  pure μ

checkRepresentation p μ = do
  matchType p μ (TypeCore Representation)
  pure ()

checkSize p μ = do
  matchType p μ (TypeCore Size)
  pure ()

checkSignedness p μ = do
  matchType p μ (TypeCore Signedness)
  pure ()

checkSubstitutability p μ = do
  matchType p μ (TypeCore $ Substitutability)
  pure ()

checkType p κt = do
  matchType p κt (TypeCore Type)
  pure κt

checkPretype p κt = do
  κ <- freshRepresentationKindVariable p
  matchType p κt (TypeCore (Pretype κ))
  pure κ

checkBoxed p κt = do
  matchType p κt (TypeCore Boxed)
  pure ()

checkLength p κt = do
  matchType p κt (TypeCore Length)
  pure ()

checkRegion p κt = do
  matchType p κt (TypeCore Region)
  pure ()

checkSubtypable p κt = do
  matchType p κt (TypeCore $ Subtypable)
  pure ()

freshMetaTypeVariable p = do
  freshTypeVariable p (TypeCore Type)

freshPretypeTypeVariable p = do
  s <- freshRepresentationKindVariable p
  freshTypeVariable p (TypeCore $ Pretype s)

freshBoxedTypeVariable p = do
  freshTypeVariable p (TypeCore Boxed)

freshLengthTypeVariable p = do
  freshTypeVariable p (TypeCore Length)

freshRegionTypeVariable p = do
  freshTypeVariable p $ TypeCore $ Region

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

checkUnique p σt = do
  σ <- freshBoxedTypeVariable p
  matchType p σt (TypeCore $ Unique σ)
  pure σ

checkPointer p σt = do
  σ <- freshPretypeTypeVariable p
  τ <- freshLengthTypeVariable p
  matchType p σt (TypeCore $ Pointer σ τ)
  pure (σ, τ)

checkWildcard p σt = do
  matchType p σt (TypeCore $ Wildcard)
  pure ()

checkEffect p σt = do
  σ <- freshPretypeTypeVariable p
  π <- freshRegionTypeVariable p
  matchType p σt (TypeCore $ Effect σ π)
  pure (σ, π)

checkShared p σt = do
  σ <- freshBoxedTypeVariable p
  π <- freshRegionTypeVariable p
  matchType p σt (TypeCore $ Shared σ π)
  pure (σ, π)

checkNumber p σt = do
  ρ1 <- freshSignednessKindVariable p
  ρ2 <- freshSizeKindVariable p
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

capture p lΓ = do
  let captures = variablesUsed lΓ
  for (Set.toList captures) $ \x -> do
    (TermBinding _ l _) <- fromJust <$> lookupTypeEnviroment x
    case l of
      Unrestricted -> pure ()
      Linear -> quit $ CaptureLinear p x
      Automatic σ -> constrain p Copy σ
  pure ()

augmentMetaTermPattern pm = go Linear pm
  where
    go l (TermPatternCore p (PatternVariable x σ)) = augmentVariableLinear p x l (TypeSchemeCore $ MonoType σ)
    go _ (TermPatternCore _ (PatternOfCourse pm)) = go Unrestricted pm

polyEffect name σ = TypeSchemeCore $ TypeForall (Bound (TypePattern freshVar (TypeCore Region) Set.empty []) bounded)
  where
    bounded = TypeSchemeCore $ MonoType $ TypeCore $ Effect σ (TypeCore $ TypeSub $ TypeVariable freshVar)
    freshVar = fresh (freeVariablesType σ) (TypeIdentifier name)

augmentRuntimeTermPattern pm = go pm
  where
    go (TermRuntimePatternCore p (RuntimePatternVariable x σ)) = augmentVariableLinear p x (Automatic σ) (polyEffect "R" σ)
    go (TermRuntimePatternCore _ (RuntimePatternTuple pms)) = foldr (.) id (map go pms)

checkConstraints :: p -> Set Constraint -> TypeUnify -> Core p ()
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

sortCheckPattern (KindPatternSource p x μ) = do
  μ <- case μ of
    Just μ -> do
      (μ, μΔ) <- kindCheck μ
      checkSort p μΔ
      pure μ
    Nothing -> do
      freshSortVariable p
  pure (KindPatternIntermediate p x μ, μ)

kindCheckScheme :: TypeSchemeSource p -> Core p (TypeSchemeUnify, TypeUnify)
kindCheckScheme =
  \case
    TypeSchemeSource p (MonoType σ) -> do
      (σ', κ) <- kindCheck σ
      matchType p κ (TypeCore $ Type)
      pure (TypeSchemeCore (MonoType σ'), TypeCore $ Type)
    TypeSchemeSource p (TypeForall (Bound pm σ)) -> do
      (pm', _) <- kindCheckPattern pm
      augmentTypePatternLevel pm' $ do
        (σ', κ) <- kindCheckScheme σ
        checkType p κ
        pure $ (TypeSchemeCore $ TypeForall (Bound (toTypePattern pm') σ'), TypeCore $ Type)
    TypeSchemeSource p (KindForall (Bound pm σ)) -> do
      -- todo rename to avoid shadowing
      (pm', _) <- sortCheckPattern pm
      augmentKindPatternLevel pm' $ do
        (σ', κ) <- kindCheckScheme σ
        matchType p κ (TypeCore $ Type)
        pure (TypeSchemeCore $ KindForall $ Bound (toKindPattern pm') σ', TypeCore $ Type)

kindCheckPattern :: TypePatternSource p -> Core p (TypePatternIntermediate p, TypeUnify)
kindCheckPattern (TypePatternSource p x κ c π) =
  case κ of
    Just κ -> do
      (κ, μ) <- secondM (checkKind p) =<< kindCheck κ
      checkConstraints p c κ
      (π, κ') <- unzip <$> traverse kindCheckSub π
      traverse (matchType p κ) κ'
      if Prelude.not $ null π
        then do
          checkSubtypable p μ
          pure ()
        else pure ()
      pure (TypePatternIntermediate p x κ c π, κ)
    Nothing -> do
      μ <- freshSubstitutabilityKindVariable p
      κ <- freshKindVariable p (TypeCore $ Kind μ)
      checkConstraints p c κ
      (π, κ') <- unzip <$> traverse kindCheckSub π
      traverse (matchType p κ) κ'
      if Prelude.not $ null π
        then do
          checkSubtypable p μ
          pure ()
        else pure ()
      pure (TypePatternIntermediate p x κ c π, κ)

kindCheckSub :: TypeSource p -> Core p (TypeSub, TypeUnify)
kindCheckSub σ@(TypeSource p _) = do
  (σ, κ) <- kindCheck σ
  case σ of
    TypeCore (TypeSub σ) -> pure (σ, κ)
    _ -> quit $ ExpectedSubtypable p

kindCheck :: TypeSource p -> Core p (TypeUnify, TypeUnify)
kindCheck (TypeSource p σ) = case σ of
  TypeSub (TypeVariable x) -> do
    κ <- lookupKindEnvironment x
    case κ of
      Just (TypeBinding _ κ _ _ _) -> pure (TypeCore $ TypeSub $ TypeVariable x, κ)
      Nothing -> quit $ UnknownTypeIdentifier p x
  Inline σ τ -> do
    (σ', _) <- secondM (checkType p) =<< kindCheck σ
    (τ', _) <- secondM (checkType p) =<< kindCheck τ
    pure (TypeCore $ Inline σ' τ', TypeCore $ Type)
  Poly λ -> do
    (ς, κ) <- kindCheckScheme λ
    pure (TypeCore $ Poly ς, κ)
  OfCourse σ -> do
    (σ', _) <- secondM (checkType p) =<< kindCheck σ
    pure (TypeCore $ OfCourse σ', TypeCore $ Type)
  FunctionPointer σ π τ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (TypeCore $ FunctionPointer σ' π' τ', TypeCore $ Pretype $ TypeCore $ KindRuntime $ PointerRep)
  FunctionLiteralType σ π τ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (TypeCore $ FunctionLiteralType σ' π' τ', TypeCore $ Type)
  Tuple σs -> do
    (σs, ρs) <- unzip <$> traverse (secondM (checkPretype p) <=< kindCheck) σs
    pure (TypeCore $ Tuple σs, TypeCore $ Pretype $ TypeCore $ KindRuntime $ StructRep ρs)
  Effect σ π -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    pure (TypeCore $ Effect σ' π', TypeCore $ Type)
  Unique σ -> do
    (σ', _) <- secondM (checkBoxed p) =<< kindCheck σ
    pure (TypeCore $ Unique σ', TypeCore $ Pretype $ TypeCore $ KindRuntime $ PointerRep)
  Shared σ π -> do
    (σ', _) <- secondM (checkBoxed p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    pure (TypeCore $ Shared σ' π', TypeCore $ Pretype $ TypeCore $ KindRuntime $ PointerRep)
  Pointer σ τ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (τ', _) <- secondM (checkLength p) =<< kindCheck τ
    pure (TypeCore $ Pointer σ' τ', TypeCore $ Boxed)
  Number ρ1 ρ2 -> do
    ρ1' <- fmap fst $ secondM (checkSignedness p) =<< kindCheck ρ1
    ρ2' <- fmap fst $ secondM (checkSize p) =<< kindCheck ρ2
    pure (TypeCore $ Number ρ1' ρ2', TypeCore $ Pretype $ TypeCore $ KindRuntime $ WordRep ρ2')
  Boolean -> do
    pure (TypeCore $ Boolean, TypeCore $ Pretype $ TypeCore $ KindRuntime $ WordRep $ TypeCore $ KindSize $ Byte)
  TypeSub World -> do
    pure (TypeCore $ TypeSub World, TypeCore Region)
  Wildcard -> do
    pure (TypeCore Wildcard, TypeCore Length)
  TypeLogical v -> absurd v
  Type -> do
    pure (TypeCore Type, TypeCore $ Kind $ TypeCore $ Invariant)
  Region -> pure (TypeCore Region, TypeCore $ Kind $ TypeCore $ Subtypable)
  KindRuntime PointerRep -> pure (TypeCore $ KindRuntime PointerRep, TypeCore Representation)
  KindRuntime (StructRep κs) -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< kindCheck) κs
    pure (TypeCore (KindRuntime (StructRep κs')), TypeCore Representation)
  KindRuntime (WordRep κ) -> do
    (κ', _) <- secondM (checkSize p) =<< kindCheck κ
    pure (TypeCore (KindRuntime (WordRep κ')), TypeCore Representation)
  KindSize κ -> pure (TypeCore (KindSize κ), TypeCore Size)
  KindSignedness κ -> pure (TypeCore (KindSignedness κ), TypeCore Signedness)
  Pretype κ -> do
    (κ', _) <- secondM (checkRepresentation p) =<< kindCheck κ
    pure (TypeCore $ Pretype κ', TypeCore $ Kind $ TypeCore $ Invariant)
  Boxed -> do
    pure (TypeCore $ Boxed, TypeCore $ Kind $ TypeCore $ Invariant)
  Length -> do
    pure (TypeCore $ Length, TypeCore $ Kind $ TypeCore $ Invariant)
  Kind κ -> do
    (κ, ()) <- secondM (checkSubstitutability p) =<< kindCheck κ
    pure (TypeCore (Kind κ), TypeCore Sort)
  Representation -> pure (TypeCore Representation, TypeCore Sort)
  Size -> pure (TypeCore Size, TypeCore Sort)
  Signedness -> pure (TypeCore Signedness, TypeCore Sort)
  Invariant -> pure (TypeCore Invariant, TypeCore Substitutability)
  Subtypable -> pure (TypeCore Subtypable, TypeCore Substitutability)
  Substitutability -> pure (TypeCore Substitutability, TypeCore Sort)
  Sort -> quit $ NotTypable p

instantiate p (TypeSchemeCore ς) = case ς of
  MonoType σ -> pure (σ, InstantiationCore InstantiateEmpty)
  TypeForall (Bound (TypePattern x κ c π) σ) -> do
    τ <- freshTypeVariable p κ
    for (Set.toList c) $ \c -> do
      constrain p c τ
    for π $ \π -> do
      lessThen p π τ
    (ς, θ) <- instantiate p $ substituteType τ x σ
    pure (ς, InstantiationCore $ InstantiateType τ θ)
  KindForall (Bound (KindPattern x μ) σ) -> do
    κ <- freshKindVariable p μ
    (ς, θ) <- instantiate p $ substituteType κ x σ
    pure (ς, InstantiationCore $ InstantiateKind κ θ)

expectTypeAnnotation p Nothing = quit $ ExpectedTypeAnnotation p
expectTypeAnnotation _ (Just σ) = pure σ

validateType σ = fst <$> kindCheck σ

data Checked p σ = Checked (TermUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

data CheckedScheme p σ = CheckedScheme (TermSchemeUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

typeCheckPlain :: TermSource p -> Core p (Checked p TypeUnify)
typeCheckPlain (TermSource p e) = case e of
  TypeAnnotation e σ' () -> do
    Checked e σ lΓ <- typeCheck e
    σ' <- fst <$> (expectTypeAnnotation p σ' >>= kindCheck)
    matchType p σ σ'
    pure $ Checked e σ' lΓ
  _ -> quit $ ExpectedTypeAnnotation p

typeCheck :: TermSource p -> Core p (Checked p TypeUnify)
typeCheck (TermSource p e) = case e of
  TermRuntime (Variable x ()) -> do
    mσ <- lookupTypeEnviroment x
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiate p σ
        pure $ Checked (TermCore p $ TermRuntime $ Variable x θ) τ (Use x)
      Nothing -> quit $ UnknownIdentifier p x
  GlobalVariable x () -> do
    mσ <- lookupTypeGlobalEnviroment x
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiate p σ
        -- todo useNothing here is kinda of a hack
        pure $ Checked (TermCore p $ GlobalVariable x θ) τ useNothing
      Nothing -> quit $ UnknownGlobalIdentifier p x
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
  PolyIntroduction λ -> do
    CheckedScheme eς σ lΓ <- typeCheckScheme λ
    pure $ Checked (TermCore p $ PolyIntroduction $ eς) (TypeCore $ Poly σ) lΓ
  PolyElimination e () () -> do
    Checked e ς lΓ <- typeCheckPlain e
    case ς of
      TypeCore (Poly ς') -> do
        (σ, θ) <- instantiate p ς'
        pure $ Checked (TermCore p $ PolyElimination e θ ς) σ lΓ
      _ -> quit $ ExpectedTypeAbstraction p
  TermRuntime (Alias e1 (Bound pm e2)) -> do
    (pm', τ) <- typeCheckRuntimePattern pm
    Checked e1' (τ', π) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p τ τ'
    Checked e2' (σ, π') lΓ2 <- traverse (checkEffect p) =<< augmentRuntimeTermPattern pm' (typeCheck e2)
    matchType p π π'
    pure $ Checked (TermCore p $ TermRuntime $ Alias e1' $ Bound pm' e2') (TypeCore $ Effect σ π) (lΓ1 `combine` lΓ2)
  TermRuntime (Extern sym () () ()) -> do
    σ <- freshPretypeTypeVariable p
    π <- freshRegionTypeVariable p
    τ <- freshPretypeTypeVariable p
    r <- freshRegionTypeVariable p
    pure $
      Checked
        (TermCore p $ TermRuntime $ Extern sym σ π τ)
        (TypeCore $ Effect (TypeCore $ FunctionPointer σ π τ) r)
        useNothing
  TermRuntime (FunctionApplication e1 e2 ()) -> do
    Checked e1' ((σ, π2, τ), π) lΓ1 <- traverse (firstM (checkFunctionPointer p) <=< checkEffect p) =<< typeCheck e1
    lessThen p π2 π
    Checked e2' (σ', π') lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
    matchType p π π'
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
    Checked e' (((σ, _), π2), π) lΓ <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck e
    constrain p Copy σ
    lessThen p π2 π
    pure $ Checked (TermCore p $ TermRuntime $ ReadReference e') (TypeCore $ Effect σ π) lΓ
  TermRuntime (WriteReference ep ev ()) -> do
    Checked ep (((σ, _), π2), π) lΓ1 <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
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
    ρ1 <- freshSignednessKindVariable p
    ρ2 <- freshSizeKindVariable p
    pure $
      Checked
        (TermCore p $ TermRuntime (NumberLiteral v))
        (TypeCore $ Effect (TypeCore $ Number ρ1 ρ2) π)
        useNothing
  TermRuntime (Arithmatic o e1 e2 ()) -> do
    Checked e1' ((ρ1, ρ2), π) lΓ1 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' ((ρ1', ρ2'), π') lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e2
    matchType p π π'
    matchType p ρ1 ρ1'
    matchType p ρ2 ρ2'
    pure $
      Checked
        (TermCore p $ TermRuntime $ Arithmatic o e1' e2' ρ1)
        (TypeCore $ Effect (TypeCore $ Number ρ1 ρ2) π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (Relational o e1 e2 () ()) -> do
    Checked e1' ((ρ1, ρ2), π) lΓ1 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' ((ρ1', ρ2'), π') lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e2
    matchType p π π'
    matchType p ρ1 ρ1'
    matchType p ρ2 ρ2'
    pure $
      Checked
        (TermCore p $ TermRuntime $ Relational o e1' e2' (TypeCore $ Number ρ1 ρ2) ρ1)
        (TypeCore $ Effect (TypeCore $ Boolean) π)
        (lΓ1 `combine` lΓ2)
  FunctionLiteral (Bound pm e) -> do
    (pm', σ) <- typeCheckRuntimePattern pm
    Checked e' (τ, π) lΓ <- traverse (checkEffect p) =<< augmentRuntimeTermPattern pm' (typeCheck e)
    pure $ Checked (TermCore p $ FunctionLiteral $ Bound pm' e') (TypeCore $ FunctionLiteralType σ π τ) lΓ
  Borrow eu (Bound (TypePatternSource p' α κpm c πs) (Bound pm e)) -> do
    -- Shadowing type variables is prohibited

    vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
    let α' = fresh vars α
    let pmσ = TypePatternSource p' α' κpm c πs
    pm <- pure $ convertType α' α pm
    e <- pure $ convertType α' α e
    πs <- pure $ fmap (convertType α' α) πs
    π <- case (c, πs) of
      (c, [π]) | Set.null c -> pure π
      _ -> quit $ IncorrectRegionBounds p

    (π, κ) <- kindCheckSub π

    Checked eu' (τ, π') lΓ1 <- traverse (firstM (checkUnique p) <=< checkEffect p) =<< typeCheck eu
    matchType p (TypeCore $ TypeSub π) π'

    (pmσ', κ') <- kindCheckPattern pmσ
    matchType p κ κ'
    checkRegion p κ
    σ' <- freshPretypeTypeVariable p
    augmentTypePatternLevel pmσ' $ do
      (pm', (τ', α')) <- secondM (checkShared p) =<< typeCheckRuntimePattern pm
      matchType p (TypeCore $ TypeSub $ TypeVariable α) α'
      matchType p τ τ'
      augmentRuntimeTermPattern pm' $ do
        Checked e' (σ, α'') lΓ2 <- traverse (checkEffect p) =<< typeCheck e
        matchType p σ σ'
        matchType p (TypeCore $ TypeSub $ TypeVariable α) α''
        pure $ Checked (TermCore p $ Borrow eu' (Bound (toTypePattern pmσ') (Bound pm' e'))) (TypeCore $ Effect (TypeCore $ Tuple [σ, TypeCore $ Unique τ]) π') (lΓ1 `combine` lΓ2)
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
  TermRuntime (PointerIncrement ep ei ()) -> do
    Checked ep' (((σ, ()), π2), π) lΓ1 <-
      traverse (firstM (firstM (secondM (checkWildcard p) <=< checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
    Checked ei' ((κ1, κ2), π') lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck ei
    matchType p π π'
    matchType p κ1 (TypeCore $ KindSignedness Unsigned)
    matchType p κ2 (TypeCore $ KindSize Native)
    τ <- freshLengthTypeVariable p
    pure $
      Checked
        (TermCore p $ TermRuntime $ PointerIncrement ep' ei' σ)
        (TypeCore $ Effect (TypeCore $ Shared (TypeCore $ Pointer σ τ) π2) π)
        (lΓ1 `combine` lΓ2)
  TermSugar (Not e) () -> do
    Checked e' ((), π) lΓ <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    pure $ Checked (desugar p (Not e')) (TypeCore $ Effect (TypeCore Boolean) π) lΓ
  TermSugar (And e ey) () -> do
    Checked e' ((), π) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked ey' ((), π') lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck ey
    matchType p π π'
    pure $ Checked (desugar p (And e' ey')) (TypeCore $ Effect (TypeCore Boolean) π) (lΓ1 `combine` (lΓ2 `branch` useNothing))
  TermSugar (Or e en) () -> do
    Checked e' ((), π) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked en' ((), π') lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck en
    matchType p π π'
    pure $ Checked (desugar p (And e' en')) (TypeCore $ Effect (TypeCore Boolean) π) (lΓ1 `combine` (useNothing `branch` lΓ2))
  TermSugar (Do e1 e2) () -> do
    Checked e1' (τ, π) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p τ (TypeCore $ Tuple [])
    Checked e2' (σ, π') lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
    matchType p π π'
    pure $ Checked (desugar p $ Do e1' e2') (TypeCore $ Effect σ π) (lΓ1 `combine` lΓ2)

typeCheckScheme :: TermSchemeSource p -> Core p (CheckedScheme p TypeSchemeUnify)
typeCheckScheme (TermSchemeSource p (TypeAbstraction (Bound (TypePatternSource p' α κpm c π) e))) = do
  -- Shadowing type variables is prohibited
  vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
  let α' = fresh vars α
  let pm = TypePatternSource p' α' κpm c π
  e <- pure $ convertType α' α e

  (pm', _) <- kindCheckPattern pm

  augmentTypePatternLevel pm' $ do
    CheckedScheme e' σ' lΓ <- typeCheckScheme e
    pure $
      CheckedScheme
        (TermSchemeCore p $ TypeAbstraction (Bound (toTypePattern pm') e'))
        (TypeSchemeCore $ TypeForall (Bound (toTypePattern pm') σ'))
        lΓ
typeCheckScheme (TermSchemeSource p (KindAbstraction (Bound (KindPatternSource p' β μpm) e))) = do
  -- Shadowing type variables is prohibited
  vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
  let β' = fresh vars β
  let pm = KindPatternSource p' β' μpm
  e <- pure $ convertType β' β e

  (pm', _) <- sortCheckPattern pm

  augmentKindPatternLevel pm' $ do
    CheckedScheme e' σ' lΓ <- typeCheckScheme e
    pure $
      CheckedScheme
        (TermSchemeCore p $ KindAbstraction (Bound (toKindPattern pm') e'))
        (TypeSchemeCore $ KindForall (Bound (toKindPattern pm') σ'))
        lΓ
typeCheckScheme (TermSchemeSource p (MonoTerm e)) = do
  Checked e σ lΓ <- typeCheck e
  pure $ CheckedScheme (TermSchemeCore p $ MonoTerm e) (TypeSchemeCore $ MonoType σ) lΓ

defaultType _ _ _ (Just upper) = pure $ TypeCore $ TypeSub upper
defaultType p μ _ Nothing = do
  μ'@(TypeCore μ) <- finish μ
  case μ of
    Kind (TypeCore Invariant) -> pure $ TypeCore $ Type
    Kind (TypeCore Subtypable) -> pure $ TypeCore $ Region
    Representation -> pure $ TypeCore $ KindRuntime $ PointerRep
    Size -> pure $ TypeCore $ KindSize $ Int
    Signedness -> pure $ TypeCore $ KindSignedness $ Signed
    Substitutability -> pure $ TypeCore $ Invariant
    Sort -> pure $ TypeCore $ Kind $ TypeCore $ Invariant
    Region -> pure $ TypeCore $ TypeSub World
    Length -> pure $ TypeCore $ Wildcard
    (TypeLogical v) -> absurd v
    _ -> quit $ AmbiguousType p μ'

finish :: (ZonkType u) => u TypeLogical -> Core p (u v)
finish σ = zonkType go σ
  where
    go x =
      indexTypeLogicalMap x >>= \case
        LinkTypeLogical σ -> finish σ
        UnboundTypeLogical p κ c _ upper _ -> do
          σ <- defaultType p κ c upper
          modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkTypeLogical (flexible σ)) $ typeLogicalMap state}
          pure (flexible σ)

topologicalBoundsSort :: [TypeLogical] -> Core p [TypeLogical]
topologicalBoundsSort vars = sortTopological id quit children vars
  where
    quit x = error $ "unexpected cycle: " ++ show x
    children x =
      indexTypeLogicalMap x >>= \case
        (LinkTypeLogical σ) -> do
          Set.toList <$> unsolvedTypeLogical σ
        (UnboundTypeLogical _ κ _ vars _ _) -> do
          α <- foldMap Set.toList <$> traverse unsolvedTypeLogical vars
          β <- Set.toList <$> unsolvedTypeLogical κ
          pure $ α <> β

unsolvedTypeLogical :: TypeUnify -> Core p (Set TypeLogical)
unsolvedTypeLogical σ = do
  let α = Set.toList (freeTypeLogical σ)
  α <- for α $ \x ->
    indexTypeLogicalMap x >>= \case
      LinkTypeLogical σ -> unsolvedTypeLogical σ
      UnboundTypeLogical _ _ _ _ Nothing _ -> pure $ Set.singleton x
      _ -> pure $ Set.empty
  pure $ Set.unions α

-- todo actually use levels for generalization
generalize' :: [String] -> [TypeLogical] -> (TermSchemeUnify p, TypeSchemeUnify) -> Core p (TermSchemeUnify p, TypeSchemeUnify)
generalize' _ [] (e, σ) = pure (e, σ)
generalize' [] _ _ = error "names not infinite"
generalize' (n : names) (x : xs) (e, σ) = do
  (e, σ) <- generalize' names xs (e, σ)
  indexTypeLogicalMap x >>= \case
    UnboundTypeLogical p κ c π _ _ -> do
      TypeCore μ <- reconstruct p κ
      modifyTypeLogicalMap $ \σΓ -> Map.insert x (LinkTypeLogical $ TypeCore $ TypeSub $ TypeVariable $ TypeIdentifier n) σΓ
      case μ of
        Kind _ -> do
          pure
            ( TermSchemeCore p $ TypeAbstraction (Bound (TypePattern (TypeIdentifier n) κ c π) e),
              TypeSchemeCore $ TypeForall (Bound (TypePattern (TypeIdentifier n) κ c π) σ)
            )
        Sort ->
          pure
            ( TermSchemeCore p $ KindAbstraction (Bound (KindPattern (TypeIdentifier n) κ) e),
              TypeSchemeCore $ KindForall (Bound (KindPattern (TypeIdentifier n) κ) σ)
            )
        _ -> error "generalization error"
    _ -> error "generalization error"

generalize :: Bool -> (TermUnify p, TypeUnify) -> Core p (TermSchemeInfer p, TypeSchemeInfer)
generalize inline (e@(TermCore p _), σ) = do
  vars <- unsolvedTypeLogical σ
  vars <- topologicalBoundsSort (Set.toList vars)
  vars <-
    if Prelude.not inline
      then do
        flip filterM vars $ \x -> do
          indexTypeLogicalMap x >>= \case
            UnboundTypeLogical p κ _ _ _ _ -> do
              TypeCore μ <- reconstruct p κ
              case μ of
                Kind _ -> pure True
                Sort -> pure False
                _ -> error "generalization error"
            LinkTypeLogical _ -> error "generalization error"
      else pure vars
  used <- usedVars <$> getState
  let names = filter (\x -> x `Set.notMember` used) $ temporaries' ((: []) <$> ['A' .. 'Z'])
  (e, σ) <- generalize' names vars (TermSchemeCore p $ MonoTerm e, TypeSchemeCore $ MonoType σ)
  e <- finish e
  σ <- finish σ
  pure (e, σ)

typeCheckGlobalAuto ::
  Bool ->
  TermSource p ->
  Core p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalAuto inline e = do
  Checked e σ _ <- typeCheck e
  (e, ς) <- generalize inline (e, σ)
  pure (e, ς)

typeCheckGlobalSemi ::
  TermSchemeSource p -> Core p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalSemi e = do
  CheckedScheme e ς _ <- typeCheckScheme e
  ς <- finish ς
  e <- finish e
  pure (e, ς)

typeCheckGlobalManual ::
  forall p.
  TermSchemeSource p ->
  TypeSchemeSource p ->
  Core p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalManual e ς = do
  (ς, _) <- firstM finish =<< kindCheckScheme ς
  e <- go ς e
  e <- finish e
  pure (e, ς)
  where
    go :: TypeSchemeInfer -> TermSchemeSource p -> Core p (TermSchemeUnify p)
    go (TypeSchemeCore (MonoType σ)) (TermSchemeSource p (MonoTerm e)) = do
      Checked e σ' _ <- typeCheck e
      matchType p (flexible σ) σ'
      pure (TermSchemeCore p $ MonoTerm e)
    go
      (TypeSchemeCore (TypeForall (Bound (TypePattern x κ c π) ς)))
      (TermSchemeSource _ (TypeAbstraction (Bound (TypePatternSource p x' κ' c' π') e))) = do
        ς <- pure $ flexible ς
        κ <- pure $ flexible κ
        case κ' of
          Just κ' -> do
            (κ', _) <- kindCheck κ'
            matchType p κ κ'
          Nothing -> pure ()
        -- this is a bit hacky to assume no constraints mean any constraints
        case π' of
          [] -> pure ()
          _ -> do
            (π', _) <- unzip <$> traverse kindCheck π'
            sequence $ zipWith (matchType p) (map flexible π) π'
            pure ()
        case c' of
          c' | Set.null c' || c == c' -> pure ()
          _ -> quit $ BadConstraintAnnotation p
        π <- pure $ map assumeSub π
        e' <- augmentKindEnvironment p x' κ c (Set.fromList π) minBound $ go (convertType x' x ς) e
        pure $ TermSchemeCore p $ TypeAbstraction (Bound (TypePattern x' κ c (map (TypeCore . TypeSub) π)) e')
        where
          assumeSub (TypeCore (TypeSub σ)) = σ
          assumeSub _ = error "not sub"
    go
      (TypeSchemeCore (KindForall (Bound (KindPattern x μ) ς)))
      (TermSchemeSource _ (KindAbstraction (Bound (KindPatternSource p x' μ') e))) = do
        case μ' of
          Just μ' -> do
            (μ', _) <- kindCheck μ'
            matchType p (flexible μ) μ'
          Nothing -> pure ()
        e' <- augmentKindEnvironment p x' (flexible μ) Set.empty Set.empty minBound $ go (convertType x' x ς) e
        pure $ TermSchemeCore p $ KindAbstraction $ Bound (KindPattern x' $ flexible μ) e'
    go _ (TermSchemeSource p _) = quit $ MismatchedTypeLambdas p

typeCheckGlobalScope ::
  forall p.
  TermSource p ->
  TypeSchemeSource p ->
  Core p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalScope e@(TermSource p _) ς = do
  (ς, _) <- firstM finish =<< kindCheckScheme ς
  e <- go ς
  e <- finish e
  pure (e, ς)
  where
    go :: TypeSchemeInfer -> Core p (TermSchemeUnify p)
    go (TypeSchemeCore (MonoType σ)) = do
      Checked e σ' _ <- typeCheck e
      matchType p (flexible σ) σ'
      pure (TermSchemeCore p $ MonoTerm e)
    go
      (TypeSchemeCore (TypeForall (Bound (TypePattern x κ c π) ς))) =
        do
          ς <- pure $ flexible ς
          κ <- pure $ flexible κ
          π <- pure $ map assumeSub π
          e' <- augmentKindEnvironment p x κ c (Set.fromList π) minBound $ go ς
          pure $ TermSchemeCore p $ TypeAbstraction (Bound (TypePattern x κ c (map (TypeCore . TypeSub) π)) e')
        where
          assumeSub (TypeCore (TypeSub σ)) = σ
          assumeSub _ = error "not sub"
    go
      (TypeSchemeCore (KindForall (Bound (KindPattern x μ) ς))) =
        do
          e' <- augmentKindEnvironment p x (flexible μ) Set.empty Set.empty minBound $ go ς
          pure $ TermSchemeCore p $ KindAbstraction $ Bound (KindPattern x $ flexible μ) e'

syntaticCheck :: (TermSchemeInfer p, TypeSchemeInfer) -> Core p (TermSchemeInfer p, TypeSchemeInfer)
syntaticCheck (e@(TermSchemeCore p _), ς) = do
  syntaticFunctionCheck p ς
  pure (e, ς)

syntaticFunctionCheck _ (TypeSchemeCore (MonoType (TypeCore (FunctionLiteralType _ _ _)))) = pure ()
syntaticFunctionCheck p (TypeSchemeCore (TypeForall (Bound _ ς))) = syntaticFunctionCheck p ς
syntaticFunctionCheck p _ = quit $ ExpectedFunctionLiteral p
