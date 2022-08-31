module TypeCheck where

import Ast.Common
import Ast.Term
import Ast.Type
import Control.Monad (filterM, (<=<))
import Data.Bifunctor (second)
import Data.Functor.Identity (runIdentity)
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

data Mode = InlineMode | SymbolMode

freshTypeVariable p κ = (TypeCore . TypeLogical) <$> (Level <$> levelCounter <$> getState >>= freshTypeVariableRaw p κ [] Nothing)

freshRepresentationKindVariable p = freshTypeVariable p (TypeCore Representation)

freshSizeKindVariable p = freshTypeVariable p (TypeCore Size)

freshSignednessKindVariable p = freshTypeVariable p (TypeCore Signedness)

check' error f p σ = case f σ of
  Just σ -> pure σ
  Nothing -> quit $ error p σ

checkKind' = check' ExpectedKind $ \case
  (TypeCore (Top (Kind σ τ))) -> Just (σ, τ)
  _ -> Nothing

checkRepresentation' = check' ExpectedRepresentation $ \case
  (TypeCore Representation) -> Just ()
  _ -> Nothing

checkMultiplicity' = check' ExpectedMultiplicity $ \case
  (TypeCore Multiplicity) -> Just ()
  _ -> Nothing

checkSize' = check' ExpectedSize $ \case
  (TypeCore Size) -> Just ()
  _ -> Nothing

checkSignedness' = check' ExpectedSignedness $ \case
  (TypeCore Signedness) -> Just ()
  _ -> Nothing

checkType' = check' ExpectedType $ \case
  (TypeCore Type) -> Just ()
  _ -> Nothing

checkPretype' = check' ExpectedPretype $ \case
  (TypeCore (Pretype κ τ)) -> Just (κ, τ)
  _ -> Nothing

checkPretype p σ = do
  κ <- freshRepresentationKindVariable p
  τ <- freshMultiplicityKindVariable p
  matchType p σ (TypeCore $ Pretype κ τ)
  pure (κ, τ)

checkBoxed' = check' ExpectedBoxed $ \case
  (TypeCore Boxed) -> Just ()
  _ -> Nothing

checkRegion' = check' ExpectedRegion $ \case
  (TypeCore Region) -> Just ()
  _ -> Nothing

checkSubtypable' = check' ExpectedSubtypable' $ \case
  (TypeCore (Top Subtypable)) -> Just ()
  _ -> Nothing

freshMetaTypeVariable p = do
  freshTypeVariable p (TypeCore Type)

freshMultiplicityKindVariable p = do
  freshTypeVariable p (TypeCore Multiplicity)

freshPretypeTypeVariable p = do
  s <- freshRepresentationKindVariable p
  τ <- freshMultiplicityKindVariable p
  freshTypeVariable p (TypeCore $ Pretype s τ)

freshBoxedTypeVariable p = do
  freshTypeVariable p (TypeCore Boxed)

freshRegionTypeVariable p = do
  freshTypeVariable p $ TypeCore $ Region

checkInline p σt = do
  σ <- freshMetaTypeVariable p
  π <- freshMultiplicityKindVariable p
  τ <- freshMetaTypeVariable p
  matchType p σt (TypeCore (Inline σ π τ))
  pure (σ, π, τ)

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
  matchType p σt (TypeCore $ Pointer σ)
  pure (σ)

checkArray p σt = do
  σ <- freshPretypeTypeVariable p
  matchType p σt (TypeCore $ Array σ)
  pure (σ)

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
  case count x lΓ of
    Single -> pure ()
    _ -> matchType p l (TypeCore $ TypeSub Unrestricted)
  pure $ Checked e σ (Remove x lΓ)

capture p base lΓ = do
  let captures = variablesUsed lΓ
  for (Set.toList captures) $ \x -> do
    (TermBinding _ l _) <- fromJust <$> lookupTypeEnviroment x
    lessThen p base l
    pure ()
  pure ()

requireUnrestricted p σ = do
  κ <- reconstruct p σ
  (_, l) <- checkPretype p κ
  matchType p l (TypeCore $ TypeSub Unrestricted)
  pure ()

makeTuple p σs = do
  π <- freshMultiplicityKindVariable p
  for σs $ \σ -> do
    κ <- reconstruct p σ
    (_, π') <- checkPretype p κ
    lessThen p π π'
  pure $ TypeCore $ Tuple σs π

augmentMetaTermPattern l (TermPatternCore p (PatternVariable x σ)) = augmentVariableLinear p x l (TypeSchemeCore $ MonoType σ)

polyEffect name σ = TypeSchemeCore $ TypeForall (Bound (TypePattern freshVar (TypeCore Region) []) bounded)
  where
    bounded = TypeSchemeCore $ MonoType $ TypeCore $ Effect σ (TypeCore $ TypeSub $ TypeVariable freshVar)
    freshVar = fresh (freeVariablesType σ) (TypeIdentifier name)

augmentRuntimeTermPattern pm = go pm
  where
    go (TermRuntimePatternCore p (RuntimePatternVariable x σ)) = \e -> do
      κ <- reconstruct p σ
      (_, l) <- checkPretype p κ
      augmentVariableLinear p x l (polyEffect "R" σ) e
    go (TermRuntimePatternCore _ (RuntimePatternTuple pms)) = foldr (.) id (map go pms)

typeCheckMetaPattern = \case
  (TermPatternSource p (PatternVariable x σ)) -> do
    σ' <- case σ of
      Nothing -> freshMetaTypeVariable p
      Just σ -> do
        (σ', _) <- secondM (checkType' p) =<< kindCheck σ
        pure (flexible σ')
    pure (TermPatternCore p $ (PatternVariable x σ'), σ')

typeCheckRuntimePattern = \case
  (TermRuntimePatternSource p (RuntimePatternVariable x σ)) -> do
    σ' <- case σ of
      Nothing -> freshPretypeTypeVariable p
      Just σ -> do
        (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
        pure (flexible σ')
    pure ((TermRuntimePatternCore p $ RuntimePatternVariable x σ', σ'))
  (TermRuntimePatternSource p (RuntimePatternTuple pms)) -> do
    (pms, σs) <- unzip <$> traverse typeCheckRuntimePattern pms
    τ <- makeTuple p σs
    pure ((TermRuntimePatternCore p $ RuntimePatternTuple pms, τ))

kindCheckScheme :: Mode -> TypeSchemeSource p -> Core p (TypeSchemeInfer, TypeInfer)
kindCheckScheme mode =
  \case
    TypeSchemeSource p (MonoType σ) -> do
      (σ', _) <- secondM (checkType' p) =<< kindCheck σ
      pure (TypeSchemeCore (MonoType σ'), TypeCore $ Type)
    TypeSchemeSource p (TypeForall (Bound pm σ)) -> do
      (pm', _) <- kindCheckPattern mode pm
      augmentTypePatternLevel pm' $ do
        (σ', _) <- secondM (checkType' p) =<< kindCheckScheme mode σ
        pure $ (TypeSchemeCore $ TypeForall (Bound (toTypePattern pm') σ'), TypeCore $ Type)

kindCheckPattern :: Mode -> TypePatternSource p -> Core p (TypePatternIntermediate p, TypeInfer)
kindCheckPattern mode (TypePatternSource p x κ π) = do
  (κ, (μ, σ)) <- secondM (checkKind' p) =<< kindCheck κ
  case mode of
    SymbolMode -> matchType p (flexible σ) (TypeCore $ Top Transparent)
    InlineMode -> pure ()
  (π, κ') <- unzip <$> traverse kindCheckSub π
  traverse (matchType p (flexible κ)) (map flexible κ')
  if Prelude.not $ null π
    then do
      checkSubtypable' p μ
      pure ()
    else pure ()
  pure (TypePatternIntermediate p x κ π, κ)

kindCheckSub :: TypeSource p -> Core p (TypeSub, TypeInfer)
kindCheckSub σ@(TypeSource p _) = do
  (σ, κ) <- kindCheck σ
  case σ of
    TypeCore (TypeSub σ) -> pure (σ, κ)
    _ -> quit $ ExpectedSubtypable p

kindCheck :: TypeSource p -> Core p (TypeInfer, TypeInfer)
kindCheck (TypeSource p σ) = case σ of
  TypeSub (TypeVariable x) -> do
    κ <- lookupKindEnvironment x
    case κ of
      Just (TypeBinding _ κ _ _) -> pure (TypeCore $ TypeSub $ TypeVariable x, κ)
      Just (LinkTypeBinding σ) -> do
        κ <- reconstruct p (flexible σ)
        pure (TypeCore $ TypeSub $ TypeVariable x, runIdentity $ zonkType (error "unexpected logical") κ)
      Nothing -> quit $ UnknownTypeIdentifier p x
  TypeSub (TypeGlobalVariable x) -> do
    κ <- lookupKindGlobalEnvironment x
    case κ of
      Just (TypeBinding _ κ _ _) -> pure (TypeCore $ TypeSub $ TypeGlobalVariable x, κ)
      Just (LinkTypeBinding σ) -> do
        κ <- reconstruct p (flexible σ)
        pure (TypeCore $ TypeSub $ TypeGlobalVariable x, runIdentity $ zonkType (error "unexpected logical") κ)
      Nothing -> quit $ UnknownTypeGlobalIdentifier p x
  Inline σ π τ -> do
    (σ', _) <- secondM (checkType' p) =<< kindCheck σ
    (π', _) <- secondM (checkMultiplicity' p) =<< kindCheck π
    (τ', _) <- secondM (checkType' p) =<< kindCheck τ
    pure (TypeCore $ Inline σ' π' τ', TypeCore $ Type)
  Poly λ -> do
    (ς, κ) <- kindCheckScheme InlineMode λ
    pure (TypeCore $ Poly ς, κ)
  FunctionPointer σ π τ -> do
    (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion' p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype' p) =<< kindCheck τ
    pure (TypeCore $ FunctionPointer σ' π' τ', TypeCore $ Pretype (TypeCore $ KindRuntime $ PointerRep) (TypeCore $ TypeSub Unrestricted))
  FunctionLiteralType σ π τ -> do
    (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion' p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype' p) =<< kindCheck τ
    pure (TypeCore $ FunctionLiteralType σ' π' τ', TypeCore $ Type)
  Tuple σs τ -> do
    (σs, (ρs, τs)) <- second unzip <$> unzip <$> traverse (secondM (checkPretype' p) <=< kindCheck) σs
    (τ', _) <- secondM (checkMultiplicity' p) =<< kindCheck τ
    for τs $ \τs -> do
      lessThen p (flexible τ') (flexible τs)
    pure (TypeCore $ Tuple σs τ', TypeCore $ Pretype (TypeCore $ KindRuntime $ StructRep ρs) τ')
  Effect σ π -> do
    (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion' p) =<< kindCheck π
    pure (TypeCore $ Effect σ' π', TypeCore $ Type)
  Unique σ -> do
    (σ', _) <- secondM (checkBoxed' p) =<< kindCheck σ
    pure (TypeCore $ Unique σ', TypeCore $ Pretype (TypeCore $ KindRuntime $ PointerRep) (TypeCore $ TypeSub Linear))
  Shared σ π -> do
    (σ', _) <- secondM (checkBoxed' p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion' p) =<< kindCheck π
    pure (TypeCore $ Shared σ' π', TypeCore $ Pretype (TypeCore $ KindRuntime $ PointerRep) (TypeCore $ TypeSub Unrestricted))
  Pointer σ -> do
    (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
    pure (TypeCore $ Pointer σ', TypeCore $ Boxed)
  Array σ -> do
    (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
    pure (TypeCore $ Array σ', TypeCore $ Boxed)
  Number ρ1 ρ2 -> do
    ρ1' <- fmap fst $ secondM (checkSignedness' p) =<< kindCheck ρ1
    ρ2' <- fmap fst $ secondM (checkSize' p) =<< kindCheck ρ2
    pure (TypeCore $ Number ρ1' ρ2', TypeCore $ Pretype (TypeCore $ KindRuntime $ WordRep ρ2') (TypeCore $ TypeSub Unrestricted))
  Boolean -> do
    pure (TypeCore $ Boolean, TypeCore $ Pretype (TypeCore $ KindRuntime $ WordRep $ TypeCore $ KindSize $ Byte) (TypeCore $ TypeSub Unrestricted))
  TypeSub World -> do
    pure (TypeCore $ TypeSub World, TypeCore Region)
  TypeSub Linear -> do
    pure (TypeCore $ TypeSub Linear, TypeCore Multiplicity)
  TypeSub Unrestricted -> do
    pure (TypeCore $ TypeSub Unrestricted, TypeCore Multiplicity)
  TypeLogical v -> absurd v
  Type -> do
    pure (TypeCore Type, TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Transparent))
  Region -> pure (TypeCore Region, TypeCore $ Top $ Kind (TypeCore $ Top Subtypable) (TypeCore $ Top Transparent))
  KindRuntime PointerRep -> pure (TypeCore $ KindRuntime PointerRep, TypeCore Representation)
  KindRuntime (StructRep κs) -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation' p) <=< kindCheck) κs
    pure (TypeCore (KindRuntime (StructRep κs')), TypeCore Representation)
  KindRuntime (WordRep κ) -> do
    (κ', _) <- secondM (checkSize' p) =<< kindCheck κ
    pure (TypeCore (KindRuntime (WordRep κ')), TypeCore Representation)
  KindSize κ -> pure (TypeCore (KindSize κ), TypeCore Size)
  KindSignedness κ -> pure (TypeCore (KindSignedness κ), TypeCore Signedness)
  Pretype κ τ -> do
    (κ', _) <- secondM (checkRepresentation' p) =<< kindCheck κ
    (τ', _) <- secondM (checkMultiplicity' p) =<< kindCheck τ
    pure (TypeCore $ Pretype κ' τ', TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Transparent))
  Boxed -> do
    pure (TypeCore $ Boxed, TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Transparent))
  Multiplicity -> do
    pure (TypeCore $ Multiplicity, TypeCore $ Top $ Kind (TypeCore $ Top Subtypable) (TypeCore $ Top Transparent))
  Representation -> pure (TypeCore Representation, TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Opaque))
  Size -> pure (TypeCore Size, TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Opaque))
  Signedness -> pure (TypeCore Signedness, TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Opaque))
  Top _ -> quit $ NotTypable p

instantiate p (TypeSchemeCore ς) = case ς of
  MonoType σ -> pure (σ, InstantiationCore InstantiateEmpty)
  TypeForall (Bound (TypePattern x κ π) σ) -> do
    τ <- freshTypeVariable p κ
    for π $ \π -> do
      lessThen p π τ
    (ς, θ) <- instantiate p $ substituteType τ x σ
    pure (ς, InstantiationCore $ InstantiateType τ θ)

expectTypeAnnotation p Nothing = quit $ ExpectedTypeAnnotation p
expectTypeAnnotation _ (Just σ) = pure σ

validateType σ = fst <$> kindCheck σ

data Checked p σ = Checked (TermUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

data CheckedScheme p σ = CheckedScheme (TermSchemeUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

typeCheckPlain :: TermSource p -> Core p (Checked p TypeUnify)
typeCheckPlain (TermSource p e) = case e of
  Annotation (TypeAnnotation e σ') -> do
    Checked e σ lΓ <- typeCheck e
    (σ', _) <- kindCheck σ'
    matchType p σ (flexible σ')
    pure $ Checked e (flexible σ') lΓ
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
    mσ <- lookuptypeGlobalEnvironment x
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiate p σ
        -- todo useNothing here is kinda of a hack
        pure $ Checked (TermCore p $ GlobalVariable x θ) τ useNothing
      Nothing -> quit $ UnknownGlobalIdentifier p x
  InlineAbstraction (Bound pm e) -> do
    (pm', σ) <- typeCheckMetaPattern pm
    π <- freshMultiplicityKindVariable p
    Checked e' τ lΓ <- augmentMetaTermPattern π pm' (typeCheck e)
    pure $ Checked (TermCore p $ InlineAbstraction $ Bound pm' e') (TypeCore $ Inline σ π τ) lΓ
  InlineApplication e1 e2 () -> do
    Checked e1' (σ, π, τ) lΓ1 <- traverse (checkInline p) =<< typeCheck e1
    Checked e2' σ' lΓ2 <- typeCheck e2
    matchType p σ σ'
    capture p π lΓ2
    pure $ Checked (TermCore p $ InlineApplication e1' e2' σ) τ (lΓ1 `combine` lΓ2)
  Bind e1 (Bound pm e2) -> do
    Checked e1' τ lΓ1 <- typeCheck e1
    (pm', τ') <- typeCheckMetaPattern pm
    matchType p τ τ'
    π <- freshMultiplicityKindVariable p
    Checked e2' σ lΓ2 <- augmentMetaTermPattern π pm' $ typeCheck e2
    capture p π lΓ1
    pure $ Checked (TermCore p $ Bind e1' $ Bound pm' e2') σ (lΓ1 `combine` lΓ2)
  PolyIntroduction λ -> do
    CheckedScheme eς σ lΓ <- typeCheckScheme InlineMode λ
    pure $ Checked (TermCore p $ PolyIntroduction $ eς) (TypeCore $ Poly σ) lΓ
  PolyElimination e () () -> do
    Checked e ς lΓ <- typeCheckPlain e
    go e ς lΓ ς
    where
      go e ς lΓ (TypeCore (TypeSub (TypeVariable x))) =
        indexKindEnvironment x >>= \case
          LinkTypeBinding σ -> go e ς lΓ (flexible σ)
          _ -> quit $ ExpectedTypeAbstraction p
      go e ς lΓ (TypeCore (Poly ς')) = do
        (σ, θ) <- instantiate p ς'
        pure $ Checked (TermCore p $ PolyElimination e θ ς) σ lΓ
      go _ _ _ _ = quit $ ExpectedTypeAbstraction p
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

    for checked $ \(Checked _ (_, π') _) -> do
      matchType p π π'
      pure ()

    let (es, σs, lΓs) = unzip3 $ map (\(Checked es (σ, _) lΓ) -> (es, σ, lΓ)) checked
    τ <- makeTuple p σs

    pure $
      Checked
        (TermCore p $ TermRuntime $ TupleIntroduction es)
        (TypeCore $ Effect τ π)
        (combineAll lΓs)
  TermRuntime (ReadReference e) -> do
    Checked e' ((σ, π2), π) lΓ <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck e
    requireUnrestricted p σ
    lessThen p π2 π
    pure $ Checked (TermCore p $ TermRuntime $ ReadReference e') (TypeCore $ Effect σ π) lΓ
  TermRuntime (WriteReference ep ev ()) -> do
    Checked ep (((σ), π2), π) lΓ1 <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
    Checked ev (σ', π') lΓ2 <- traverse (checkEffect p) =<< typeCheck ev
    matchType p σ σ'
    matchType p π π'
    lessThen p π2 π
    requireUnrestricted p σ
    μ <- makeTuple p []
    pure $
      Checked
        (TermCore p $ TermRuntime $ WriteReference ep ev σ)
        (TypeCore $ Effect μ π)
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
  TermErasure (Borrow eu (Bound (TypePatternSource p' α κpm πs) (Bound pm e))) -> do
    -- Shadowing type variables is prohibited

    vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
    let α' = fresh vars α
    let pmσ = TypePatternSource p' α' κpm πs
    pm <- pure $ convertType α' α pm
    e <- pure $ convertType α' α e
    πs <- pure $ fmap (convertType α' α) πs
    π <- case πs of
      [π] -> pure π
      _ -> quit $ IncorrectRegionBounds p

    (π, κ) <- kindCheckSub π

    Checked eu' (τ, π') lΓ1 <- traverse (firstM (checkUnique p) <=< checkEffect p) =<< typeCheck eu
    matchType p (TypeCore $ TypeSub π) π'

    (pmσ', κ') <- kindCheckPattern SymbolMode pmσ
    matchType p (flexible κ) (flexible κ')
    checkRegion' p κ
    σ' <- freshPretypeTypeVariable p
    augmentTypePatternLevel pmσ' $ do
      (pm', (τ', α')) <- secondM (checkShared p) =<< typeCheckRuntimePattern pm
      matchType p (TypeCore $ TypeSub $ TypeVariable α) α'
      matchType p τ τ'
      augmentRuntimeTermPattern pm' $ do
        Checked e' (σ, α'') lΓ2 <- traverse (checkEffect p) =<< typeCheck e
        matchType p σ σ'
        matchType p (TypeCore $ TypeSub $ TypeVariable α) α''
        μ <- makeTuple p [σ, TypeCore $ Unique τ]
        pure $
          Checked
            (TermCore p $ TermErasure $ Borrow eu' (Bound (flexible $ toTypePattern pmσ') (Bound pm' e')))
            (TypeCore $ Effect μ π')
            (lΓ1 `combine` lΓ2)
  Annotation (TypeAnnotation e σ') -> do
    Checked e σ lΓ <- typeCheck e
    σ' <- fst <$> kindCheck σ'
    matchType p σ (flexible σ')
    pure $ Checked e σ lΓ
  Annotation (PretypeAnnotation e σ') -> do
    Checked e τ lΓ <- typeCheck e
    (σ, _) <- checkEffect p τ
    σ' <- fst <$> kindCheck σ'
    matchType p σ (flexible σ')
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
    Checked ep' ((σ, π2), π) lΓ1 <- traverse (firstM (firstM (checkArray p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
    Checked ei' ((κ1, κ2), π') lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck ei
    matchType p π π'
    matchType p κ1 (TypeCore $ KindSignedness Unsigned)
    matchType p κ2 (TypeCore $ KindSize Native)
    pure $
      Checked
        (TermCore p $ TermRuntime $ PointerIncrement ep' ei' σ)
        (TypeCore $ Effect (TypeCore $ Shared (TypeCore $ Array σ) π2) π)
        (lΓ1 `combine` lΓ2)
  TermErasure (IsolatePointer e) -> do
    Checked e ((σ, π2), π) lΓ <- traverse (firstM (firstM (checkArray p) <=< checkShared p) <=< checkEffect p) =<< typeCheck e
    pure $
      Checked
        (TermCore p $ TermErasure $ IsolatePointer e)
        (TypeCore $ Effect (TypeCore $ Shared (TypeCore $ Pointer σ) π2) π)
        lΓ
  TermSugar (Not e) -> do
    Checked e' ((), π) lΓ <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    pure $ Checked (TermCore p $ TermSugar $ Not e') (TypeCore $ Effect (TypeCore Boolean) π) lΓ
  TermSugar (And e ey) -> do
    Checked e' ((), π) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked ey' ((), π') lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck ey
    matchType p π π'
    pure $ Checked (TermCore p $ TermSugar $ And e' ey') (TypeCore $ Effect (TypeCore Boolean) π) (lΓ1 `combine` (lΓ2 `branch` useNothing))
  TermSugar (Or e en) -> do
    Checked e' ((), π) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked en' ((), π') lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck en
    matchType p π π'
    pure $ Checked (TermCore p $ TermSugar $ Or e' en') (TypeCore $ Effect (TypeCore Boolean) π) (lΓ1 `combine` (useNothing `branch` lΓ2))
  TermSugar (Do e1 e2) -> do
    Checked e1' (τ, π) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    μ <- makeTuple p []
    matchType p τ μ
    Checked e2' (σ, π') lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
    matchType p π π'
    pure $ Checked (TermCore p $ TermSugar $ Do e1' e2') (TypeCore $ Effect σ π) (lΓ1 `combine` lΓ2)

typeCheckScheme :: Mode -> TermSchemeSource p -> Core p (CheckedScheme p TypeSchemeUnify)
typeCheckScheme mode (TermSchemeSource p (TypeAbstraction (Bound (TypePatternSource p' α κpm π) e))) = do
  -- Shadowing type variables is prohibited
  vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
  let α' = fresh vars α
  let pm = TypePatternSource p' α' κpm π
  e <- pure $ convertType α' α e

  (pm', _) <- kindCheckPattern mode pm

  augmentTypePatternLevel pm' $ do
    CheckedScheme e' σ' lΓ <- typeCheckScheme mode e
    pure $
      CheckedScheme
        (TermSchemeCore p $ TypeAbstraction (Bound (toTypePattern pm') e'))
        (TypeSchemeCore $ TypeForall (Bound (toTypePattern pm') σ'))
        lΓ
typeCheckScheme _ (TermSchemeSource p (MonoTerm e)) = do
  Checked e σ lΓ <- typeCheck e
  pure $ CheckedScheme (TermSchemeCore p $ MonoTerm e) (TypeSchemeCore $ MonoType σ) lΓ

defaultType _ _ (Just upper) = pure $ TypeCore $ TypeSub upper
defaultType p μ Nothing = do
  μ'@(TypeCore μ) <- finish μ
  case μ of
    Representation -> pure $ TypeCore $ KindRuntime $ PointerRep
    Size -> pure $ TypeCore $ KindSize $ Int
    Signedness -> pure $ TypeCore $ KindSignedness $ Signed
    Region -> pure $ TypeCore $ TypeSub World
    Multiplicity -> pure $ TypeCore $ TypeSub Unrestricted
    (TypeLogical v) -> absurd v
    _ -> quit $ AmbiguousType p μ'

finish :: (ZonkType u) => u TypeLogical -> Core p (u v)
finish σ = zonkType go σ
  where
    go x =
      indexTypeLogicalMap x >>= \case
        LinkTypeLogical σ -> finish σ
        UnboundTypeLogical p κ _ upper _ -> do
          σ <- defaultType p κ upper
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
        (UnboundTypeLogical _ κ vars _ _) -> do
          α <- foldMap Set.toList <$> traverse unsolvedTypeLogical vars
          β <- Set.toList <$> unsolvedTypeLogical κ
          pure $ α <> β

unsolvedTypeLogical :: TypeUnify -> Core p (Set TypeLogical)
unsolvedTypeLogical σ = do
  let α = Set.toList (freeTypeLogical σ)
  α <- for α $ \x ->
    indexTypeLogicalMap x >>= \case
      LinkTypeLogical σ -> unsolvedTypeLogical σ
      UnboundTypeLogical _ _ _ Nothing _ -> pure $ Set.singleton x
      _ -> pure $ Set.empty
  pure $ Set.unions α

-- todo actually use levels for generalization
generalize' :: [String] -> [TypeLogical] -> (TermSchemeUnify p, TypeSchemeUnify) -> Core p (TermSchemeUnify p, TypeSchemeUnify)
generalize' _ [] (e, σ) = pure (e, σ)
generalize' [] _ _ = error "names not infinite"
generalize' (n : names) (x : xs) (e, σ) = do
  (e, σ) <- generalize' names xs (e, σ)
  indexTypeLogicalMap x >>= \case
    UnboundTypeLogical p κ π _ _ -> do
      modifyTypeLogicalMap $ \σΓ -> Map.insert x (LinkTypeLogical $ TypeCore $ TypeSub $ TypeVariable $ TypeIdentifier n) σΓ
      pure
        ( TermSchemeCore p $ TypeAbstraction (Bound (TypePattern (TypeIdentifier n) κ π) e),
          TypeSchemeCore $ TypeForall (Bound (TypePattern (TypeIdentifier n) κ π) σ)
        )
    _ -> error "generalization error"

generalize :: Mode -> (TermUnify p, TypeUnify) -> Core p (TermSchemeInfer p, TypeSchemeInfer)
generalize mode (e@(TermCore p _), σ) = do
  vars <- unsolvedTypeLogical σ
  vars <- topologicalBoundsSort (Set.toList vars)
  vars <-
    case mode of
      SymbolMode -> do
        flip filterM vars $ \x -> do
          indexTypeLogicalMap x >>= \case
            UnboundTypeLogical p κ _ _ _ -> do
              TypeCore μ <- reconstruct p κ
              case μ of
                Top (Kind _ (TypeCore (Top Opaque))) -> pure False
                Top (Kind _ (TypeCore (Top Transparent))) -> pure True
                _ -> error "generalization error"
            LinkTypeLogical _ -> error "generalization error"
      InlineMode -> pure vars
  used <- usedVars <$> getState
  let names = filter (\x -> x `Set.notMember` used) $ temporaries' ((: []) <$> ['A' .. 'Z'])
  (e, σ) <- generalize' names vars (TermSchemeCore p $ MonoTerm e, TypeSchemeCore $ MonoType σ)
  e <- finish e
  σ <- finish σ
  pure (e, σ)

typeCheckGlobalAuto ::
  Mode ->
  TermSource p ->
  Core p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalAuto mode e = do
  Checked e σ _ <- typeCheck e
  (e, ς) <- generalize mode (e, σ)
  pure (e, ς)

typeCheckGlobalSemi ::
  Mode -> TermSchemeSource p -> Core p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalSemi mode e = do
  CheckedScheme e ς _ <- typeCheckScheme mode e
  ς <- finish ς
  e <- finish e
  pure (e, ς)

typeCheckGlobalManual ::
  forall p.
  Mode ->
  TermSchemeSource p ->
  TypeSchemeSource p ->
  Core p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalManual mode e ς = do
  (ς, _) <- kindCheckScheme mode ς
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
      (TypeSchemeCore (TypeForall (Bound (TypePattern x κ π) ς)))
      (TermSchemeSource _ (TypeAbstraction (Bound (TypePatternSource p x' κ' π') e))) = do
        (κ', _) <- kindCheck κ'
        matchType p (flexible κ) (flexible κ')

        (π', _) <- unzip <$> traverse kindCheck π'
        sequence $ zipWith (matchType p) (map flexible π) (map flexible π')

        π <- pure $ map assumeSub π
        e' <- augmentKindEnvironment p x' κ (Set.fromList π) minBound $ go (convertType x' x ς) e
        pure $ TermSchemeCore p $ TypeAbstraction (Bound (TypePattern x' (flexible κ) (map (TypeCore . TypeSub) π)) e')
        where
          assumeSub (TypeCore (TypeSub σ)) = σ
          assumeSub _ = error "not sub"
    go _ (TermSchemeSource p _) = quit $ MismatchedTypeLambdas p

typeCheckGlobalScope ::
  forall p.
  Mode ->
  TermSource p ->
  TypeSchemeSource p ->
  Core p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalScope mode e@(TermSource p _) ς = do
  (ς, _) <- kindCheckScheme mode ς
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
      (TypeSchemeCore (TypeForall (Bound (TypePattern x κ π) ς))) =
        do
          π <- pure $ map assumeSub π
          e' <- augmentKindEnvironment p x κ (Set.fromList π) minBound $ go ς
          pure $ TermSchemeCore p $ TypeAbstraction (Bound (TypePattern x (flexible κ) (map (TypeCore . TypeSub) π)) e')
        where
          assumeSub (TypeCore (TypeSub σ)) = σ
          assumeSub _ = error "not sub"

-- todo remove this and do it in global type checking
syntaticCheck :: (TermSchemeInfer p, TypeSchemeInfer) -> Core p (TermSchemeInfer p, TypeSchemeInfer)
syntaticCheck (e@(TermSchemeCore p _), ς) = do
  syntaticFunctionCheck p ς
  pure (e, ς)

syntaticFunctionCheck _ (TypeSchemeCore (MonoType (TypeCore (FunctionLiteralType _ _ _)))) = pure ()
syntaticFunctionCheck p (TypeSchemeCore (TypeForall (Bound _ ς))) = syntaticFunctionCheck p ς
syntaticFunctionCheck p _ = quit $ ExpectedFunctionLiteral p
