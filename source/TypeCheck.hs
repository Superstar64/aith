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
import Linearity
import Misc.Util (firstM, secondM, sortTopological, temporaries')
import TypeCheck.Core
import TypeCheck.Unify

data Mode = InlineMode | SymbolMode

freshTypeVariable p κ = (TypeAst () . TypeLogical) <$> (Level <$> levelCounter <$> getState >>= freshTypeVariableRaw p κ [] Nothing)

freshRepresentationKindVariable p = freshTypeVariable p (TypeAst () Representation)

freshSizeKindVariable p = freshTypeVariable p (TypeAst () Size)

freshSignednessKindVariable p = freshTypeVariable p (TypeAst () Signedness)

check' error f p σ = case f σ of
  Just σ -> pure σ
  Nothing -> quit $ error p σ

checkKind' = check' ExpectedKind $ \case
  (TypeAst () (Top (Kind σ τ))) -> Just (σ, τ)
  _ -> Nothing

checkRepresentation' = check' ExpectedRepresentation $ \case
  (TypeAst () Representation) -> Just ()
  _ -> Nothing

checkMultiplicity' = check' ExpectedMultiplicity $ \case
  (TypeAst () Multiplicity) -> Just ()
  _ -> Nothing

checkSize' = check' ExpectedSize $ \case
  (TypeAst () Size) -> Just ()
  _ -> Nothing

checkSignedness' = check' ExpectedSignedness $ \case
  (TypeAst () Signedness) -> Just ()
  _ -> Nothing

checkType' = check' ExpectedType $ \case
  (TypeAst () Type) -> Just ()
  _ -> Nothing

checkPretype' = check' ExpectedPretype $ \case
  (TypeAst () (Pretype κ τ)) -> Just (κ, τ)
  _ -> Nothing

checkPretype p σ = do
  κ <- freshRepresentationKindVariable p
  τ <- freshMultiplicityKindVariable p
  matchType p σ (TypeAst () $ Pretype κ τ)
  pure (κ, τ)

checkBoxed' = check' ExpectedBoxed $ \case
  (TypeAst () Boxed) -> Just ()
  _ -> Nothing

checkRegion' = check' ExpectedRegion $ \case
  (TypeAst () Region) -> Just ()
  _ -> Nothing

checkSubtypable' = check' ExpectedSubtypable' $ \case
  (TypeAst () (Top Subtypable)) -> Just ()
  _ -> Nothing

freshMetaTypeVariable p = do
  freshTypeVariable p (TypeAst () Type)

freshMultiplicityKindVariable p = do
  freshTypeVariable p (TypeAst () Multiplicity)

freshPretypeTypeVariable p = do
  s <- freshRepresentationKindVariable p
  τ <- freshMultiplicityKindVariable p
  freshTypeVariable p (TypeAst () $ Pretype s τ)

freshBoxedTypeVariable p = do
  freshTypeVariable p (TypeAst () Boxed)

freshRegionTypeVariable p = do
  freshTypeVariable p $ TypeAst () $ Region

checkInline p σt = do
  σ <- freshMetaTypeVariable p
  π <- freshMultiplicityKindVariable p
  τ <- freshMetaTypeVariable p
  matchType p σt (TypeAst () (Inline σ π τ))
  pure (σ, π, τ)

checkFunctionPointer p σt = do
  σ <- freshPretypeTypeVariable p
  π <- freshRegionTypeVariable p
  τ <- freshPretypeTypeVariable p
  matchType p σt (TypeAst () $ FunctionPointer σ π τ)
  pure (σ, π, τ)

checkFunctionLiteralType p σt = do
  σ <- freshPretypeTypeVariable p
  π <- freshRegionTypeVariable p
  τ <- freshPretypeTypeVariable p
  matchType p σt (TypeAst () $ FunctionLiteralType σ π τ)
  pure (σ, π, τ)

checkUnique p σt = do
  σ <- freshBoxedTypeVariable p
  matchType p σt (TypeAst () $ Unique σ)
  pure σ

checkPointer p σt = do
  σ <- freshPretypeTypeVariable p
  matchType p σt (TypeAst () $ Pointer σ)
  pure (σ)

checkArray p σt = do
  σ <- freshPretypeTypeVariable p
  matchType p σt (TypeAst () $ Array σ)
  pure (σ)

checkEffect p σt = do
  σ <- freshPretypeTypeVariable p
  π <- freshRegionTypeVariable p
  matchType p σt (TypeAst () $ Effect σ π)
  pure (σ, π)

checkShared p σt = do
  σ <- freshBoxedTypeVariable p
  π <- freshRegionTypeVariable p
  matchType p σt (TypeAst () $ Shared σ π)
  pure (σ, π)

checkNumber p σt = do
  ρ1 <- freshSignednessKindVariable p
  ρ2 <- freshSizeKindVariable p
  matchType p σt (TypeAst () $ Number ρ1 ρ2)
  pure (ρ1, ρ2)

checkBoolean p σt = do
  matchType p σt (TypeAst () $ Boolean)

checkStep p σt = do
  σ <- freshPretypeTypeVariable p
  τ <- freshPretypeTypeVariable p
  matchType p σt (TypeAst () $ Step σ τ)
  pure (σ, τ)

augmentVariableLinear p x l ς check = do
  Checked e σ lΓ <- augmentTypeEnvironment x p l ς check
  case count x lΓ of
    Single -> pure ()
    _ -> matchType p l (TypeAst () $ TypeSub Unrestricted)
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
  matchType p l (TypeAst () $ TypeSub Unrestricted)
  pure ()

makeTuple p σs = do
  π <- freshMultiplicityKindVariable p
  for σs $ \σ -> do
    κ <- reconstruct p σ
    (_, π') <- checkPretype p κ
    lessThen p π π'
  pure $ TypeAst () $ Tuple σs π

augmentMetaTermPattern l (TermPattern p (PatternVariable x (Core σ))) = augmentVariableLinear p x l (TypeScheme () $ MonoType σ)

polyEffect name σ = TypeScheme () $ TypeForall (Bound (TypePattern () freshVar (TypeAst () Region) []) bounded)
  where
    bounded = TypeScheme () $ MonoType $ TypeAst () $ Effect σ (TypeAst () $ TypeSub $ TypeVariable freshVar)
    freshVar = fresh (freeVariablesType σ) (TypeIdentifier name)

augmentRuntimeTermPattern pm = go pm
  where
    go (TermRuntimePattern p (RuntimePatternVariable x (Core σ))) = \e -> do
      κ <- reconstruct p σ
      (_, l) <- checkPretype p κ
      augmentVariableLinear p x l (polyEffect "R" σ) e
    go (TermRuntimePattern _ (RuntimePatternTuple pms)) = foldr (.) id (map go pms)

typeCheckMetaPattern = \case
  (TermPattern p (PatternVariable x (Source σ))) -> do
    σ' <- case σ of
      Nothing -> freshMetaTypeVariable p
      Just σ -> do
        (σ', _) <- secondM (checkType' p) =<< kindCheck σ
        pure (flexible σ')
    pure (TermPattern p (PatternVariable x (Core σ')), σ')

typeCheckRuntimePattern = \case
  (TermRuntimePattern p (RuntimePatternVariable x (Source σ))) -> do
    σ' <- case σ of
      Nothing -> freshPretypeTypeVariable p
      Just σ -> do
        (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
        pure (flexible σ')
    pure (TermRuntimePattern p $ RuntimePatternVariable x (Core σ'), σ')
  (TermRuntimePattern p (RuntimePatternTuple pms)) -> do
    (pms, σs) <- unzip <$> traverse typeCheckRuntimePattern pms
    τ <- makeTuple p σs
    pure (TermRuntimePattern p $ RuntimePatternTuple pms, τ)

kindCheckScheme :: Mode -> TypeSchemeSource p -> Check p (TypeSchemeInfer, TypeInfer)
kindCheckScheme mode =
  \case
    TypeScheme p (MonoType σ) -> do
      (σ', _) <- secondM (checkType' p) =<< kindCheck σ
      pure (TypeScheme () (MonoType σ'), TypeAst () Type)
    TypeScheme p (TypeForall (Bound pm σ)) -> do
      (pm', _) <- kindCheckPattern mode pm
      augmentTypePatternLevel pm' $ do
        (σ', _) <- secondM (checkType' p) =<< kindCheckScheme mode σ
        pure (TypeScheme () $ TypeForall (Bound (toTypePattern pm') σ'), TypeAst () $ Type)

kindCheckPattern :: Mode -> TypePatternSource p -> Check p (TypePatternIntermediate p, TypeInfer)
kindCheckPattern mode (TypePattern p x κ π) = do
  (κ, (μ, σ)) <- secondM (checkKind' p) =<< kindCheck κ
  case mode of
    SymbolMode -> matchType p (flexible σ) (TypeAst () $ Top Transparent)
    InlineMode -> pure ()
  (π, κ') <- unzip <$> traverse kindCheckSub π
  traverse (matchType p (flexible κ)) (map flexible κ')
  if Prelude.not $ null π
    then do
      checkSubtypable' p μ
      pure ()
    else pure ()
  pure (TypePatternIntermediate p x κ π, κ)

kindCheckSub :: TypeSource p -> Check p (TypeSub, TypeInfer)
kindCheckSub σ@(TypeAst p _) = do
  (σ, κ) <- kindCheck σ
  case σ of
    TypeAst () (TypeSub σ) -> pure (σ, κ)
    _ -> quit $ ExpectedSubtypable p

kindCheck :: TypeSource p -> Check p (TypeInfer, TypeInfer)
kindCheck (TypeAst p σ) = case σ of
  TypeSub (TypeVariable x) -> do
    κ <- lookupKindEnvironment x
    case κ of
      Just (TypeBinding _ κ _ _ _) -> pure (TypeAst () $ TypeSub $ TypeVariable x, κ)
      Just (LinkTypeBinding σ) -> do
        κ <- reconstruct p (flexible σ)
        pure (TypeAst () $ TypeSub $ TypeVariable x, runIdentity $ zonkType (error "unexpected logical") κ)
      Nothing -> quit $ UnknownTypeIdentifier p x
  TypeSub (TypeGlobalVariable x) -> do
    κ <- lookupKindGlobalEnvironment x
    case κ of
      Just (TypeBinding _ κ _ _ _) -> pure (TypeAst () $ TypeSub $ TypeGlobalVariable x, κ)
      Just (LinkTypeBinding σ) -> do
        κ <- reconstruct p (flexible σ)
        pure (TypeAst () $ TypeSub $ TypeGlobalVariable x, runIdentity $ zonkType (error "unexpected logical") κ)
      Nothing -> quit $ UnknownTypeGlobalIdentifier p x
  Inline σ π τ -> do
    (σ', _) <- secondM (checkType' p) =<< kindCheck σ
    (π', _) <- secondM (checkMultiplicity' p) =<< kindCheck π
    (τ', _) <- secondM (checkType' p) =<< kindCheck τ
    pure (TypeAst () $ Inline σ' π' τ', TypeAst () $ Type)
  Poly λ -> do
    (ς, κ) <- kindCheckScheme InlineMode λ
    pure (TypeAst () $ Poly ς, κ)
  FunctionPointer σ π τ -> do
    (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion' p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype' p) =<< kindCheck τ
    pure (TypeAst () $ FunctionPointer σ' π' τ', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) (TypeAst () $ TypeSub Unrestricted))
  FunctionLiteralType σ π τ -> do
    (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion' p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype' p) =<< kindCheck τ
    pure (TypeAst () $ FunctionLiteralType σ' π' τ', TypeAst () $ Type)
  Tuple σs τ -> do
    (σs, (ρs, τs)) <- second unzip <$> unzip <$> traverse (secondM (checkPretype' p) <=< kindCheck) σs
    (τ', _) <- secondM (checkMultiplicity' p) =<< kindCheck τ
    for τs $ \τs -> do
      lessThen p (flexible τ') (flexible τs)
    pure (TypeAst () $ Tuple σs τ', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ StructRep ρs) τ')
  Step σ τ -> do
    (σ, (κ, _)) <- secondM (checkPretype' p) =<< kindCheck σ
    (τ, (μ, _)) <- secondM (checkPretype' p) =<< kindCheck τ
    let union = TypeAst () $ KindRuntime $ UnionRep $ [κ, μ]
    let wrap = TypeAst () $ KindRuntime $ StructRep $ [TypeAst () $ KindRuntime $ WordRep $ TypeAst () $ KindSize $ Byte, union]
    pure (TypeAst () $ Step σ τ, TypeAst () $ Pretype wrap $ TypeAst () $ TypeSub $ Linear)
  Effect σ π -> do
    (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion' p) =<< kindCheck π
    pure (TypeAst () $ Effect σ' π', TypeAst () $ Type)
  Unique σ -> do
    (σ', _) <- secondM (checkBoxed' p) =<< kindCheck σ
    pure (TypeAst () $ Unique σ', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) (TypeAst () $ TypeSub Linear))
  Shared σ π -> do
    (σ', _) <- secondM (checkBoxed' p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion' p) =<< kindCheck π
    pure (TypeAst () $ Shared σ' π', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) (TypeAst () $ TypeSub Unrestricted))
  Pointer σ -> do
    (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
    pure (TypeAst () $ Pointer σ', TypeAst () $ Boxed)
  Array σ -> do
    (σ', _) <- secondM (checkPretype' p) =<< kindCheck σ
    pure (TypeAst () $ Array σ', TypeAst () $ Boxed)
  Number ρ1 ρ2 -> do
    ρ1' <- fmap fst $ secondM (checkSignedness' p) =<< kindCheck ρ1
    ρ2' <- fmap fst $ secondM (checkSize' p) =<< kindCheck ρ2
    pure (TypeAst () $ Number ρ1' ρ2', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ WordRep ρ2') (TypeAst () $ TypeSub Unrestricted))
  Boolean -> do
    pure (TypeAst () $ Boolean, TypeAst () $ Pretype (TypeAst () $ KindRuntime $ WordRep $ TypeAst () $ KindSize $ Byte) (TypeAst () $ TypeSub Unrestricted))
  TypeSub World -> do
    pure (TypeAst () $ TypeSub World, TypeAst () Region)
  TypeSub Linear -> do
    pure (TypeAst () $ TypeSub Linear, TypeAst () Multiplicity)
  TypeSub Unrestricted -> do
    pure (TypeAst () $ TypeSub Unrestricted, TypeAst () Multiplicity)
  TypeLogical v -> absurd v
  Type -> do
    pure (TypeAst () Type, TypeAst () $ Top $ Kind (TypeAst () $ Top Invariant) (TypeAst () $ Top Transparent))
  Region -> pure (TypeAst () Region, TypeAst () $ Top $ Kind (TypeAst () $ Top Subtypable) (TypeAst () $ Top Transparent))
  KindRuntime PointerRep -> pure (TypeAst () $ KindRuntime PointerRep, TypeAst () Representation)
  KindRuntime (StructRep κs) -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation' p) <=< kindCheck) κs
    pure (TypeAst () (KindRuntime (StructRep κs')), TypeAst () Representation)
  KindRuntime (UnionRep κs) -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation' p) <=< kindCheck) κs
    pure (TypeAst () (KindRuntime (UnionRep κs')), TypeAst () Representation)
  KindRuntime (WordRep κ) -> do
    (κ', _) <- secondM (checkSize' p) =<< kindCheck κ
    pure (TypeAst () (KindRuntime (WordRep κ')), TypeAst () Representation)
  KindSize κ -> pure (TypeAst () (KindSize κ), TypeAst () Size)
  KindSignedness κ -> pure (TypeAst () (KindSignedness κ), TypeAst () Signedness)
  Pretype κ τ -> do
    (κ', _) <- secondM (checkRepresentation' p) =<< kindCheck κ
    (τ', _) <- secondM (checkMultiplicity' p) =<< kindCheck τ
    pure (TypeAst () $ Pretype κ' τ', TypeAst () $ Top $ Kind (TypeAst () $ Top Invariant) (TypeAst () $ Top Transparent))
  Boxed -> do
    pure (TypeAst () $ Boxed, TypeAst () $ Top $ Kind (TypeAst () $ Top Invariant) (TypeAst () $ Top Transparent))
  Multiplicity -> do
    pure (TypeAst () $ Multiplicity, TypeAst () $ Top $ Kind (TypeAst () $ Top Subtypable) (TypeAst () $ Top Transparent))
  Representation -> pure (TypeAst () Representation, TypeAst () $ Top $ Kind (TypeAst () $ Top Invariant) (TypeAst () $ Top Opaque))
  Size -> pure (TypeAst () Size, TypeAst () $ Top $ Kind (TypeAst () $ Top Invariant) (TypeAst () $ Top Opaque))
  Signedness -> pure (TypeAst () Signedness, TypeAst () $ Top $ Kind (TypeAst () $ Top Invariant) (TypeAst () $ Top Opaque))
  Top _ -> quit $ NotTypable p

instantiate p (TypeScheme () ς) = case ς of
  MonoType σ -> pure (σ, Instantiation InstantiateEmpty)
  TypeForall (Bound (TypePattern () x κ π) σ) -> do
    τ <- freshTypeVariable p κ
    for π $ \π -> do
      lessThen p π τ
    (ς, θ) <- instantiate p $ substituteType τ x σ
    pure (ς, Instantiation $ InstantiateType τ θ)

expectTypeAnnotation p Nothing = quit $ ExpectedTypeAnnotation p
expectTypeAnnotation _ (Just σ) = pure σ

validateType σ = fst <$> kindCheck σ

data Checked p σ = Checked (TermUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

data CheckedScheme p σ = CheckedScheme (TermSchemeUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

typeCheckPlain :: TermSource p -> Check p (Checked p TypeUnify)
typeCheckPlain (Term p e) = case e of
  Annotation (Source (TypeAnnotation e σ')) -> do
    Checked e σ lΓ <- typeCheck e
    (σ', _) <- kindCheck σ'
    matchType p σ (flexible σ')
    pure $ Checked e (flexible σ') lΓ
  _ -> quit $ ExpectedTypeAnnotation p

typeCheck :: TermSource p -> Check p (Checked p TypeUnify)
typeCheck (Term p e) = case e of
  TermRuntime (Variable x (Source ())) -> do
    mσ <- lookupTypeEnviroment x
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiate p σ
        pure $ Checked (Term p $ TermRuntime $ Variable x (Core θ)) τ (Use x)
      Nothing -> quit $ UnknownIdentifier p x
  GlobalVariable x (Source ()) -> do
    mσ <- lookuptypeGlobalEnvironment x
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiate p σ
        -- todo useNothing here is kinda of a hack
        pure $ Checked (Term p $ GlobalVariable x (Core θ)) τ useNothing
      Nothing -> quit $ UnknownGlobalIdentifier p x
  InlineAbstraction (Bound pm e) -> do
    (pm', σ) <- typeCheckMetaPattern pm
    π <- freshMultiplicityKindVariable p
    Checked e' τ lΓ <- augmentMetaTermPattern π pm' (typeCheck e)
    pure $ Checked (Term p $ InlineAbstraction $ Bound pm' e') (TypeAst () $ Inline σ π τ) lΓ
  InlineApplication e1 e2 (Source ()) -> do
    Checked e1' (σ, π, τ) lΓ1 <- traverse (checkInline p) =<< typeCheck e1
    Checked e2' σ' lΓ2 <- typeCheck e2
    matchType p σ σ'
    capture p π lΓ2
    pure $ Checked (Term p $ InlineApplication e1' e2' (Core σ)) τ (lΓ1 `combine` lΓ2)
  Bind e1 (Bound pm e2) -> do
    Checked e1' τ lΓ1 <- typeCheck e1
    (pm', τ') <- typeCheckMetaPattern pm
    matchType p τ τ'
    π <- freshMultiplicityKindVariable p
    Checked e2' σ lΓ2 <- augmentMetaTermPattern π pm' $ typeCheck e2
    capture p π lΓ1
    pure $ Checked (Term p $ Bind e1' $ Bound pm' e2') σ (lΓ1 `combine` lΓ2)
  PolyIntroduction λ -> do
    CheckedScheme eς σ lΓ <- typeCheckScheme InlineMode λ
    pure $ Checked (Term p $ PolyIntroduction $ eς) (TypeAst () $ Poly σ) lΓ
  PolyElimination e (Source ()) (Source ()) -> do
    Checked e ς lΓ <- typeCheckPlain e
    go e ς lΓ ς
    where
      go e ς lΓ (TypeAst () (TypeSub (TypeVariable x))) =
        indexKindEnvironment x >>= \case
          LinkTypeBinding σ -> go e ς lΓ (flexible σ)
          _ -> quit $ ExpectedTypeAbstraction p
      go e ς lΓ (TypeAst () (TypeSub (TypeGlobalVariable x))) =
        indexKindGlobalEnvironment x >>= \case
          LinkTypeBinding σ -> go e ς lΓ (flexible σ)
          _ -> quit $ ExpectedTypeAbstraction p
      go e ς lΓ (TypeAst () (Poly ς')) = do
        (σ, θ) <- instantiate p ς'
        pure $ Checked (Term p $ PolyElimination e (Core θ) (Core ς)) σ lΓ
      go _ _ _ _ = quit $ ExpectedTypeAbstraction p
  TermRuntime (Alias e1 (Bound pm e2)) -> do
    (pm', τ) <- typeCheckRuntimePattern pm
    Checked e1' (τ', π) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p τ τ'
    Checked e2' (σ, π') lΓ2 <- traverse (checkEffect p) =<< augmentRuntimeTermPattern pm' (typeCheck e2)
    matchType p π π'
    pure $ Checked (Term p $ TermRuntime $ Alias e1' $ Bound pm' e2') (TypeAst () $ Effect σ π) (lΓ1 `combine` lΓ2)
  TermRuntime (Extern sym (Source ()) (Source ()) (Source ())) -> do
    σ <- freshPretypeTypeVariable p
    π <- freshRegionTypeVariable p
    τ <- freshPretypeTypeVariable p
    r <- freshRegionTypeVariable p
    pure $
      Checked
        (Term p $ TermRuntime $ Extern sym (Core σ) (Core π) (Core τ))
        (TypeAst () $ Effect (TypeAst () $ FunctionPointer σ π τ) r)
        useNothing
  TermRuntime (FunctionApplication e1 e2 (Source ())) -> do
    Checked e1' ((σ, π2, τ), π) lΓ1 <- traverse (firstM (checkFunctionPointer p) <=< checkEffect p) =<< typeCheck e1
    lessThen p π2 π
    Checked e2' (σ', π') lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
    matchType p π π'
    matchType p σ σ'
    pure $ Checked (Term p $ TermRuntime $ FunctionApplication e1' e2' (Core σ)) (TypeAst () $ Effect τ π) (lΓ1 `combine` lΓ2)
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
        (Term p $ TermRuntime $ TupleIntroduction es)
        (TypeAst () $ Effect τ π)
        (combineAll lΓs)
  TermRuntime (ReadReference e) -> do
    Checked e' ((σ, π2), π) lΓ <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck e
    requireUnrestricted p σ
    lessThen p π2 π
    pure $ Checked (Term p $ TermRuntime $ ReadReference e') (TypeAst () $ Effect σ π) lΓ
  TermRuntime (WriteReference ep ev (Source ())) -> do
    Checked ep (((σ), π2), π) lΓ1 <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
    Checked ev (σ', π') lΓ2 <- traverse (checkEffect p) =<< typeCheck ev
    matchType p σ σ'
    matchType p π π'
    lessThen p π2 π
    requireUnrestricted p σ
    μ <- makeTuple p []
    pure $
      Checked
        (Term p $ TermRuntime $ WriteReference ep ev (Core σ))
        (TypeAst () $ Effect μ π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (NumberLiteral v) -> do
    π <- freshRegionTypeVariable p
    ρ1 <- freshSignednessKindVariable p
    ρ2 <- freshSizeKindVariable p
    pure $
      Checked
        (Term p $ TermRuntime (NumberLiteral v))
        (TypeAst () $ Effect (TypeAst () $ Number ρ1 ρ2) π)
        useNothing
  TermRuntime (Arithmatic o e1 e2 (Source ())) -> do
    Checked e1' ((ρ1, ρ2), π) lΓ1 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' ((ρ1', ρ2'), π') lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e2
    matchType p π π'
    matchType p ρ1 ρ1'
    matchType p ρ2 ρ2'
    pure $
      Checked
        (Term p $ TermRuntime $ Arithmatic o e1' e2' (Core ρ1))
        (TypeAst () $ Effect (TypeAst () $ Number ρ1 ρ2) π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (Relational o e1 e2 (Source ()) (Source ())) -> do
    Checked e1' ((ρ1, ρ2), π) lΓ1 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' ((ρ1', ρ2'), π') lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e2
    matchType p π π'
    matchType p ρ1 ρ1'
    matchType p ρ2 ρ2'
    pure $
      Checked
        (Term p $ TermRuntime $ Relational o e1' e2' (Core (TypeAst () $ Number ρ1 ρ2)) (Core ρ1))
        (TypeAst () $ Effect (TypeAst () $ Boolean) π)
        (lΓ1 `combine` lΓ2)
  FunctionLiteral (Bound pm e) -> do
    (pm', σ) <- typeCheckRuntimePattern pm
    Checked e' (τ, π) lΓ <- traverse (checkEffect p) =<< augmentRuntimeTermPattern pm' (typeCheck e)
    pure $ Checked (Term p $ FunctionLiteral $ Bound pm' e') (TypeAst () $ FunctionLiteralType σ π τ) lΓ
  TermErasure (Borrow eu (Bound (TypePattern p' α κpm πs) (Bound pm e))) -> do
    -- Shadowing type variables is prohibited

    vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
    let α' = fresh vars α
    let pmσ = TypePattern p' α' κpm πs
    pm <- pure $ convertType α' α pm
    e <- pure $ convertType α' α e
    πs <- pure $ fmap (convertType α' α) πs
    π <- case πs of
      [π] -> pure π
      _ -> quit $ IncorrectRegionBounds p

    (π, κ) <- kindCheckSub π

    Checked eu' (τ, π') lΓ1 <- traverse (firstM (checkUnique p) <=< checkEffect p) =<< typeCheck eu
    matchType p (TypeAst () $ TypeSub π) π'

    (pmσ', κ') <- kindCheckPattern SymbolMode pmσ
    matchType p (flexible κ) (flexible κ')
    checkRegion' p κ
    σ' <- freshPretypeTypeVariable p
    augmentTypePatternLevel pmσ' $ do
      (pm', (τ', α')) <- secondM (checkShared p) =<< typeCheckRuntimePattern pm
      matchType p (TypeAst () $ TypeSub $ TypeVariable α) α'
      matchType p τ τ'
      augmentRuntimeTermPattern pm' $ do
        Checked e' (σ, α'') lΓ2 <- traverse (checkEffect p) =<< typeCheck e
        matchType p σ σ'
        matchType p (TypeAst () $ TypeSub $ TypeVariable α) α''
        μ <- makeTuple p [σ, TypeAst () $ Unique τ]
        pure $
          Checked
            (Term p $ TermErasure $ Borrow eu' (Bound (flexible $ toTypePattern pmσ') (Bound pm' e')))
            (TypeAst () $ Effect μ π')
            (lΓ1 `combine` lΓ2)
  Annotation (Source (PretypeAnnotation (Term p (TermErasure (Wrap (Source ()) e))) σ)) -> do
    (σ, _) <- kindCheck σ
    go σ
    where
      go σ
        | (TypeAst () (TypeSub (TypeVariable x))) <- σ = indexKindEnvironment x >>= go'
        | (TypeAst () (TypeSub (TypeGlobalVariable x))) <- σ = indexKindGlobalEnvironment x >>= go'
        where
          go' (TypeBinding _ _ _ _ (Named τ)) = do
            Checked e (τ', π) lΓ <- traverse (checkEffect p) =<< typeCheck e
            matchType p (flexible τ) τ'
            pure $ Checked (Term p (TermErasure (Wrap (Core (flexible σ)) e))) (TypeAst () $ Effect (flexible σ) π) lΓ
          go' (TypeBinding _ _ _ _ Unnamed) = quit $ ExpectedNewtype p σ
          go' (LinkTypeBinding σ) = go σ
      go σ = quit $ ExpectedNewtype p σ
  TermErasure (Wrap _ _) -> do
    quit $ ExpectedTypeAnnotation p
  -- can't use typecheck plain, need to expect pretype annotation
  TermErasure (Unwrap (Source ()) (Term _ (Annotation (Source (PretypeAnnotation e σ))))) -> do
    (σ, _) <- kindCheck σ
    go σ
    where
      go σ
        | (TypeAst () (TypeSub (TypeVariable x))) <- σ = indexKindEnvironment x >>= go'
        | (TypeAst () (TypeSub (TypeGlobalVariable x))) <- σ = indexKindGlobalEnvironment x >>= go'
        where
          go' (TypeBinding _ _ _ _ (Named τ)) = do
            Checked e (σ', π) lΓ <- traverse (checkEffect p) =<< typeCheck e
            matchType p (flexible σ) σ'
            pure $ Checked (Term p (TermErasure (Unwrap (Core (flexible σ)) e))) (TypeAst () $ Effect (flexible τ) π) lΓ
          go' (TypeBinding _ _ _ _ Unnamed) = quit $ ExpectedNewtype p σ
          go' (LinkTypeBinding σ) = go σ
      go σ = quit $ ExpectedNewtype p σ
  TermErasure (Unwrap _ (Term p _)) -> do
    quit $ ExpectedTypeAnnotation p
  Annotation (Source (TypeAnnotation e σ')) -> do
    Checked e σ lΓ <- typeCheck e
    σ' <- fst <$> kindCheck σ'
    matchType p σ (flexible σ')
    pure $ Checked e σ lΓ
  Annotation (Source (PretypeAnnotation e σ')) -> do
    Checked e τ lΓ <- typeCheck e
    (σ, _) <- checkEffect p τ
    σ' <- fst <$> kindCheck σ'
    matchType p σ (flexible σ')
    pure $ Checked e τ lΓ
  TermRuntime (BooleanLiteral b) -> do
    π <- freshRegionTypeVariable p
    pure $ Checked (Term p $ TermRuntime $ BooleanLiteral b) (TypeAst () $ Effect (TypeAst () Boolean) π) useNothing
  TermRuntime (If eb et ef) -> do
    Checked eb' ((), π) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck eb
    Checked et' (σ, π') lΓ2 <- traverse (checkEffect p) =<< typeCheck et
    Checked ef' (σ', π'') lΓ3 <- traverse (checkEffect p) =<< typeCheck ef
    matchType p π π'
    matchType p π π''
    matchType p σ σ'
    pure $ Checked (Term p $ TermRuntime $ If eb' et' ef') (TypeAst () $ Effect σ π) (lΓ1 `combine` (lΓ2 `branch` lΓ3))
  TermRuntime (PointerIncrement ep ei (Source ())) -> do
    Checked ep' ((σ, π2), π) lΓ1 <- traverse (firstM (firstM (checkArray p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
    Checked ei' ((κ1, κ2), π') lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck ei
    matchType p π π'
    matchType p κ1 (TypeAst () $ KindSignedness Unsigned)
    matchType p κ2 (TypeAst () $ KindSize Native)
    pure $
      Checked
        (Term p $ TermRuntime $ PointerIncrement ep' ei' (Core σ))
        (TypeAst () $ Effect (TypeAst () $ Shared (TypeAst () $ Array σ) π2) π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (Continue e) -> do
    Checked e (σ, π) lΓ <- traverse (checkEffect p) =<< typeCheck e
    τ <- freshPretypeTypeVariable p
    pure $ Checked (Term p $ TermRuntime $ Continue e) (TypeAst () $ Effect (TypeAst () $ Step τ σ) π) lΓ
  TermRuntime (Break e) -> do
    Checked e (τ, π) lΓ <- traverse (checkEffect p) =<< typeCheck e
    σ <- freshPretypeTypeVariable p
    pure $ Checked (Term p $ TermRuntime $ Break e) (TypeAst () $ Effect (TypeAst () $ Step τ σ) π) lΓ
  TermRuntime (Loop e1 (Bound pm e2)) -> do
    (pm, σ) <- typeCheckRuntimePattern pm
    Checked e1 (σ', π) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p σ σ'
    Checked e2 ((τ, σ''), π') lΓ2 <- traverse (firstM (checkStep p) <=< checkEffect p) =<< augmentRuntimeTermPattern pm (typeCheck e2)
    matchType p π π'
    matchType p σ σ''
    capture p (TypeAst () $ TypeSub $ Unrestricted) lΓ2
    pure $ Checked (Term p $ TermRuntime $ Loop e1 (Bound pm e2)) (TypeAst () $ Effect τ π) (combine lΓ1 lΓ2)
  TermErasure (IsolatePointer e) -> do
    Checked e ((σ, π2), π) lΓ <- traverse (firstM (firstM (checkArray p) <=< checkShared p) <=< checkEffect p) =<< typeCheck e
    pure $
      Checked
        (Term p $ TermErasure $ IsolatePointer e)
        (TypeAst () $ Effect (TypeAst () $ Shared (TypeAst () $ Pointer σ) π2) π)
        lΓ
  TermSugar (Not e) -> do
    Checked e' ((), π) lΓ <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    pure $ Checked (Term p $ TermSugar $ Not e') (TypeAst () $ Effect (TypeAst () Boolean) π) lΓ
  TermSugar (And e ey) -> do
    Checked e' ((), π) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked ey' ((), π') lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck ey
    matchType p π π'
    pure $ Checked (Term p $ TermSugar $ And e' ey') (TypeAst () $ Effect (TypeAst () Boolean) π) (lΓ1 `combine` (lΓ2 `branch` useNothing))
  TermSugar (Or e en) -> do
    Checked e' ((), π) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked en' ((), π') lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck en
    matchType p π π'
    pure $ Checked (Term p $ TermSugar $ Or e' en') (TypeAst () $ Effect (TypeAst () Boolean) π) (lΓ1 `combine` (useNothing `branch` lΓ2))
  TermSugar (Do e1 e2) -> do
    Checked e1' (τ, π) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    μ <- makeTuple p []
    matchType p τ μ
    Checked e2' (σ, π') lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
    matchType p π π'
    pure $ Checked (Term p $ TermSugar $ Do e1' e2') (TypeAst () $ Effect σ π) (lΓ1 `combine` lΓ2)

typeCheckScheme :: Mode -> TermSchemeSource p -> Check p (CheckedScheme p TypeSchemeUnify)
typeCheckScheme mode (TermScheme p (TypeAbstraction (Bound (TypePattern p' α κpm π) e))) = do
  -- Shadowing type variables is prohibited
  vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
  let α' = fresh vars α
  let pm = TypePattern p' α' κpm π
  e <- pure $ convertType α' α e

  (pm', _) <- kindCheckPattern mode pm

  augmentTypePatternLevel pm' $ do
    CheckedScheme e' σ' lΓ <- typeCheckScheme mode e
    pure $
      CheckedScheme
        (TermScheme p $ TypeAbstraction (Bound (toTypePattern pm') e'))
        (TypeScheme () $ TypeForall (Bound (toTypePattern pm') σ'))
        lΓ
typeCheckScheme _ (TermScheme p (MonoTerm e)) = do
  Checked e σ lΓ <- typeCheck e
  pure $ CheckedScheme (TermScheme p $ MonoTerm e) (TypeScheme () $ MonoType σ) lΓ

defaultType _ _ (Just upper) = pure $ TypeAst () $ TypeSub upper
defaultType p μ Nothing = do
  μ'@(TypeAst () μ) <- finish μ
  case μ of
    Representation -> pure $ TypeAst () $ KindRuntime $ PointerRep
    Size -> pure $ TypeAst () $ KindSize $ Int
    Signedness -> pure $ TypeAst () $ KindSignedness $ Signed
    Region -> pure $ TypeAst () $ TypeSub World
    Multiplicity -> pure $ TypeAst () $ TypeSub Unrestricted
    (TypeLogical v) -> absurd v
    _ -> quit $ AmbiguousType p μ'

finish :: TypeAlgebra u => u () TypeLogical -> Check p (u () Void)
finish σ = zonkType go σ
  where
    go x =
      indexTypeLogicalMap x >>= \case
        LinkTypeLogical σ -> finish σ
        UnboundTypeLogical p κ _ upper _ -> do
          σ <- defaultType p κ upper
          modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkTypeLogical (flexible σ)) $ typeLogicalMap state}
          pure (flexible σ)

topologicalBoundsSort :: [TypeLogical] -> Check p [TypeLogical]
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

unsolvedTypeLogical :: TypeUnify -> Check p (Set TypeLogical)
unsolvedTypeLogical σ = do
  let α = Set.toList (freeTypeLogical σ)
  α <- for α $ \x ->
    indexTypeLogicalMap x >>= \case
      LinkTypeLogical σ -> unsolvedTypeLogical σ
      UnboundTypeLogical _ _ _ Nothing _ -> pure $ Set.singleton x
      _ -> pure $ Set.empty
  pure $ Set.unions α

-- todo actually use levels for generalization
generalize' :: [String] -> [TypeLogical] -> (TermSchemeUnify p, TypeSchemeUnify) -> Check p (TermSchemeUnify p, TypeSchemeUnify)
generalize' _ [] (e, σ) = pure (e, σ)
generalize' [] _ _ = error "names not infinite"
generalize' (n : names) (x : xs) (e, σ) = do
  (e, σ) <- generalize' names xs (e, σ)
  indexTypeLogicalMap x >>= \case
    UnboundTypeLogical p κ π _ _ -> do
      modifyTypeLogicalMap $ \σΓ -> Map.insert x (LinkTypeLogical $ TypeAst () $ TypeSub $ TypeVariable $ TypeIdentifier n) σΓ
      pure
        ( TermScheme p $ TypeAbstraction (Bound (TypePattern () (TypeIdentifier n) κ π) e),
          TypeScheme () $ TypeForall (Bound (TypePattern () (TypeIdentifier n) κ π) σ)
        )
    _ -> error "generalization error"

generalize :: Mode -> (TermUnify p, TypeUnify) -> Check p (TermSchemeInfer p, TypeSchemeInfer)
generalize mode (e@(Term p _), σ) = do
  vars <- unsolvedTypeLogical σ
  vars <- topologicalBoundsSort (Set.toList vars)
  vars <-
    case mode of
      SymbolMode -> do
        flip filterM vars $ \x -> do
          indexTypeLogicalMap x >>= \case
            UnboundTypeLogical p κ _ _ _ -> do
              TypeAst () μ <- reconstruct p κ
              case μ of
                Top (Kind _ (TypeAst () (Top Opaque))) -> pure False
                Top (Kind _ (TypeAst () (Top Transparent))) -> pure True
                _ -> error "generalization error"
            LinkTypeLogical _ -> error "generalization error"
      InlineMode -> pure vars
  used <- usedVars <$> getState
  let names = filter (\x -> x `Set.notMember` used) $ temporaries' ((: []) <$> ['A' .. 'Z'])
  (e, σ) <- generalize' names vars (TermScheme p $ MonoTerm e, TypeScheme () $ MonoType σ)
  e <- finish e
  σ <- finish σ
  pure (e, σ)

typeCheckGlobalAuto ::
  Mode ->
  TermSource p ->
  Check p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalAuto mode e = do
  Checked e σ _ <- typeCheck e
  (e, ς) <- generalize mode (e, σ)
  pure (e, ς)

typeCheckGlobalSemi ::
  Mode -> TermSchemeSource p -> Check p (TermSchemeInfer p, TypeSchemeInfer)
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
  Check p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalManual mode e ς = do
  (ς, _) <- kindCheckScheme mode ς
  e <- go ς e
  e <- finish e
  pure (e, ς)
  where
    go :: TypeSchemeInfer -> TermSchemeSource p -> Check p (TermSchemeUnify p)
    go (TypeScheme () (MonoType σ)) (TermScheme p (MonoTerm e)) = do
      Checked e σ' _ <- typeCheck e
      matchType p (flexible σ) σ'
      pure (TermScheme p $ MonoTerm e)
    go
      (TypeScheme () (TypeForall (Bound (TypePattern () x κ π) ς)))
      (TermScheme _ (TypeAbstraction (Bound (TypePattern p x' κ' π') e))) = do
        (κ', _) <- kindCheck κ'
        matchType p (flexible κ) (flexible κ')

        (π', _) <- unzip <$> traverse kindCheck π'
        sequence $ zipWith (matchType p) (map flexible π) (map flexible π')

        π <- pure $ map assumeSub π
        e' <- augmentKindEnvironment p x' κ (Set.fromList π) minBound $ go (convertType x' x ς) e
        pure $ TermScheme p $ TypeAbstraction (Bound (TypePattern () x' (flexible κ) (map (TypeAst () . TypeSub) π)) e')
        where
          assumeSub (TypeAst () (TypeSub σ)) = σ
          assumeSub _ = error "not sub"
    go _ (TermScheme p _) = quit $ MismatchedTypeLambdas p

typeCheckGlobalScope ::
  forall p.
  Mode ->
  TermSource p ->
  TypeSchemeSource p ->
  Check p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalScope mode e@(Term p _) ς = do
  (ς, _) <- kindCheckScheme mode ς
  e <- go ς
  e <- finish e
  pure (e, ς)
  where
    go :: TypeSchemeInfer -> Check p (TermSchemeUnify p)
    go (TypeScheme () (MonoType σ)) = do
      Checked e σ' _ <- typeCheck e
      matchType p (flexible σ) σ'
      pure (TermScheme p $ MonoTerm e)
    go
      (TypeScheme () (TypeForall (Bound (TypePattern () x κ π) ς))) =
        do
          π <- pure $ map assumeSub π
          e' <- augmentKindEnvironment p x κ (Set.fromList π) minBound $ go ς
          pure $ TermScheme p $ TypeAbstraction (Bound (TypePattern () x (flexible κ) (map (TypeAst () . TypeSub) π)) e')
        where
          assumeSub (TypeAst () (TypeSub σ)) = σ
          assumeSub _ = error "not sub"

-- todo remove this and do it in global type checking
syntaticCheck :: (TermSchemeInfer p, TypeSchemeInfer) -> Check p (TermSchemeInfer p, TypeSchemeInfer)
syntaticCheck (e@(TermScheme p _), ς) = do
  syntaticFunctionCheck p ς
  pure (e, ς)

syntaticFunctionCheck _ (TypeScheme () (MonoType (TypeAst () (FunctionLiteralType _ _ _)))) = pure ()
syntaticFunctionCheck p (TypeScheme () (TypeForall (Bound _ ς))) = syntaticFunctionCheck p ς
syntaticFunctionCheck p _ = quit $ ExpectedFunctionLiteral p
