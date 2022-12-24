module TypeCheck where

import Ast.Common
import Ast.Term
import Ast.Type
import Control.Monad (filterM, (<=<))
import Data.Bifunctor (second)
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Void
import Linearity
import Misc.Util (firstM, secondM, sortTopological, temporaries, uppers)
import TypeCheck.Core
import TypeCheck.Unify

data Mode = InlineMode | SymbolMode

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
  pure $ TypeAst () $ Tuple σs

-- todo relabel seems somewhat fragile here
-- this depends on `(σ, κ) <- kindCheck σ`, never having unification variables in σ
-- because relabel ignores unification variables
augmentMetaTermPattern l (TermPattern p (PatternVariable x σ)) = augmentVariableLinear p x l (reLabel (TypeScheme () $ MonoType σ))

polyEffect name σ = TypeScheme () $ TypeForall (Bound (TypePattern () freshVar (TypeAst () Region) []) bounded)
  where
    bounded = TypeScheme () $ MonoType $ TypeAst () $ Effect σ (TypeAst () $ TypeSub $ TypeVariable freshVar)
    freshVar = fresh (freeVariablesType σ) (TypeIdentifier name)

augmentRuntimeTermPattern pm = go pm
  where
    go (TermRuntimePattern p (RuntimePatternVariable x σ)) = \e -> do
      κ <- reconstruct p σ
      (_, l) <- checkPretype p κ
      augmentVariableLinear p x l (MonoLabel (polyEffect "R" σ)) e
    go (TermRuntimePattern _ (RuntimePatternTuple pms)) = foldr (.) id (map go pms)

typeCheckMetaPattern :: TermPatternSource p -> Check p (TermPatternUnify p, TypeUnify)
typeCheckMetaPattern = \case
  (TermPattern p (PatternVariable x σ)) -> do
    σ' <- case σ of
      TypeAst _ (Hole (Source ())) -> freshMetaTypeVariable p
      σ -> do
        (σ', _) <- secondM (checkType p) =<< kindCheck σ
        pure (flexible σ')
    pure (TermPattern p (PatternVariable x σ'), σ')

typeCheckRuntimePattern = \case
  (TermRuntimePattern p (RuntimePatternVariable x σ)) -> do
    σ' <- case σ of
      TypeAst _ (Hole (Source ())) -> freshPretypeTypeVariable p
      σ -> do
        (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
        pure (flexible σ')
    pure (TermRuntimePattern p $ RuntimePatternVariable x σ', σ')
  (TermRuntimePattern p (RuntimePatternTuple pms)) -> do
    (pms, σs) <- unzip <$> traverse typeCheckRuntimePattern pms
    τ <- makeTuple p σs
    pure (TermRuntimePattern p $ RuntimePatternTuple pms, τ)

kindCheckScheme :: Mode -> TypeSchemeSource p -> Check p (TypeSchemeInfer, TypeUnify)
kindCheckScheme mode =
  \case
    TypeScheme p (MonoType σ) -> do
      (σ', _) <- secondM (checkType p) =<< kindCheck σ
      pure (TypeScheme () (MonoType σ'), TypeAst () Type)
    TypeScheme p (TypeForall (Bound pm σ)) -> do
      (pm', _) <- kindCheckPattern mode pm
      augmentTypePatternLevel pm' $ do
        (σ', _) <- secondM (checkType p) =<< kindCheckScheme mode σ
        pure (TypeScheme () $ TypeForall (Bound (toTypePattern pm') σ'), TypeAst () $ Type)

kindCheckPattern :: Mode -> TypePatternSource p -> Check p (TypePatternIntermediate p, TypeUnify)
kindCheckPattern mode (TypePattern p x κ π) = do
  (κ, (μ, σ, _)) <- secondM (checkKind p) =<< kindCheck κ
  case mode of
    SymbolMode -> matchType p σ (TypeAst () Transparent)
    InlineMode -> pure ()
  (π, κ') <- unzip <$> traverse kindCheckSub π
  traverse (matchType p (flexible κ)) κ'
  if Prelude.not $ null π
    then do
      checkSubtypable p μ
      pure ()
    else pure ()
  pure (TypePatternIntermediate p x κ π, flexible κ)

kindCheckSub :: TypeSource p -> Check p (TypeSub, TypeUnify)
kindCheckSub σ@(TypeAst p _) = do
  (σ, κ) <- kindCheck σ
  case σ of
    TypeAst () (TypeSub σ) -> pure (σ, κ)
    _ -> quit $ ExpectedSubtypable p

kindCheck :: TypeSource p -> Check p (TypeInfer, TypeUnify)
kindCheck (TypeAst p σ) = case σ of
  TypeSub (TypeVariable x) -> do
    lookupKindEnvironment x >>= \case
      Just (TypeBinding _ κ _ _ _) -> pure (TypeAst () $ TypeSub $ TypeVariable x, κ)
      Nothing -> do
        heading <- moduleScope <$> askEnvironment
        kindCheck (TypeAst p $ TypeSub $ TypeGlobalVariable $ globalType heading x)
  TypeSub (TypeGlobalVariable x) -> do
    lookupKindGlobalEnvironment x >>= \case
      Just (TypeBinding _ κ _ _ _) -> pure (TypeAst () $ TypeSub $ TypeGlobalVariable x, κ)
      Nothing ->
        lookupSynonym x >>= \case
          Just σ -> do
            κ <- reconstruct p (flexible σ)
            pure (flexible σ, κ)
          Nothing -> quit $ UnknownTypeGlobalIdentifier p x
  Inline σ π τ -> do
    (σ', _) <- secondM (checkType p) =<< kindCheck σ
    (π', _) <- secondM (checkMultiplicity p) =<< kindCheck π
    (τ', _) <- secondM (checkType p) =<< kindCheck τ
    pure (TypeAst () $ Inline σ' π' τ', TypeAst () $ Type)
  Poly σ λ -> do
    (σ, _) <- secondM (checkLabel p) =<< kindCheck σ
    (ς, κ) <- kindCheckScheme InlineMode λ
    pure (TypeAst () $ Poly σ ς, κ)
  FunctionPointer σ π τ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (TypeAst () $ FunctionPointer σ' π' τ', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) (TypeAst () $ TypeSub Unrestricted))
  FunctionLiteralType σ π τ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (TypeAst () $ FunctionLiteralType σ' π' τ', TypeAst () $ Type)
  Tuple σs -> do
    (σs, (ρs, τs)) <- second unzip <$> unzip <$> traverse (secondM (checkPretype p) <=< kindCheck) σs
    τ <- freshMultiplicityKindVariable p
    for τs $ \τs -> do
      lessThen p τ τs
    pure (TypeAst () $ Tuple σs, TypeAst () $ Pretype (TypeAst () $ KindRuntime $ StructRep ρs) τ)
  Step σ τ -> do
    (σ, (κ, _)) <- secondM (checkPretype p) =<< kindCheck σ
    (τ, (μ, _)) <- secondM (checkPretype p) =<< kindCheck τ
    let union = TypeAst () $ KindRuntime $ UnionRep $ [κ, μ]
    let wrap = TypeAst () $ KindRuntime $ StructRep $ [TypeAst () $ KindRuntime $ WordRep $ TypeAst () $ KindSize $ Byte, union]
    pure (TypeAst () $ Step σ τ, TypeAst () $ Pretype wrap $ TypeAst () $ TypeSub $ Linear)
  Effect σ π -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    pure (TypeAst () $ Effect σ' π', TypeAst () $ Type)
  Unique σ -> do
    (σ', _) <- secondM (checkBoxed p) =<< kindCheck σ
    pure (TypeAst () $ Unique σ', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) (TypeAst () $ TypeSub Linear))
  Shared σ π -> do
    (σ', _) <- secondM (checkBoxed p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    pure (TypeAst () $ Shared σ' π', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) (TypeAst () $ TypeSub Unrestricted))
  Pointer σ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    pure (TypeAst () $ Pointer σ', TypeAst () $ Boxed)
  Array σ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    pure (TypeAst () $ Array σ', TypeAst () $ Boxed)
  Number ρ1 ρ2 -> do
    (ρ1', _) <- secondM (checkSignedness p) =<< kindCheck ρ1
    (ρ2', _) <- secondM (checkSize p) =<< kindCheck ρ2
    pure (TypeAst () $ Number ρ1' ρ2', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ WordRep (flexible ρ2')) (TypeAst () $ TypeSub Unrestricted))
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
    pure (TypeAst () Type, TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Transparent) uni1)
  Region -> pure (TypeAst () Region, TypeAst () $ Kind (TypeAst () Subtypable) (TypeAst () Transparent) uni1)
  KindRuntime PointerRep -> pure (TypeAst () $ KindRuntime PointerRep, TypeAst () Representation)
  KindRuntime (StructRep κs) -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< kindCheck) κs
    pure (TypeAst () (KindRuntime (StructRep κs')), TypeAst () Representation)
  KindRuntime (UnionRep κs) -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< kindCheck) κs
    pure (TypeAst () (KindRuntime (UnionRep κs')), TypeAst () Representation)
  KindRuntime (WordRep κ) -> do
    (κ', _) <- secondM (checkSize p) =<< kindCheck κ
    pure (TypeAst () (KindRuntime (WordRep κ')), TypeAst () Representation)
  KindSize κ -> pure (TypeAst () (KindSize κ), TypeAst () Size)
  KindSignedness κ -> pure (TypeAst () (KindSignedness κ), TypeAst () Signedness)
  Pretype κ τ -> do
    (κ', _) <- secondM (checkRepresentation p) =<< kindCheck κ
    (τ', _) <- secondM (checkMultiplicity p) =<< kindCheck τ
    pure (TypeAst () $ Pretype κ' τ', TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Transparent) uni1)
  Boxed -> do
    pure (TypeAst () $ Boxed, TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Transparent) uni1)
  Multiplicity -> do
    pure (TypeAst () $ Multiplicity, TypeAst () $ Kind (TypeAst () Subtypable) (TypeAst () Transparent) uni2)
  Representation -> pure (TypeAst () Representation, TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Opaque) uni2)
  Size -> pure (TypeAst () Size, TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Opaque) uni2)
  Signedness -> pure (TypeAst () Signedness, TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Opaque) uni1)
  Kind μ κ ρ -> do
    (μ, _) <- secondM (checkOrderability p) =<< kindCheck μ
    (κ, _) <- secondM (checkTransparency p) =<< kindCheck κ
    (ρ, _) <- secondM (checkUniverse p) =<< kindCheck ρ
    pure (TypeAst () (Kind μ κ ρ), TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Transparent) (TypeAst () (Higher $ flexible ρ)))
  Invariant -> do
    pure (TypeAst () Invariant, TypeAst () Orderability)
  Subtypable -> do
    pure (TypeAst () Subtypable, TypeAst () Orderability)
  Transparent -> do
    pure (TypeAst () Transparent, TypeAst () Transparency)
  Opaque -> do
    pure (TypeAst () Opaque, TypeAst () Transparency)
  Base -> do
    pure (TypeAst () Base, TypeAst () Universe)
  Higher κ -> do
    (κ, _) <- secondM (checkUniverse p) =<< (kindCheck κ)
    pure (TypeAst () $ Higher κ, TypeAst () Universe)
  Orderability -> do
    pure (TypeAst () Orderability, TypeAst () Top)
  Transparency -> do
    pure (TypeAst () Transparency, TypeAst () Top)
  Universe -> do
    pure (TypeAst () Universe, TypeAst () Top)
  AmbiguousLabel -> do
    pure (TypeAst () AmbiguousLabel, TypeAst () Label)
  Label -> do
    pure (TypeAst () Label, TypeAst () $ Top)
  Top -> quit $ NotTypable p
  Hole (Source ()) -> quit $ NotTypable p

instantiate p (TypeScheme () ς) = case ς of
  MonoType σ -> pure (σ, Instantiation InstantiateEmpty)
  TypeForall (Bound (TypePattern () x κ π) σ) -> do
    τ <- freshTypeVariable p κ
    for π $ \π -> do
      lessThen p π τ
    (ς, θ) <- instantiate p $ substituteType τ x σ
    pure (ς, Instantiation $ InstantiateType τ θ)

instantiateLabel :: p -> LabelSchemeUnify -> Check p (TypeUnify, InstantiationUnify)
instantiateLabel p (MonoLabel ς) = instantiate p ς
instantiateLabel p (LabelForall x ς) = do
  τ <- freshLabelTypeVariable p
  instantiateLabel p $ substituteLabel τ x ς
  where
    -- todo maybe make LabelScheme a part of TypeAlgebra
    substituteLabel σx x (MonoLabel σ) = MonoLabel $ substituteType σx x σ
    -- todo labels are assumed to not overlap here
    substituteLabel σx x (LabelForall x' ς) = LabelForall x' (substituteLabel σx x ς)

expectTypeAnnotation p Nothing = quit $ ExpectedTypeAnnotation p
expectTypeAnnotation _ (Just σ) = pure σ

validateType σ = fst <$> kindCheck σ

data Checked p σ = Checked (TermUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

data CheckedScheme p σ = CheckedScheme (TermSchemeUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

typeCheck :: forall p. TermSource p -> Check p (Checked p TypeUnify)
typeCheck (Term p e) = case e of
  TermRuntime (Variable x (Source ())) -> do
    mσ <- lookupTypeEnviroment x
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiateLabel p σ
        pure $ Checked (Term p $ TermRuntime $ Variable x (Core θ)) τ (Use x)
      Nothing -> do
        heading <- moduleScope <$> askEnvironment
        typeCheck (Term p $ GlobalVariable (globalTerm heading x) (Source ()))
  GlobalVariable x (Source ()) -> do
    mσ <- lookupTypeGlobalEnvironment x
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiateLabel p σ
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
    τ <- freshLabelTypeVariable p
    pure $ Checked (Term p $ PolyIntroduction $ eς) (TypeAst () $ Poly τ σ) lΓ
  PolyElimination e (Source ()) (Source ()) -> do
    enterLevel
    Checked e ς lΓ <- typeCheck e
    leaveLevel
    elimatePoly e ς lΓ
    where
      elimatePoly e τ@(TypeAst () (Poly l ς)) lΓ = do
        validateLevel l
        (σ, θ) <- instantiate p ς
        pure $ Checked (Term p $ PolyElimination e (Core θ) (Core τ)) σ lΓ
      elimatePoly e (TypeAst () (TypeLogical v)) lΓ =
        indexTypeLogicalMap v >>= \case
          LinkTypeLogical σ -> elimatePoly e σ lΓ
          _ -> quit $ ExpectedTypeAnnotation p
      elimatePoly _ _ _ = quit $ ExpectedTypeAnnotation p
      validateLevel (TypeAst () (TypeLogical v)) =
        indexTypeLogicalMap v >>= \case
          LinkTypeLogical σ -> validateLevel σ
          UnboundTypeLogical p _ _ _ level' -> do
            level <- currentLevel
            if level >= level'
              then quit $ ExpectedTypeAnnotation p
              else pure ()
      validateLevel _ = quit $ ExpectedTypeAnnotation p
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
    pure $
      Checked
        (Term p $ TermRuntime $ WriteReference ep ev (Core σ))
        (TypeAst () $ Effect (TypeAst () $ Tuple []) π)
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
    pure $ Checked (Term p $ FunctionLiteral (Bound pm' e')) (TypeAst () $ FunctionLiteralType σ π τ) lΓ
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
    matchType p κ κ'
    checkRegion p κ
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
    case σ of
      (TypeAst () (TypeSub (TypeVariable x))) -> indexKindEnvironment x >>= go σ
      (TypeAst () (TypeSub (TypeGlobalVariable x))) -> indexKindGlobalEnvironment x >>= go σ
      _ -> quit $ ExpectedNewtype p (flexible σ)
    where
      go :: TypeInfer -> TypeBinding p -> Check p (Checked p TypeUnify)
      go σ (TypeBinding _ _ _ _ (Named τ)) = do
        Checked e (τ', π) lΓ <- traverse (checkEffect p) =<< typeCheck e
        matchType p (flexible τ) τ'
        pure $ Checked (Term p (TermErasure (Wrap (Core (flexible σ)) e))) (TypeAst () $ Effect (flexible σ) π) lΓ
      go σ (TypeBinding _ _ _ _ Unnamed) = quit $ ExpectedNewtype p (flexible σ)
  TermErasure (Wrap _ _) -> do
    quit $ ExpectedTypeAnnotation p
  -- can't use typecheck plain, need to expect pretype annotation
  TermErasure (Unwrap (Source ()) (Term _ (Annotation (Source (PretypeAnnotation e σ))))) -> do
    (σ, _) <- kindCheck σ
    case σ of
      (TypeAst () (TypeSub (TypeVariable x))) -> indexKindEnvironment x >>= go σ
      (TypeAst () (TypeSub (TypeGlobalVariable x))) -> indexKindGlobalEnvironment x >>= go σ
      _ -> quit $ ExpectedNewtype p (flexible σ)
    where
      go :: TypeInfer -> TypeBinding p -> Check p (Checked p TypeUnify)
      go σ (TypeBinding _ _ _ _ (Named τ)) = do
        Checked e (σ', π) lΓ <- traverse (checkEffect p) =<< typeCheck e
        matchType p (flexible σ) σ'
        pure $ Checked (Term p (TermErasure (Unwrap (Core (flexible σ)) e))) (TypeAst () $ Effect (flexible (flexible τ)) π) lΓ
      go σ (TypeBinding _ _ _ _ Unnamed) = quit $ ExpectedNewtype p (flexible σ)
  TermErasure (Unwrap _ (Term p _)) -> do
    quit $ ExpectedTypeAnnotation p
  Annotation (Source (TypeAnnotation e τ)) -> do
    Checked e σ lΓ <- typeCheck e
    (τ, _) <- kindCheck τ
    let ς = reLabel $ TypeScheme () $ MonoType $ flexible τ
    (σ', _) <- instantiateLabel p ς
    (σ'', _) <- instantiateLabel p ς
    matchType p σ σ'
    pure $ Checked e σ'' lΓ
  Annotation (Source (PretypeAnnotation e σ')) -> do
    Checked e τ lΓ <- typeCheck e
    (σ, _) <- checkEffect p τ
    σ' <- flexible <$> fst <$> kindCheck σ'
    matchType p σ σ'
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
    matchType p τ (TypeAst () $ Tuple [])
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
        (TermScheme p $ TypeAbstraction (Bound (flexible $ toTypePattern pm') e'))
        (TypeScheme () $ TypeForall (Bound (flexible $ toTypePattern pm') σ'))
        lΓ
typeCheckScheme _ (TermScheme p (MonoTerm e (Source ()))) = do
  Checked e σ lΓ <- typeCheck e
  pure $ CheckedScheme (TermScheme p $ MonoTerm e (Core σ)) (TypeScheme () $ MonoType σ) lΓ

defaultType _ _ (Just upper) = pure $ TypeAst () $ TypeSub upper
defaultType p μ Nothing = do
  μ'@(TypeAst () μ) <- finish μ
  case μ of
    Representation -> pure $ TypeAst () $ KindRuntime $ PointerRep
    Size -> pure $ TypeAst () $ KindSize $ Int
    Signedness -> pure $ TypeAst () $ KindSignedness $ Signed
    Region -> pure $ TypeAst () $ TypeSub World
    Multiplicity -> pure $ TypeAst () $ TypeSub Unrestricted
    Label -> pure $ TypeAst () $ AmbiguousLabel
    (TypeLogical v) -> absurd v
    _ -> quit $ AmbiguousType p μ'

zonk :: TypeAlgebra u => u Core () TypeLogical -> Check p (u Core () TypeLogical)
zonk σ = zonkType go σ
  where
    go x =
      indexTypeLogicalMap x >>= \case
        LinkTypeLogical σ -> zonk σ
        UnboundTypeLogical _ _ _ _ _ -> do
          pure $ TypeAst () $ TypeLogical x

finish :: TypeAlgebra u => u Core () TypeLogical -> Check p (u Core () Void)
finish σ = zonkType go σ
  where
    go x =
      indexTypeLogicalMap x >>= \case
        LinkTypeLogical σ -> finish σ
        UnboundTypeLogical p κ _ upper _ -> do
          σ <- defaultType p κ upper
          modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkTypeLogical (flexible σ)) $ typeLogicalMap state}
          pure (flexible σ)

topologicalBoundsSort :: Map TypeLogical (TypeLogicalState p) -> [TypeLogical] -> [TypeLogical]
topologicalBoundsSort vars = runIdentity . sortTopological id quit (Identity . children)
  where
    quit x = error $ "unexpected cycle: " ++ show x
    children x = case vars Map.! x of
      LinkTypeLogical σ -> unsolvedTypeLogical vars σ
      UnboundTypeLogical _ κ bound _ _ -> α <> β
        where
          α = bound >>= unsolvedTypeLogical vars
          β = unsolvedTypeLogical vars κ

-- unsolved variables, may have duplicates
unsolvedTypeLogical :: TypeAlgebra u => Map TypeLogical (TypeLogicalState p) -> u Core () TypeLogical -> [TypeLogical]
unsolvedTypeLogical vars σ = free >>= lookup
  where
    free = freeTypeLogical σ
    lookup x | LinkTypeLogical σ <- vars Map.! x = unsolvedTypeLogical vars σ
    lookup x | UnboundTypeLogical _ _ _ Nothing _ <- vars Map.! x = [x]
    lookup _ = []

generalizable mode x = do
  level <- currentLevel
  indexTypeLogicalMap x >>= \case
    UnboundTypeLogical p κ _ _ level' -> do
      TypeAst () μ <- reconstruct p κ
      case μ of
        _ | level >= level' -> pure False
        Top -> pure False
        Kind _ _ _ | InlineMode <- mode -> pure True
        Kind _ (TypeAst () Opaque) _ -> pure False
        Kind _ (TypeAst () Transparent) _ -> pure True
        _ -> error "generalization error"
    LinkTypeLogical _ -> error "generalization error"

generalizeExact _ [] e = pure e
generalizeExact scope ((n, x) : remaining) e = do
  e <- generalizeExact scope remaining e
  indexTypeLogicalMap x >>= \case
    UnboundTypeLogical p κ π _ _ -> do
      modifyTypeLogicalMap $ \σΓ -> Map.insert x (LinkTypeLogical $ TypeAst () $ TypeSub $ TypeVariable $ TypeIdentifier n) σΓ
      pure (scope p n κ π e)
    _ -> error "generalization error"

-- todo refactor this
generalize :: Mode -> (TermUnify p, TypeUnify) -> Check p (TermSchemeUnify p, TypeSchemeUnify)
generalize mode (e@(Term p _), σ) = do
  logical <- getTypeLogicalMap
  vars <- filterM (generalizable mode) $ topologicalBoundsSort logical (unsolvedTypeLogical logical σ)
  used <- usedVars <$> getState
  let names = filter (\x -> x `Set.notMember` used) $ temporaries uppers
  generalizeExact scope (zip names vars) (TermScheme p $ MonoTerm e (Core σ), TypeScheme () $ MonoType σ)
  where
    scope p n κ π (e, σ) =
      ( TermScheme p $ TypeAbstraction (Bound (TypePattern () (TypeIdentifier n) κ π) e),
        TypeScheme () $ TypeForall (Bound (TypePattern () (TypeIdentifier n) κ π) σ)
      )

typeCheckGlobalAuto ::
  Mode ->
  TermSource p ->
  Check p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalAuto mode e = do
  enterLevel
  Checked e σ _ <- typeCheck e
  leaveLevel
  (e, ς) <- generalize mode (e, σ)
  e <- finish e
  ς <- finish ς
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
    go (TypeScheme () (MonoType σ)) (TermScheme p (MonoTerm e (Source ()))) = do
      Checked e σ' _ <- typeCheck e
      matchType p (flexible σ) σ'
      pure (TermScheme p $ MonoTerm e (Core $ flexible σ))
    go
      (TypeScheme () (TypeForall (Bound (TypePattern () x κ π) ς)))
      (TermScheme _ (TypeAbstraction (Bound (TypePattern p x' κ' π') e))) = do
        (κ', _) <- kindCheck κ'
        matchType p (flexible κ) (flexible κ')

        (π', _) <- unzip <$> traverse kindCheck π'
        sequence $ zipWith (matchType p) (map flexible π) (map flexible π')

        π <- pure $ map assumeSub π
        e' <- augmentKindEnvironment p x' (flexible κ) (Set.fromList π) minBound $ go (convertType x' x ς) e
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
      pure (TermScheme p $ MonoTerm e (Core $ flexible σ))
    go
      (TypeScheme () (TypeForall (Bound (TypePattern () x κ π) ς))) =
        do
          π <- pure $ map assumeSub π
          e' <- augmentKindEnvironment p x (flexible κ) (Set.fromList π) minBound $ go ς
          pure $ TermScheme p $ TypeAbstraction (Bound (TypePattern () x (flexible κ) (map (TypeAst () . TypeSub) π)) e')
        where
          assumeSub (TypeAst () (TypeSub σ)) = σ
          assumeSub _ = error "not sub"

typeCheckGlobalSyn :: TypeSource p -> Check p TypeInfer
typeCheckGlobalSyn σ = do
  (σ, _) <- kindCheck σ
  pure σ

typeCheckGlobalNew :: TypeSource p -> TypeSource p -> Check p (TypeInfer, TypeInfer)
typeCheckGlobalNew σ κ@(TypeAst p _) = do
  (κ', _) <- kindCheck κ
  checkPretype p (flexible κ')
  (σ, κ) <- kindCheck σ
  matchType p κ (flexible κ')
  pure (σ, κ')

typeCheckGlobalForward :: TypeSchemeSource p -> Check p TypeSchemeInfer
typeCheckGlobalForward ς = do
  (ς, _) <- kindCheckScheme SymbolMode ς
  pure ς

typeCheckGlobalNewForward :: TypeSource p -> Check p TypeInfer
typeCheckGlobalNewForward κ@(TypeAst p _) = do
  (κ, _) <- kindCheck κ
  checkPretype p (flexible κ)
  pure κ
