module TypeCheck where

import Ast.Common
import Ast.Kind
import Ast.Sort
import Ast.Term
import Ast.Type
import Control.Monad ((<=<))
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Void
import Environment
import Misc.MonoidMap (Map)
import qualified Misc.MonoidMap as Map
import Misc.Util (firstM, secondM, temporaries', visitTopological)
import TypeCheck.Core
import TypeCheck.Substitute
import TypeCheck.Unify

augmentTypePatternBottom (Pattern p x κ) = augmentKindEnvironment x p κ (error "constraints used during kind checking") (error "level usage during kind checking")

augmentTypePatternLevel (Pattern p x κ) c e = do
  lev <- Level <$> currentLevel
  augmentKindEnvironment x p κ c lev e

augmentKindPatternBottom (Pattern p x μ) = augmentSortEnvironment x p μ (error "level usage during sort checking")

augmentKindPatternLevel (Pattern p x μ) e = do
  lev <- Level <$> currentLevel
  augmentSortEnvironment x p μ lev e

freshTypeVariable p κ = (CoreType Internal . TypeLogical) <$> (Level <$> levelCounter <$> getState >>= freshTypeVariableRaw p κ Map.empty)

freshKindVariable p μ = (CoreKind Internal . KindLogical) <$> (Level <$> levelCounter <$> getState >>= freshKindVariableRaw p μ)

checkKind p μt = do
  matchSort p μt Kind
  pure ()

checkExistance p μt = do
  matchSort p μt Existance
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
  matchKind p κt (CoreKind Internal Type)
  pure κt

checkPretype p κt = do
  κ <- freshKindVariable p Existance
  matchKind p κt (CoreKind Internal (Pretype κ))
  pure κ

checkRegion p κt = do
  matchKind p κt (CoreKind Internal Region)
  pure ()

checkReal p κt = do
  κ <- freshKindVariable p Representation
  matchKind p κt (CoreKind Internal $ Real κ)
  pure κ

freshMetaTypeVariable p = do
  freshTypeVariable p (CoreKind Internal Type)

freshPretypeTypeVariable p = do
  s <- freshKindVariable p Existance
  freshTypeVariable p (CoreKind Internal $ Pretype s)

freshPretypeRealTypeVariable p = do
  s <- freshKindVariable p Representation
  freshTypeVariable p (CoreKind Internal $ Pretype $ CoreKind Internal $ Real $ s)

freshRegionTypeVariable p = do
  freshTypeVariable p $ CoreKind Internal $ Region

enforcePretypeReal p σt = do
  σ <- freshPretypeRealTypeVariable p
  matchType p σt σ
  pure σ

checkMacro p σt = do
  σ <- freshMetaTypeVariable p
  τ <- freshMetaTypeVariable p
  matchType p σt (CoreType Internal (Macro σ τ))
  pure (σ, τ)

checkFunctionPointer p σt = do
  σ <- freshPretypeRealTypeVariable p
  π <- freshRegionTypeVariable p
  τ <- freshPretypeTypeVariable p
  matchType p σt (CoreType Internal $ FunctionPointer σ π τ)
  pure (σ, π, τ)

checkFunctionLiteralType p σt = do
  σ <- freshPretypeRealTypeVariable p
  π <- freshRegionTypeVariable p
  τ <- freshPretypeTypeVariable p
  matchType p σt (CoreType Internal $ FunctionLiteralType σ π τ)
  pure (σ, π, τ)

checkReference p σt = do
  π <- freshRegionTypeVariable p
  σ <- freshPretypeRealTypeVariable p
  matchType p σt (CoreType Internal $ Reference π σ)
  pure (π, σ)

checkEffect p σt = do
  σ <- freshPretypeTypeVariable p
  π <- freshRegionTypeVariable p
  matchType p σt (CoreType Internal $ Effect σ π)
  pure (σ, π)

checkNumber p σt = do
  ρ1 <- freshKindVariable p Signedness
  ρ2 <- freshKindVariable p Size
  matchType p σt (CoreType Internal $ Number ρ1 ρ2)
  pure (ρ1, ρ2)

augmentVariableLinear p x l ς e = do
  (a, lΓ) <- augmentTypeEnvironment x p l ς e
  case l of
    Unrestricted -> pure ()
    Linear -> case count x lΓ of
      Single -> pure ()
      _ -> quit $ InvalidUsage p x
    Automatic σ -> case count x lΓ of
      Single -> pure ()
      _ -> constrain p Copy σ []
  pure (a, Remove x lΓ)

augmentMetaTermPattern pm = go Linear pm
  where
    go l (CoreTermPattern p (PatternVariable x σ)) = augmentVariableLinear p x l (CoreTypeScheme Internal $ MonoType σ)
    go _ (CoreTermPattern _ (PatternOfCourse pm)) = go Unrestricted pm

polyEffect padding σ = CoreTypeScheme Internal $ ImplicitForall (Bound (Pattern Internal freshVar (CoreKind Internal Region)) bounded) Map.empty
  where
    bounded = CoreTypeScheme Internal $ MonoType $ padding $ CoreType Internal $ Effect σ (CoreType Internal $ TypeVariable freshVar)
    freshVar = fresh (Map.keysSet $ freeVariablesInternal σ) (TypeIdentifier "R")

augmentRuntimeTermPattern pm = go pm
  where
    go (CoreTermRuntimePattern p (RuntimePatternVariable x σ)) = augmentVariableLinear p x (Automatic σ) (polyEffect id σ)
    go (CoreTermRuntimePattern _ (RuntimePatternPair pm pm')) = go pm . go pm'

capture p lΓ = do
  let captures = variablesUsed lΓ
  for (Set.toList captures) $ \x -> do
    (_, l, _) <- fromJust <$> lookupTypeEnviroment x
    case l of
      Unrestricted -> pure ()
      Linear -> quit $ CaptureLinear p x
      Automatic σ -> constrain p Copy σ []
  pure ()

typeCheckConstraints :: p -> Map.Map Constraint [Type (KindAuto p) Void p] -> KindUnify -> Core p (Map.Map Constraint [TypeUnify])
typeCheckConstraints p c κ = flip Map.traverseWithKey c $ \c σs -> do
  (σs, κs) <- unzip <$> traverse typeCheckValidateType σs
  predicateKindCheck p c κ κs
  pure σs

typeCheckAnnotateMetaPattern = \case
  (CoreTermPattern p (PatternVariable x σ)) -> do
    σ' <- case σ of
      Nothing -> freshMetaTypeVariable p
      Just σ -> do
        (σ', κ) <- typeCheckValidateType σ
        checkType p κ
        pure σ'
    pure (CoreTermPattern p $ (PatternVariable x σ'), σ')
  (CoreTermPattern p (PatternOfCourse pm)) -> do
    (pm', σ) <- typeCheckAnnotateMetaPattern pm
    pure (CoreTermPattern p (PatternOfCourse pm'), CoreType Internal (OfCourse σ))

typeCheckAnnotateRuntimePattern = \case
  (CoreTermRuntimePattern p (RuntimePatternVariable x σ)) -> do
    σ' <- case σ of
      Nothing -> freshPretypeRealTypeVariable p
      Just σ -> do
        σ' <- fst <$> typeCheckValidateType σ
        enforcePretypeReal p σ'
    pure ((CoreTermRuntimePattern p $ RuntimePatternVariable x σ', σ'))
  (CoreTermRuntimePattern p (RuntimePatternPair pm1 pm2)) -> do
    (pm1', σ1) <- typeCheckAnnotateRuntimePattern pm1
    (pm2', σ2) <- typeCheckAnnotateRuntimePattern pm2
    pure ((CoreTermRuntimePattern p $ RuntimePatternPair pm1' pm2', CoreType Internal $ Pair σ1 σ2))

typeCheckAnnotateKindPattern :: Pattern KindIdentifier Sort p -> Core p (Pattern KindIdentifier Sort p, Sort)
typeCheckAnnotateKindPattern pm@(Pattern _ _ μ) = pure (pm, μ)

typeCheckValidateKind :: Kind Void p -> Core p (KindUnify, Sort)
typeCheckValidateKind =
  let recurse = typeCheckValidateKind
   in \case
        (CoreKind p (KindVariable x)) -> do
          μ <- lookupSortEnvironment x
          case μ of
            Just (_, μ, _) -> pure (CoreKind Internal $ KindVariable x, μ)
            Nothing -> quit $ UnknownKindIdentifier p x
        (CoreKind _ Type) -> do
          pure (CoreKind Internal $ Type, Kind)
        (CoreKind _ Region) -> pure (CoreKind Internal Region, Kind)
        (CoreKind _ Imaginary) -> pure (CoreKind Internal Imaginary, Existance)
        (CoreKind p (Real κ)) -> do
          (κ', _) <- secondM (checkRepresentation p) =<< recurse κ
          pure (CoreKind Internal (Real κ'), Existance)
        (CoreKind _ (KindRuntime PointerRep)) -> pure (CoreKind Internal $ KindRuntime PointerRep, Representation)
        (CoreKind p (KindRuntime (StructRep κs))) -> do
          (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< recurse) κs
          pure (CoreKind Internal (KindRuntime (StructRep κs')), Representation)
        (CoreKind p (KindRuntime (WordRep κ))) -> do
          (κ', _) <- secondM (checkSize p) =<< recurse κ
          pure (CoreKind Internal (KindRuntime (WordRep κ')), Representation)
        (CoreKind _ (KindSize κ)) -> pure (CoreKind Internal (KindSize κ), Size)
        (CoreKind _ (KindSignedness κ)) -> pure (CoreKind Internal (KindSignedness κ), Signedness)
        CoreKind p (Pretype κ) -> do
          (κ', _) <- secondM (checkExistance p) =<< recurse κ
          pure (CoreKind Internal $ Pretype κ', Kind)
        CoreKind _ (KindLogical v) -> absurd v

typeCheckValidateTypeScheme :: TypeScheme (KindAuto p) Void p p -> Core p (TypeScheme KindUnify TypeLogicalRaw Internal p, KindUnify)
typeCheckValidateTypeScheme =
  let recurse = typeCheckValidateTypeScheme
   in \case
        (CoreTypeScheme p (MonoType σ)) -> do
          (σ', κ) <- typeCheckValidateType σ
          pure (CoreTypeScheme p (MonoType σ'), κ)
        (CoreTypeScheme p (ImplicitForall (Bound pm σ) c)) -> do
          (pm', κ2) <- typeCheckAnnotateTypePattern pm
          c' <- typeCheckConstraints p c κ2
          (σ', κ) <- augmentTypePatternBottom pm' $ recurse σ
          pure $ (CoreTypeScheme p $ ImplicitForall (Bound pm' σ') c', κ)
        (CoreTypeScheme p (ImplicitKindForall (Bound pm σ))) -> do
          pm' <- fst <$> typeCheckAnnotateKindPattern pm
          (σ', _) <- augmentKindPatternBottom pm' $ recurse σ
          pure (CoreTypeScheme p $ ImplicitKindForall $ Bound pm' σ', CoreKind Internal $ Type)

typeCheckAnnotateTypePattern :: Pattern TypeIdentifier (KindAuto p) p -> Core p (Pattern TypeIdentifier KindUnify p, KindUnify)
typeCheckAnnotateTypePattern = \case
  (Pattern p x (Just κ)) -> do
    (κ', μ) <- typeCheckValidateKind κ
    matchSort p μ Kind
    pure (Pattern p x κ', κ')
  (Pattern p x Nothing) -> do
    κ <- freshKindVariable p Kind
    pure (Pattern p x κ, κ)

typeCheckValidateType :: Type (KindAuto p) Void p -> Core p (TypeUnify, KindUnify)
typeCheckValidateType =
  let recurse = typeCheckValidateType
   in \case
        (CoreType p (TypeVariable x)) -> do
          κ <- lookupKindEnvironment x
          case κ of
            Just (_, κ, _, _) -> pure (CoreType Internal (TypeVariable x), κ)
            Nothing -> quit $ UnknownTypeIdentifier p x
        (CoreType p (Macro σ τ)) -> do
          (σ', _) <- secondM (checkType p) =<< recurse σ
          (τ', _) <- secondM (checkType p) =<< recurse τ
          pure (CoreType Internal $ Macro σ' τ', CoreKind Internal $ Type)
        (CoreType p (Forall (Bound pm σ) c)) -> do
          (pm', κ2) <- typeCheckAnnotateTypePattern pm
          c' <- typeCheckConstraints p c κ2
          (σ', κ) <- augmentTypePatternBottom pm' $ recurse σ
          pure $ (CoreType Internal $ Forall (Bound (Internal <$ pm') σ') c', κ)
        (CoreType p (OfCourse σ)) -> do
          (σ', _) <- secondM (checkType p) =<< recurse σ
          pure (CoreType Internal $ OfCourse σ', CoreKind Internal $ Type)
        CoreType p (FunctionPointer σ π τ) -> do
          (σ', _) <- secondM (checkReal p <=< checkPretype p) =<< recurse σ
          (π', _) <- secondM (checkRegion p) =<< recurse π
          (τ', _) <- secondM (checkPretype p) =<< recurse τ
          pure (CoreType Internal $ FunctionPointer σ' π' τ', CoreKind Internal $ Pretype $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ PointerRep)
        CoreType p (FunctionLiteralType σ π τ) -> do
          (σ', _) <- secondM (checkReal p <=< checkPretype p) =<< recurse σ
          (π', _) <- secondM (checkRegion p) =<< recurse π
          (τ', _) <- secondM (checkPretype p) =<< recurse τ
          pure (CoreType Internal $ FunctionLiteralType σ' π' τ', CoreKind Internal $ Type)
        CoreType p (Pair σ τ) -> do
          (σ', ρ1) <- secondM (checkReal p <=< checkPretype p) =<< recurse σ
          (τ', ρ2) <- secondM (checkReal p <=< checkPretype p) =<< recurse τ
          pure (CoreType Internal $ Pair σ' τ', CoreKind Internal $ Pretype $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ StructRep [ρ1, ρ2])
        CoreType p (Effect σ π) -> do
          (σ', _) <- secondM (checkPretype p) =<< recurse σ
          (π', _) <- secondM (checkRegion p) =<< recurse π
          pure (CoreType Internal $ Effect σ' π', CoreKind Internal $ Type)
        CoreType p (Reference π σ) -> do
          (π', _) <- secondM (checkRegion p) =<< recurse π
          (σ', _) <- secondM (checkReal p <=< checkPretype p) =<< recurse σ
          pure (CoreType Internal $ Reference π' σ', CoreKind Internal $ Pretype $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ PointerRep)
        CoreType p (Number ρ1 ρ2) -> do
          ρ1' <- case ρ1 of
            Nothing -> freshKindVariable p Signedness
            Just ρ1 -> fmap fst $ secondM (checkSignedness p) =<< typeCheckValidateKind ρ1
          ρ2' <- case ρ2 of
            Nothing -> freshKindVariable p Size
            Just ρ2 -> fmap fst $ secondM (checkSize p) =<< typeCheckValidateKind ρ2
          pure (CoreType Internal $ Number ρ1' ρ2', CoreKind Internal $ Pretype $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ WordRep ρ2')
        CoreType _ (TypeLogical v) -> absurd v

instantiateTypeScheme p = \case
  (CoreTypeScheme _ (MonoType σ)) -> pure (σ, InstantiateEmpty)
  (CoreTypeScheme _ (ImplicitForall (Bound (Pattern _ x κ) σ) c)) -> do
    τ <- freshTypeVariable p κ
    flip Map.traverseWithKey c $ \k c -> do
      constrain p k τ c
    (ς, θ) <- instantiateTypeScheme p $ substitute τ x σ
    pure (ς, InstantiateType x τ θ)
  (CoreTypeScheme _ (ImplicitKindForall (Bound (Pattern _ x μ) σ))) -> do
    κ <- freshKindVariable p μ
    (ς, θ) <- instantiateTypeScheme p $ substitute κ x σ
    pure (ς, InstantiateKind x κ θ)

expectTypeAnnotation p Nothing = quit $ ExpectedTypeAnnotation p
expectTypeAnnotation _ (Just σ) = pure σ

typeCheckAnnotateLinearTerm :: TermAuto p -> Core p ((TermUnify p, TypeUnify), Use TermIdentifier)
typeCheckAnnotateLinearTerm =
  let recurse = typeCheckAnnotateLinearTerm
   in \case
        (CoreTerm p (TermRuntime (Variable x ()))) -> do
          mσ <- lookupTypeEnviroment x
          case mσ of
            Just (_, _, σ) -> do
              (τ, θ) <- instantiateTypeScheme p σ
              pure ((CoreTerm p $ TermRuntime $ Variable x θ, τ), Use x)
            Nothing -> quit $ UnknownIdentifier p x
        (CoreTerm p (MacroAbstraction (Bound pm e))) -> do
          (pm', σ) <- typeCheckAnnotateMetaPattern pm
          ((e', τ), lΓ) <- augmentMetaTermPattern pm' (recurse e)
          pure ((CoreTerm p (MacroAbstraction (Bound pm' e')), CoreType Internal $ Macro σ τ), lΓ)
        (CoreTerm p (MacroApplication e1 e2 σ'')) -> do
          ((e1', (σ, τ)), lΓ1) <- firstM (secondM (checkMacro p)) =<< recurse e1
          ((e2', σ'), lΓ2) <- recurse e2
          matchType p σ σ'
          case σ'' of
            Nothing -> pure ()
            Just σ'' -> do
              σ'' <- fst <$> typeCheckValidateType σ''
              matchType p σ σ''
          pure ((CoreTerm p (MacroApplication e1' e2' σ), τ), lΓ1 `combine` lΓ2)
        (CoreTerm p (Bind e1 (Bound pm e2))) -> do
          ((e1', τ), lΓ1) <- recurse e1
          (pm', τ') <- typeCheckAnnotateMetaPattern pm
          matchType p τ τ'
          ((e2', σ), lΓ2) <- augmentMetaTermPattern pm' $ recurse e2
          pure ((CoreTerm p (Bind e1' (Bound pm' e2')), σ), lΓ1 `combine` lΓ2)
        (CoreTerm p (OfCourseIntroduction e)) -> do
          ((e', σ), lΓ) <- recurse e
          capture p lΓ
          pure ((CoreTerm p (OfCourseIntroduction e'), CoreType Internal $ OfCourse $ σ), lΓ)
        (CoreTerm p (TypeAbstraction (Bound pm e) c)) -> do
          (pm', κ) <- typeCheckAnnotateTypePattern pm
          c <- (traverse . traverse) (expectTypeAnnotation p) c
          c' <- typeCheckConstraints p c κ
          augmentTypePatternLevel pm' c' $ do
            enterLevel
            ((e', σ'), lΓ) <- typeCheckAnnotateLinearTerm e
            leaveLevel

            θ <- solve
            let σ'' = applySubstitution θ σ'
            let e'' = applySubstitution θ e'

            θ <- removeDeadVariables θ
            reunifyEquations p θ
            ambigousTypeCheck (Map.keysSet $ freeVariablesInternal @TypeLogicalRaw σ'')
            ambigousKindCheck (Map.keysSet $ freeVariablesInternal @KindLogicalRaw σ'')

            pure ((CoreTerm p (TypeAbstraction (Bound pm' e'') c'), CoreType Internal $ Forall (Bound (Internal <$ pm') σ'') Map.empty), lΓ)
        (CoreTerm p (TypeApplication e σ (Bound pm@(Pattern _ α _) τ) c)) -> do
          ((e, ς), lΓ) <- typeCheckAnnotateLinearTerm e
          (pm', κ) <- typeCheckAnnotateTypePattern pm
          c <- (traverse . traverse) (expectTypeAnnotation p) c
          c' <- typeCheckConstraints p c κ
          τ <- expectTypeAnnotation p τ
          (σ, κ') <- case σ of
            Just σ -> typeCheckValidateType σ
            Nothing -> do
              κ <- freshKindVariable p Kind
              σ <- freshTypeVariable p κ
              pure (σ, κ)
          matchKind p κ κ'
          augmentTypePatternBottom pm' $ do
            τ <- fst <$> typeCheckValidateType τ
            matchType p (CoreType Internal $ Forall (Bound (Internal <$ pm') τ) c') ς
            pure (((CoreTerm p (TypeApplication e σ (Bound pm' τ) c')), substitute σ α τ), lΓ)
        CoreTerm p (TermRuntime (Alias e1 (Bound pm e2))) -> do
          (pm', τ) <- typeCheckAnnotateRuntimePattern pm
          ((e1', (τ', π)), lΓ1) <- firstM (secondM $ checkEffect p) =<< recurse e1
          matchType p τ τ'
          ((e2', (σ, π')), lΓ2) <- firstM (secondM $ checkEffect p) =<< augmentRuntimeTermPattern pm' (recurse e2)
          matchType p π π'
          pure ((CoreTerm p $ TermRuntime $ Alias e1' (Bound pm' e2'), CoreType Internal $ Effect σ π), lΓ1 `combine` lΓ2)
        CoreTerm p (TermRuntime (Extern sym σ π τ)) -> do
          σ' <- case σ of
            Nothing -> freshPretypeRealTypeVariable p
            Just σ -> fmap fst $ secondM (checkReal p) =<< secondM (checkPretype p) =<< typeCheckValidateType σ
          π' <- case π of
            Nothing -> freshRegionTypeVariable p
            Just π -> fmap fst $ secondM (checkRegion p) =<< typeCheckValidateType π
          τ' <- case τ of
            Nothing -> freshPretypeTypeVariable p
            Just τ -> fmap fst $ secondM (checkPretype p) =<< typeCheckValidateType τ
          r <- freshRegionTypeVariable p
          pure (((CoreTerm p $ TermRuntime $ Extern sym σ' π' τ'), CoreType Internal $ Effect (CoreType Internal $ FunctionPointer σ' π' τ') r), useNothing)
        CoreTerm p (TermRuntime (FunctionApplication e1 e2 σ'')) -> do
          ((e1', ((σ, π, τ), π')), lΓ1) <- firstM (secondM $ firstM (checkFunctionPointer p) <=< checkEffect p) =<< recurse e1
          matchType p π π'
          ((e2', (σ', π'')), lΓ2) <- firstM (secondM $ checkEffect p) =<< recurse e2
          matchType p π π''
          matchType p σ σ'
          case σ'' of
            Nothing -> pure ()
            Just σ' -> do
              σ' <- fmap fst $ typeCheckValidateType σ'
              matchType p σ σ'
          pure ((CoreTerm p $ TermRuntime $ FunctionApplication e1' e2' σ, CoreType Internal $ Effect τ π), lΓ1 `combine` lΓ2)
        CoreTerm p (TermRuntime (PairIntroduction e1 e2)) -> do
          ((e1', (σ, π)), lΓ1) <- firstM (secondM $ checkEffect p) =<< recurse e1
          ((e2', (τ, π')), lΓ2) <- firstM (secondM $ checkEffect p) =<< recurse e2
          matchType p π π'
          σ <- enforcePretypeReal p σ
          τ <- enforcePretypeReal p τ
          pure ((CoreTerm p $ TermRuntime $ PairIntroduction e1' e2', CoreType Internal $ Effect (CoreType Internal $ Pair σ τ) π), lΓ1 `combine` lΓ2)
        CoreTerm p (TermRuntime (ReadReference e)) -> do
          ((e', ((π, σ), π')), lΓ) <- firstM (secondM $ firstM (checkReference p) <=< checkEffect p) =<< recurse e
          constrain p Copy σ []
          matchType p π π'
          pure ((CoreTerm p $ TermRuntime $ ReadReference e', CoreType Internal $ Effect σ π), lΓ)
        CoreTerm p (TermRuntime (NumberLiteral v)) -> do
          π <- freshRegionTypeVariable p
          ρ1 <- freshKindVariable p Signedness
          ρ2 <- freshKindVariable p Size
          pure ((CoreTerm p (TermRuntime (NumberLiteral v)), CoreType Internal $ Effect (CoreType Internal $ Number ρ1 ρ2) π), useNothing)
        CoreTerm p (TermRuntime (Arithmatic o e1 e2 s)) -> do
          ((e1', ((ρ1, ρ2), π)), lΓ1) <- firstM (secondM $ firstM (checkNumber p) <=< checkEffect p) =<< recurse e1
          ((e2', ((ρ1', ρ2'), π')), lΓ2) <- firstM (secondM $ firstM (checkNumber p) <=< checkEffect p) =<< recurse e2
          matchType p π π'
          matchKind p ρ1 ρ1'
          matchKind p ρ2 ρ2'
          case s of
            Nothing -> pure ()
            Just s -> do
              s <- fmap fst $ typeCheckValidateKind s
              matchKind p ρ1 s
          pure ((CoreTerm p $ TermRuntime $ Arithmatic o e1' e2' ρ1, CoreType Internal $ Effect (CoreType Internal $ Number ρ1 ρ2) π), lΓ1 `combine` lΓ2)
        CoreTerm p (FunctionLiteral (Bound pm e)) -> do
          (pm', σ) <- typeCheckAnnotateRuntimePattern pm
          ((e', (τ, π)), lΓ) <- firstM (secondM $ checkEffect p) =<< augmentRuntimeTermPattern pm' (recurse e)
          pure ((CoreTerm p $ FunctionLiteral (Bound pm' e'), CoreType Internal $ FunctionLiteralType σ π τ), lΓ)

attachRigidType :: [String] -> [TypeLogicalRaw] -> Core p ([(Pattern TypeIdentifier KindUnify Internal, Map Constraint [TypeUnify])], Substitution)
attachRigidType (x : xs) (α : αs) = do
  (_, κ, c, _) <- indexTypeVariableMap α
  (pms, θ) <- attachRigidType xs αs
  pure ((Pattern Internal (TypeIdentifier x) κ, c) : pms, singleTypeSubstitution α (CoreType Internal $ TypeVariable $ TypeIdentifier x) <> θ)
attachRigidType _ [] = pure ([], identitySubstitution)
attachRigidType _ _ = error "empty name generator"

attachRigidKind :: [String] -> [KindLogicalRaw] -> Core p ([Pattern KindIdentifier Sort Internal], Substitution)
attachRigidKind (x : xs) (α : αs) = do
  (_, μ, _) <- indexKindVariableMap α
  (pms, θ) <- attachRigidKind xs αs
  pure (Pattern Internal (KindIdentifier x) μ : pms, singleKindSubstitution α (CoreKind Internal $ KindVariable $ KindIdentifier x) <> θ)
attachRigidKind _ [] = pure ([], identitySubstitution)
attachRigidKind _ _ = error "empty name generator"

class StripUnifier e e' | e -> e' where
  stripUnifier :: e -> e'

instance StripUnifier (TermUnify p) (TermInfer p) where
  stripUnifier = mapTerm stripUnifier stripUnifier stripUnifier id

instance StripUnifier KindUnify (Kind Void Internal) where
  stripUnifier = mapKind errorUnifierKind id

instance StripUnifier TypeUnify TypeInfer where
  stripUnifier = mapType stripUnifier errorUnifierType id

instance StripUnifier (Pattern KindIdentifier Sort Internal) (Pattern KindIdentifier Sort Internal) where
  stripUnifier = id

instance StripUnifier (Pattern TypeIdentifier KindUnify Internal) (Pattern TypeIdentifier (Kind Void Internal) Internal) where
  stripUnifier (Pattern x p κ) = Pattern x p (stripUnifier κ)

instance StripUnifier InstantiationUnify InstantiationInfer where
  stripUnifier (InstantiateType x σ θ) = InstantiateType x (stripUnifier σ) (stripUnifier θ)
  stripUnifier (InstantiateKind x κ θ) = InstantiateKind x (stripUnifier κ) (stripUnifier θ)
  stripUnifier InstantiateEmpty = InstantiateEmpty

instance StripUnifier TypeSchemeUnify TypeSchemeInfer where
  stripUnifier = mapTypeScheme stripUnifier errorUnifierType id id

errorUnifierType :: TypeLogicalRaw -> a
errorUnifierType _ = error "unexpected logic type variable"

errorUnifierKind :: KindLogicalRaw -> a
errorUnifierKind _ = error "unexpected logic kind variable"

typeTemporaries = temporaries' $ (: []) <$> ['A', 'B', 'C']

kindTemporaries = temporaries' $ (: []) <$> ['X', 'Y', 'Z']

augmentScheme (CoreTypeScheme _ (MonoType σ)) e = e σ
augmentScheme (CoreTypeScheme _ (ImplicitForall (Bound pm σ) c)) e = augmentTypePatternLevel pm c (augmentScheme σ e)
augmentScheme (CoreTypeScheme _ (ImplicitKindForall (Bound pm σ))) e = augmentKindPatternLevel pm (augmentScheme σ e)

reunifyEquations p (Substitution σθ κθ) = do
  for (Map.toList σθ) $ \(x, τ) ->
    matchType p (CoreType Internal (TypeLogical x)) τ
  for (Map.toList κθ) $ \(x, κ) ->
    matchKind p (CoreKind Internal (KindLogical x)) κ

removeDeadVariables (Substitution σθ κθ) = do
  lev <- Level <$> currentLevel
  σθ' <- for (Map.toList σθ) $ \(x, τ) -> do
    (_, _, _, lev') <- indexTypeVariableMap x
    if lev' > lev
      then do
        removeTypeVariable x
        pure []
      else pure [(x, τ)]
  κθ' <- for (Map.toList κθ) $ \(x, κ) -> do
    (_, _, lev') <- indexKindVariableMap x
    if lev' > lev
      then do
        removeKindVariable x
        pure []
      else pure [(x, κ)]
  pure $ Substitution (Map.fromList $ concat σθ') (Map.fromList $ concat κθ')

ambigousTypeCheck variables = do
  lev <- Level <$> currentLevel
  vars <- getTypeVariableMap
  for (Map.toList vars) $ \(x, (p, _, _, lev')) -> do
    if lev' > lev
      then do
        if x `Set.notMember` variables
          then do
            quit $ AmbiguousType p x
          else pure ()
      else pure ()

ambigousKindCheck variables = do
  lev <- Level <$> currentLevel
  vars <- getKindVariableMap
  for (Map.toList vars) $ \(x, (p, _, lev')) -> do
    if lev' > lev
      then do
        if x `Set.notMember` variables
          then do
            quit $ AmbiguousKind p x
          else pure ()
      else pure ()

generalize :: (TermUnify p, TypeUnify) -> Core p (TermUnify p, TypeSchemeUnify)
generalize (e, σ) = do
  θ <- solve
  (e, σ) <- pure $ applySubstitution θ (e, σ)
  removeDeadVariables θ

  ambigousTypeCheck (Map.keysSet $ freeVariablesInternal @TypeLogicalRaw σ)
  typeVars <- getTypeVariableMap
  let α = Set.toList $ Map.keysSet typeVars
  -- todo topologically sort type variables here
  (pm, θσ) <- attachRigidType typeTemporaries α

  ambigousKindCheck (Map.keysSet $ freeVariablesInternal @KindLogicalRaw σ <> freeVariablesInternal @KindLogicalRaw (map fst pm))
  kindVars <- getKindVariableMap
  let κα = Set.toList $ Map.keysSet kindVars
  (pm2, θκ) <- attachRigidKind kindTemporaries κα
  (((e, σ), pm), pm2) <- pure $ applySubstitution θκ $ applySubstitution θσ (((e, σ), pm), pm2)
  let ς = foldr prependKindPattern (foldr prependPattern (CoreTypeScheme Internal $ MonoType σ) pm) pm2
  pure (e, ς)
  where
    prependKindPattern pm e = CoreTypeScheme Internal $ ImplicitKindForall (Bound pm e)
    prependPattern (pm, c) e = CoreTypeScheme Internal $ ImplicitForall (Bound pm e) c

typeCheckGlobal ::
  TermAuto p ->
  Core p (TermInfer p, TypeSchemeInfer)
typeCheckGlobal e = do
  enterLevel
  ((e, σ), _) <- typeCheckAnnotateLinearTerm e
  leaveLevel
  (e, ς) <- generalize (e, σ)
  pure (stripUnifier e, stripUnifier ς)

typeCheckGlobalText ::
  TermAuto p ->
  Core p (TermInfer p, TypeSchemeInfer)
typeCheckGlobalText e@(CoreTerm p _) = do
  (e, ς) <- typeCheckGlobal e
  syntaticFunctionCheck p ς
  pure (e, ς)

typeCheckGlobalAnnotate ::
  TermAuto p ->
  TypeScheme (KindAuto p) Void p p ->
  Core p (TermInfer p, TypeSchemeInfer)
typeCheckGlobalAnnotate e@(CoreTerm p _) ς = do
  enterLevel
  ς' <- fst <$> typeCheckValidateTypeScheme ς
  augmentScheme ς' $ \σ -> do
    ((e, σ'), _) <- typeCheckAnnotateLinearTerm e
    matchType p σ σ'
    leaveLevel
    θ <- solve
    e <- pure $ applySubstitution θ e
    ς' <- pure $ applyQSubstitution θ ς'
    _ <- removeDeadVariables θ
    ambigousTypeCheck Set.empty
    ambigousKindCheck Set.empty
    pure (stripUnifier e, stripUnifier (Internal <$ ς'))
  where
    substituteAll = flip . foldr $ \(x, κ) -> substitute κ x
    applyQSubstitution (Substitution _ κs) (CoreTypeScheme p (MonoType σ)) = CoreTypeScheme p $ MonoType $ substituteAll (Map.toList κs) σ
    applyQSubstitution θ@(Substitution _ κs) (CoreTypeScheme p (ImplicitForall (Bound pm ς) c)) =
      CoreTypeScheme p $
        ImplicitForall
          (Bound (substituteAll (Map.toList κs) pm) (applyQSubstitution θ ς))
          (substituteAll (Map.toList κs) c)
    applyQSubstitution θ (CoreTypeScheme p (ImplicitKindForall (Bound pm ς))) = CoreTypeScheme p (ImplicitKindForall (Bound pm $ applyQSubstitution θ ς))

typeCheckGlobalAnnotateText ::
  TermAuto p ->
  TypeScheme (KindAuto p) Void p p ->
  Core p (TermInfer p, TypeSchemeInfer)
typeCheckGlobalAnnotateText e ς@(CoreTypeScheme p _) = do
  (e, ς) <- typeCheckGlobalAnnotate e ς
  syntaticFunctionCheck p ς
  pure (e, ς)

syntaticFunctionCheck _ (CoreTypeScheme _ (MonoType (CoreType _ (FunctionLiteralType _ _ _)))) = pure ()
syntaticFunctionCheck p (CoreTypeScheme _ (ImplicitForall (Bound _ ς) _)) = syntaticFunctionCheck p ς
syntaticFunctionCheck p _ = quit $ ExpectedFunctionLiteral p
