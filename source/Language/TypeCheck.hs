module Language.TypeCheck where

import Control.Monad ((<=<))
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Void
import Environment
import Language.Ast.Common
import Language.Ast.Kind
import Language.Ast.Multiplicity
import Language.Ast.Sort
import Language.Ast.Term
import Language.Ast.Type
import Language.TypeCheck.Core
import Language.TypeCheck.Unify
import Language.TypeCheck.Variable
import qualified Misc.MonoidMap as Map
import Misc.Util (firstM, secondM, temporaries')

augmentTypePatternBottom (Pattern p x κ) = augmentKindEnvironment x p κ (error "level usage during kind checking")

augmentTypePatternLevel (Pattern p x κ) e = do
  lev <- Level <$> currentLevel
  augmentKindEnvironment x p κ lev e

augmentKindPatternBottom (Pattern p x μ) = augmentSortEnvironment x p μ (error "level usage during sort checking")

augmentKindPatternLevel (Pattern p x μ) e = do
  lev <- Level <$> currentLevel
  augmentSortEnvironment x p μ lev e

checkKind p μt = do
  matchSort p μt Kind
  pure ()

checkStage p μt = do
  matchSort p μt Stage
  pure ()

checkExistance p μt = do
  matchSort p μt Existance
  pure ()

checkImpact p μt = do
  matchSort p μt Impact
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
  κ <- freshKindVariable p Stage
  matchKind p κt (CoreKind Internal (Type κ))
  pure κ

checkEvidence p κt = do
  matchKind p κt (CoreKind Internal $ Evidence)

checkRegion p κt = do
  matchKind p κt (CoreKind Internal Region)
  pure ()

checkRuntime p κt = do
  κ <- freshKindVariable p Impact
  κ' <- freshKindVariable p Existance
  matchKind p κt (CoreKind Internal (Runtime κ κ'))
  pure (κ, κ')

checkData p κt = matchKind p κt (CoreKind Internal $ Data)

checkReal p κt = do
  κ <- freshKindVariable p Representation
  matchKind p κt (CoreKind Internal $ Real κ)
  pure κ

checkTypeRT p κt = do
  (κ, κ') <- checkRuntime p =<< checkType p κt
  checkData p κ
  checkReal p κ'

makeTypeRT κt = CoreKind Internal $ Type $ CoreKind Internal $ Runtime (CoreKind Internal Data) $ CoreKind Internal $ Real κt

freshTypeVariable p κ = (CoreType Internal . TypeLogical) <$> freshTypeVariableRaw p κ

freshKindVariable p μ = (CoreKind Internal . KindLogical) <$> freshKindVariableRaw p μ

freshMetaTypeVariable p = do
  s <- freshKindVariable p Stage
  freshTypeVariable p (CoreKind Internal (Type s))

freshRuntimeTypeVariable p = do
  s <- freshKindVariable p Impact
  s' <- freshKindVariable p Existance
  freshTypeVariable p $ CoreKind Internal $ Type $ CoreKind Internal $ Runtime s s'

freshRTTypeVariable p = do
  s <- freshKindVariable p Representation
  freshTypeVariable p $ CoreKind Internal $ Type $ CoreKind Internal $ Runtime (CoreKind Internal Data) $ CoreKind Internal $ Real s

enforceRT p σt = do
  σ <- freshRTTypeVariable p
  matchType p σt σ
  -- todo rework this
  -- can't return σt reconstruction needs to destructure σ's kind
  pure σ

enforceRuntime p σt = do
  σ <- freshRuntimeTypeVariable p
  matchType p σt σ
  pure σ

enforceEvidence p σt = do
  σ <- freshTypeVariable p $ CoreKind Internal $ Type $ CoreKind Internal Evidence
  matchType p σt σ
  pure σ

freshRegionTypeVariable p = do
  freshTypeVariable p $ CoreKind Internal $ Region

checkMacro p σt = do
  σ <- freshMetaTypeVariable p
  τ <- freshMetaTypeVariable p
  matchType p σt (CoreType Internal (Macro σ τ))
  pure (σ, τ)

checkImplied p σt = do
  σ <- freshTypeVariable p (CoreKind Internal $ Type $ CoreKind Internal Evidence)
  τ <- freshMetaTypeVariable p
  matchType p σt (CoreType Internal (Implied σ τ))
  pure (σ, τ)

checkFunctionPointer p σt = do
  σ <- freshRTTypeVariable p
  τ <- freshRuntimeTypeVariable p
  matchType p σt (CoreType Internal $ FunctionPointer σ τ)
  pure (σ, τ)

checkFunctionLiteralType p σt = do
  σ <- freshRTTypeVariable p
  τ <- freshRuntimeTypeVariable p
  matchType p σt (CoreType Internal $ FunctionLiteralType σ τ)
  pure (σ, τ)

checkRegionReference p σt = do
  π <- freshRegionTypeVariable p
  σ <- freshRTTypeVariable p
  matchType p σt (CoreType Internal $ RegionReference π σ)
  pure (π, σ)

checkRegionTransformer p σt = do
  π <- freshRegionTypeVariable p
  κ <- freshKindVariable p Existance
  σ <- freshTypeVariable p $ CoreKind Internal $ Type $ CoreKind Internal $ Runtime (CoreKind Internal Data) κ
  matchType p σt (CoreType Internal $ RegionTransformer π σ)
  pure (π, σ)

checkCopy p σt = do
  σ <- freshRTTypeVariable p
  matchType p σt (CoreType Internal $ Copy σ)
  pure σ

checkNumber p σt = do
  ρ1 <- freshKindVariable p Signedness
  ρ2 <- freshKindVariable p Size
  matchType p σt (CoreType Internal $ Number ρ1 ρ2)
  pure (ρ1, ρ2)

augmentVariableLinear p x l σ e = do
  (σ', lΓ) <- augmentTypeEnvironment x p l (CoreTypeScheme Internal $ MonoType σ) e
  case (count x lΓ, l) of
    (Single, _) -> pure ()
    (_, Unrestricted) -> pure ()
    (_, _) -> quit $ InvalidUsage p x
  pure (σ', Remove x lΓ)

augmentTermPattern l pm = go l pm
  where
    go l (CoreTermPattern p (PatternCommon (PatternVariable x σ))) = augmentVariableLinear p x l σ
    go _ (CoreTermPattern _ (PatternCommon (RuntimePatternPair pm pm'))) = go Linear pm . go Linear pm'
    go _ (CoreTermPattern _ (PatternCopy _ pm)) = go Unrestricted pm
    go _ (CoreTermPattern _ (PatternOfCourse pm)) = go Unrestricted pm

capture p lΓ = do
  let captures = variablesUsed lΓ
  for (Set.toList captures) $ \x -> do
    (_, l, _) <- fromJust <$> lookupTypeEnviroment x
    case l of
      Unrestricted -> pure ()
      Linear -> quit $ CaptureLinear p x
  pure ()

typeCheckAnnotateMetaPattern (CoreTermPattern p (PatternCommon (PatternVariable x σ))) = do
  σ' <- case σ of
    Nothing -> freshMetaTypeVariable p
    Just σ -> do
      (σ', κ) <- typeCheckValidateType σ
      checkType p κ
      pure σ'
  pure (CoreTermPattern p $ PatternCommon $ (PatternVariable x σ'), σ')
typeCheckAnnotateMetaPattern (CoreTermPattern p (PatternOfCourse pm)) = do
  (pm', σ) <- typeCheckAnnotateMetaPattern pm
  pure (CoreTermPattern p (PatternOfCourse pm'), CoreType Internal (OfCourse σ))
typeCheckAnnotateMetaPattern (CoreTermPattern p _) = quit $ ExpectedMetaPattern p

typeCheckAnnotateLinearPatternRuntime (CoreTermPattern p (PatternCommon (PatternVariable x σ))) = do
  σ' <- case σ of
    Nothing -> freshRTTypeVariable p
    Just σ -> do
      σ' <- fst <$> typeCheckValidateType σ
      enforceRT p σ'
  pure ((CoreTermPattern p $ PatternCommon $ PatternVariable x σ', σ'), useNothing)
typeCheckAnnotateLinearPatternRuntime (CoreTermPattern p (PatternCommon (RuntimePatternPair pm1 pm2))) = do
  ((pm1', σ1), lΓ1) <- typeCheckAnnotateLinearPatternRuntime pm1
  ((pm2', σ2), lΓ2) <- typeCheckAnnotateLinearPatternRuntime pm2
  pure ((CoreTermPattern p $ PatternCommon $ RuntimePatternPair pm1' pm2', CoreType Internal $ RuntimePair σ1 σ2), combine lΓ1 lΓ2)
typeCheckAnnotateLinearPatternRuntime (CoreTermPattern p (PatternCopy e pm)) = do
  ((e', π), lΓ1) <- typeCheckAnnotateLinearTerm e
  ((pm', σ), lΓ2) <- typeCheckAnnotateLinearPatternRuntime pm
  matchType p π (CoreType Internal $ Copy σ)
  pure ((CoreTermPattern p $ PatternCopy e' pm', σ), lΓ1 `combine` lΓ2)
typeCheckAnnotateLinearPatternRuntime (CoreTermPattern p _) = quit $ ExpectedRuntimePattern p

typeCheckAnnotateTypePattern :: Pattern TypeIdentifier (KindAuto p) p -> Core p (Pattern TypeIdentifier KindUnify p, KindUnify)
typeCheckAnnotateTypePattern = typeCheckAnnotate
  where
    typeCheckAnnotate :: Pattern TypeIdentifier (KindAuto p) p -> Core p (Pattern TypeIdentifier KindUnify p, KindUnify)
    typeCheckAnnotate (Pattern p x (Just κ)) = do
      (κ', μ) <- typeCheckValidateKind κ
      matchSort p μ Kind
      pure (Pattern p x κ', κ')
    typeCheckAnnotate (Pattern p x Nothing) = do
      κ <- freshKindVariable p Kind
      pure (Pattern p x κ, κ)

typeCheckAnnotateKindPattern :: Pattern KindIdentifier Sort p -> Core p (Pattern KindIdentifier Sort p, Sort)
typeCheckAnnotateKindPattern = typeCheckAnnotate
  where
    typeCheckAnnotate pm@(Pattern _ _ μ) = pure (pm, μ)

typeCheckValidateTypeScheme :: TypeScheme (KindAuto p) Void p p -> Core p (TypeScheme KindUnify TypeLogicalRaw Internal p, KindUnify)
typeCheckValidateTypeScheme = typeCheckValidate
  where
    typeCheckValidate (CoreTypeScheme p (MonoType σ)) = do
      (σ', κ) <- typeCheckValidateType σ
      pure (CoreTypeScheme p (MonoType σ'), κ)
    typeCheckValidate (CoreTypeScheme p (Forall (Bound pm σ))) = do
      pm' <- fst <$> typeCheckAnnotateTypePattern pm
      (σ', κ) <- augmentTypePatternBottom pm' $ typeCheckValidate σ
      pure $ (CoreTypeScheme p $ Forall $ Bound pm' σ', κ)
    typeCheckValidate (CoreTypeScheme p (KindForall (Bound pm σ))) = do
      pm' <- fst <$> typeCheckAnnotateKindPattern pm
      (σ', _) <- augmentKindPatternBottom pm' $ typeCheckValidate σ
      pure (CoreTypeScheme p $ KindForall $ Bound pm' σ', CoreKind Internal $ Type $ CoreKind Internal Meta)

typeCheckValidateType :: Type (KindAuto p) Void p -> Core p (TypeUnify, KindUnify)
typeCheckValidateType = typeCheckValidate
  where
    typeCheckValidate (CoreType p (TypeVariable x)) = do
      κ <- lookupKindEnvironment x
      case κ of
        Just (_, κ, _) -> pure (CoreType Internal (TypeVariable x), κ)
        Nothing -> quit $ UnknownTypeIdentifier p x
    typeCheckValidate (CoreType p (Macro σ τ)) = do
      (σ', _) <- secondM (checkType p) =<< typeCheckValidate σ
      (τ', _) <- secondM (checkType p) =<< typeCheckValidate τ
      pure (CoreType Internal $ Macro σ' τ', CoreKind Internal $ Type $ CoreKind Internal Meta)
    typeCheckValidate (CoreType _ (ExplicitForall (Bound pm σ))) = do
      pm' <- fst <$> typeCheckAnnotateTypePattern pm
      (σ', κ) <- augmentTypePatternBottom pm' $ typeCheckValidate σ
      pure $ (CoreType Internal $ ExplicitForall $ Bound (Internal <$ pm') σ', κ)
    typeCheckValidate (CoreType p (Implied σ τ)) = do
      (σ', _) <- secondM (checkEvidence p <=< checkType p) =<< typeCheckValidate σ
      (τ', κ) <- secondM (checkType p) =<< typeCheckValidate τ
      pure (CoreType Internal $ Implied σ' τ', CoreKind Internal $ Type κ)
    typeCheckValidate (CoreType p (OfCourse σ)) = do
      (σ', _) <- secondM (checkType p) =<< typeCheckValidate σ
      pure (CoreType Internal $ OfCourse σ', CoreKind Internal $ Type $ CoreKind Internal Meta)
    typeCheckValidate (CoreType p (FunctionPointer σ τ)) = do
      (σ', _) <- secondM (checkTypeRT p) =<< typeCheckValidate σ
      (τ', _) <- secondM (checkRuntime p <=< checkType p) =<< typeCheckValidate τ
      pure (CoreType Internal $ FunctionPointer σ' τ', makeTypeRT $ CoreKind Internal (KindRuntime $ PointerRep))
    typeCheckValidate (CoreType p (FunctionLiteralType σ τ)) = do
      (σ', _) <- secondM (checkTypeRT p) =<< typeCheckValidate σ
      (τ', _) <- secondM (checkRuntime p <=< checkType p) =<< typeCheckValidate τ
      pure (CoreType Internal $ FunctionLiteralType σ' τ', CoreKind Internal $ Type $ CoreKind Internal Text)
    typeCheckValidate (CoreType p (Copy σ)) = do
      (σ', _) <- secondM (checkTypeRT p) =<< typeCheckValidate σ
      pure (CoreType Internal $ Copy σ', CoreKind Internal $ Type $ CoreKind Internal $ Evidence)
    typeCheckValidate (CoreType p (RuntimePair σ τ)) = do
      (σ', κ) <- secondM (checkTypeRT p) =<< typeCheckValidate σ
      (τ', κ') <- secondM (checkTypeRT p) =<< typeCheckValidate τ
      pure (CoreType Internal $ RuntimePair σ' τ', makeTypeRT $ CoreKind Internal $ KindRuntime $ StructRep [κ, κ'])
    typeCheckValidate (CoreType p (RegionTransformer π σ)) = do
      (π', _) <- secondM (checkRegion p) =<< typeCheckValidate π
      (σ', ((), κ)) <- secondM (firstM (checkData p) <=< checkRuntime p <=< checkType p) =<< typeCheckValidate σ
      pure (CoreType Internal $ RegionTransformer π' σ', CoreKind Internal $ Type $ CoreKind Internal $ Runtime (CoreKind Internal Code) κ)
    typeCheckValidate (CoreType p (RegionReference π σ)) = do
      (π', _) <- secondM (checkRegion p) =<< typeCheckValidate π
      (σ', _) <- secondM (checkTypeRT p) =<< typeCheckValidate σ
      pure (CoreType Internal $ RegionReference π' σ', makeTypeRT (CoreKind Internal $ KindRuntime PointerRep))
    typeCheckValidate (CoreType p (Number ρ1 ρ2)) = do
      ρ1' <- case ρ1 of
        Just ρ1 -> fst <$> (secondM (checkSignedness p) =<< typeCheckValidateKind ρ1)
        Nothing -> freshKindVariable p Signedness
      ρ2' <- case ρ2 of
        Just ρ2 -> fst <$> (secondM (checkSize p) =<< typeCheckValidateKind ρ2)
        Nothing -> freshKindVariable p Size
      pure
        ( CoreType Internal $ Number ρ1' ρ2',
          CoreKind Internal $
            Type $
              CoreKind Internal $
                Runtime (CoreKind Internal Data) $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ WordRep ρ2'
        )
    typeCheckValidate (CoreType _ (TypeLogical v)) = absurd v

typeCheckValidateKind :: Kind Void p -> Core p (KindUnify, Sort)
typeCheckValidateKind = typeCheckValidate
  where
    typeCheckValidate (CoreKind p (KindVariable x)) = do
      μ <- lookupSortEnvironment x
      case μ of
        Just (_, μ, _) -> pure (CoreKind Internal $ KindVariable x, μ)
        Nothing -> quit $ UnknownKindIdentifier p x
    typeCheckValidate (CoreKind p (Type κ)) = do
      (κ', _) <- secondM (checkStage p) =<< typeCheckValidate κ
      pure (CoreKind Internal $ Type κ', Kind)
    typeCheckValidate (CoreKind _ Evidence) = pure (CoreKind Internal $ Evidence, Stage)
    typeCheckValidate (CoreKind _ Region) = pure (CoreKind Internal Region, Kind)
    typeCheckValidate (CoreKind _ Meta) = pure (CoreKind Internal Meta, Stage)
    typeCheckValidate (CoreKind _ Text) = pure (CoreKind Internal Text, Stage)
    typeCheckValidate (CoreKind p (Runtime κ1 κ2)) = do
      (κ1', _) <- secondM (checkImpact p) =<< typeCheckValidate κ1
      (κ2', _) <- secondM (checkExistance p) =<< typeCheckValidate κ2
      pure (CoreKind Internal (Runtime κ1' κ2'), Stage)
    typeCheckValidate (CoreKind _ Code) = pure (CoreKind Internal Code, Impact)
    typeCheckValidate (CoreKind _ Data) = pure (CoreKind Internal Data, Impact)
    typeCheckValidate (CoreKind _ Imaginary) = pure (CoreKind Internal Imaginary, Existance)
    typeCheckValidate (CoreKind p (Real κ)) = do
      (κ', _) <- secondM (checkRepresentation p) =<< typeCheckValidate κ
      pure (CoreKind Internal (Real κ'), Existance)
    typeCheckValidate (CoreKind _ (KindRuntime PointerRep)) = pure (CoreKind Internal $ KindRuntime PointerRep, Representation)
    typeCheckValidate (CoreKind p (KindRuntime (StructRep κs))) = do
      (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< typeCheckValidate) κs
      pure (CoreKind Internal (KindRuntime (StructRep κs')), Representation)
    typeCheckValidate (CoreKind p (KindRuntime (WordRep κ))) = do
      (κ', _) <- secondM (checkSize p) =<< typeCheckValidate κ
      pure (CoreKind Internal (KindRuntime (WordRep κ')), Representation)
    typeCheckValidate (CoreKind _ (KindSize κ)) = pure (CoreKind Internal (KindSize κ), Size)
    typeCheckValidate (CoreKind _ (KindSignedness κ)) = pure (CoreKind Internal (KindSignedness κ), Signedness)
    typeCheckValidate (CoreKind _ (KindLogical v)) = absurd v

instantiateTypeScheme _ (CoreTypeScheme _ (MonoType σ)) = pure (σ, InstantiateEmpty)
instantiateTypeScheme p (CoreTypeScheme _ (Forall (Bound (Pattern _ x κ) σ))) = do
  τ <- freshTypeVariable p κ
  (ς, θ) <- instantiateTypeScheme p $ substitute τ x σ
  pure (ς, InstantiateType x τ θ)
instantiateTypeScheme p (CoreTypeScheme _ (KindForall (Bound (Pattern _ x μ) σ))) = do
  κ <- freshKindVariable p μ
  (ς, θ) <- instantiateTypeScheme p $ substitute κ x σ
  pure (ς, InstantiateKind x κ θ)

typeCheckAnnotateLinearTerm :: TermAuto p -> Core p ((TermUnify p, TypeUnify), Use TermIdentifier)
typeCheckAnnotateLinearTerm = typeCheckAnnotateLinear
  where
    typeCheckAnnotateLinear :: TermAuto p -> Core p ((TermUnify p, TypeUnify), Use TermIdentifier)
    typeCheckAnnotateLinear (CoreTerm p (TermRuntime (Variable x ()))) = do
      mσ <- lookupTypeEnviroment x
      case mσ of
        Just (_, _, σ) -> do
          (τ, θ) <- instantiateTypeScheme p σ
          pure ((CoreTerm p $ TermRuntime $ Variable x θ, τ), Use x)
        Nothing -> quit $ UnknownIdentifier p x
    typeCheckAnnotateLinear (CoreTerm p (MacroAbstraction (Bound pm e))) = do
      (pm', σ) <- typeCheckAnnotateMetaPattern pm
      ((e', τ), lΓ) <- augmentTermPattern Linear pm' (typeCheckAnnotateLinear e)
      pure ((CoreTerm p (MacroAbstraction (Bound pm' e')), CoreType Internal $ Macro σ τ), lΓ)
    typeCheckAnnotateLinear (CoreTerm p (MacroApplication e1 e2)) = do
      ((e1', (σ, τ)), lΓ1) <- firstM (secondM (checkMacro p)) =<< typeCheckAnnotateLinear e1
      ((e2', σ'), lΓ2) <- typeCheckAnnotateLinear e2
      matchType p σ σ'
      pure ((CoreTerm p (MacroApplication e1' e2'), τ), lΓ1 `combine` lΓ2)
    typeCheckAnnotateLinear (CoreTerm p (ImplicationAbstraction (Bound pm e))) = do
      (pm', σ) <- typeCheckAnnotateMetaPattern pm
      σ <- enforceEvidence p σ
      ((e', τ), lΓ) <- augmentTermPattern Unrestricted pm' (typeCheckAnnotateLinear e)
      pure ((CoreTerm p (ImplicationAbstraction (Bound pm' e')), CoreType Internal $ Implied σ τ), lΓ)
    typeCheckAnnotateLinear (CoreTerm p (ImplicationApplication e1 e2)) = do
      ((e1', (σ, τ)), lΓ1) <- firstM (secondM (checkImplied p)) =<< typeCheckAnnotateLinear e1
      ((e2', σ'), lΓ2) <- typeCheckAnnotateLinear e2
      matchType p σ σ'
      pure ((CoreTerm p (ImplicationApplication e1' e2'), τ), lΓ1 `combine` lΓ2)
    typeCheckAnnotateLinear (CoreTerm p (TermRuntime (Alias e1 (Bound pm e2)))) = do
      ((e1', τ), lΓ1) <- typeCheckAnnotateLinear e1
      ((pm', τ'), lΓ3) <- typeCheckAnnotateLinearPatternRuntime pm
      matchType p τ τ'
      ((e2', σ), lΓ2) <- augmentTermPattern Linear pm' (typeCheckAnnotateLinear e2)
      σ <- enforceRuntime p σ
      pure ((CoreTerm p (TermRuntime (Alias e1' (Bound pm' e2'))), σ), lΓ1 `combine` lΓ2 `combine` lΓ3)
    typeCheckAnnotateLinear (CoreTerm p (TermRuntime (Extern sym τ σ))) = do
      τ' <- case τ of
        Nothing -> freshRTTypeVariable p
        Just τ -> do
          τ <- (fst <$> typeCheckValidateType τ) >>= enforceRT p
          pure τ
      σ' <- case σ of
        Nothing -> freshRuntimeTypeVariable p
        Just σ -> do
          σ <- (fst <$> typeCheckValidateType σ) >>= enforceRuntime p
          pure σ
      pure ((CoreTerm p (TermRuntime (Extern sym τ' σ')), CoreType Internal $ FunctionPointer τ' σ'), useNothing)
    typeCheckAnnotateLinear (CoreTerm p (TermRuntime (FunctionApplication e1 e2 τ'))) = do
      ((e1', (σ, τ)), lΓ1) <- firstM (secondM (checkFunctionPointer p)) =<< typeCheckAnnotateLinear e1
      ((e2', σ'), lΓ2) <- typeCheckAnnotateLinear e2
      matchType p σ σ'
      case τ' of
        Nothing -> pure ()
        Just τ' -> do
          τ'' <- fst <$> typeCheckValidateType τ'
          matchType p τ τ''
      pure ((CoreTerm p $ TermRuntime $ FunctionApplication e1' e2' τ, τ), lΓ1 `combine` lΓ2)
    typeCheckAnnotateLinear (CoreTerm p (TermRuntime (FunctionLiteral (Bound pm e)))) = do
      ((pm', σ), lΓ1) <- typeCheckAnnotateLinearPatternRuntime pm
      ((e', τ), lΓ2) <- augmentTermPattern Linear pm' (typeCheckAnnotateLinear e)
      τ <- enforceRuntime p τ
      pure ((CoreTerm p $ TermRuntime $ FunctionLiteral $ Bound pm' e', CoreType Internal $ FunctionLiteralType σ τ), lΓ1 `combine` lΓ2)
    typeCheckAnnotateLinear (CoreTerm p (TermRuntime (ReadReference ev e σ''))) = do
      ((e', (π, σ)), lΓ1) <- firstM (secondM (checkRegionReference p)) =<< typeCheckAnnotateLinear e
      ((ev', σ'), lΓ2) <- firstM (secondM (checkCopy p)) =<< typeCheckAnnotateLinear ev
      matchType p σ σ'
      case σ'' of
        Nothing -> pure ()
        Just σ'' -> do
          σ''' <- fst <$> typeCheckValidateType σ''
          matchType p σ σ'''
      pure ((CoreTerm p (TermRuntime (ReadReference ev' e' σ)), CoreType Internal (RegionTransformer π σ)), lΓ1 `combine` lΓ2)
    typeCheckAnnotateLinear (CoreTerm p (OfCourseIntroduction e)) = do
      ((e', σ), lΓ) <- typeCheckAnnotateLinear e
      capture p lΓ
      pure ((CoreTerm p (OfCourseIntroduction e'), CoreType Internal $ OfCourse $ σ), lΓ)
    typeCheckAnnotateLinear (CoreTerm p (Bind e1 (Bound pm e2))) = do
      ((e1', τ), lΓ1) <- typeCheckAnnotateLinear e1
      (pm', τ') <- typeCheckAnnotateMetaPattern pm
      matchType p τ τ'
      ((e2', σ), lΓ2) <- augmentTermPattern Linear pm' $ typeCheckAnnotateLinear e2
      pure ((CoreTerm p (Bind e1' (Bound pm' e2')), σ), lΓ1 `combine` lΓ2)
    typeCheckAnnotateLinear (CoreTerm p (TermRuntime (RuntimePairIntroduction e1 e2))) = do
      ((e1', σ), lΓ1) <- typeCheckAnnotateLinear e1
      ((e2', τ), lΓ2) <- typeCheckAnnotateLinear e2
      σ <- enforceRT p σ
      τ <- enforceRT p τ
      pure ((CoreTerm p (TermRuntime (RuntimePairIntroduction e1' e2')), CoreType Internal (RuntimePair σ τ)), lΓ1 `combine` lΓ2)
    typeCheckAnnotateLinear (CoreTerm p (PureRegionTransformer e)) = do
      ((e', σ), lΓ) <- typeCheckAnnotateLinear e
      σ <- enforceRT p σ
      π <- freshRegionTypeVariable p
      pure ((CoreTerm p $ PureRegionTransformer e', CoreType Internal $ RegionTransformer π σ), lΓ)
    typeCheckAnnotateLinear (CoreTerm p (DoRegionTransformer e1 (Bound pm e2))) = do
      ((e1', (π, σ)), lΓ1) <- firstM (secondM (checkRegionTransformer p)) =<< typeCheckAnnotateLinear e1
      ((pm', σ'), lΓ2) <- typeCheckAnnotateLinearPatternRuntime pm
      matchType p σ σ'
      ((e2', (π', τ)), lΓ3) <- firstM (secondM (checkRegionTransformer p)) =<< augmentTermPattern Linear pm' (typeCheckAnnotateLinear e2)
      matchType p π π'
      pure ((CoreTerm p $ DoRegionTransformer e1' (Bound pm' e2'), CoreType Internal $ RegionTransformer π τ), lΓ1 `combine` lΓ2 `combine` lΓ3)
    typeCheckAnnotateLinear (CoreTerm p ProofCopyNumber) = do
      ρ1 <- freshKindVariable p Signedness
      ρ2 <- freshKindVariable p Size
      pure ((CoreTerm p ProofCopyNumber, CoreType Internal $ Copy $ CoreType Internal $ Number ρ1 ρ2), useNothing)
    typeCheckAnnotateLinear (CoreTerm p ProofCopyFunction) = do
      σ <- freshRTTypeVariable p
      τ <- freshRuntimeTypeVariable p
      pure ((CoreTerm p ProofCopyFunction, CoreType Internal $ Copy (CoreType Internal $ FunctionPointer σ τ)), useNothing)
    typeCheckAnnotateLinear (CoreTerm p (ProofCopyPair e1 e2)) = do
      ((e1', σ), lΓ1) <- firstM (secondM $ checkCopy p) =<< typeCheckAnnotateLinear e1
      ((e2', τ), lΓ2) <- firstM (secondM $ checkCopy p) =<< typeCheckAnnotateLinear e2
      pure ((CoreTerm p $ ProofCopyPair e1' e2', CoreType Internal $ Copy (CoreType Internal $ RuntimePair σ τ)), lΓ1 `combine` lΓ2)
    typeCheckAnnotateLinear (CoreTerm p ProofCopyReference) = do
      π <- freshRegionTypeVariable p
      σ <- freshRTTypeVariable p
      pure ((CoreTerm p ProofCopyReference, CoreType Internal $ Copy $ CoreType Internal $ RegionReference π σ), useNothing)
    typeCheckAnnotateLinear (CoreTerm p (TermRuntime (NumberLiteral n σ'))) = do
      ρ1 <- freshKindVariable p Signedness
      ρ2 <- freshKindVariable p Size
      let σ = CoreType Internal $ Number ρ1 ρ2
      case σ' of
        Nothing -> pure ()
        Just σ' -> do
          σ'' <- fst <$> typeCheckValidateType σ'
          matchType p σ σ''
      pure ((CoreTerm p $ TermRuntime $ NumberLiteral n σ, σ), useNothing)
    typeCheckAnnotateLinear (CoreTerm p (TermRuntime (Arithmatic o e1 e2 κ'))) = do
      κ <- freshKindVariable p Signedness
      case κ' of
        Nothing -> pure ()
        Just κ' -> do
          κ'' <- fst <$> typeCheckValidateKind κ'
          matchKind p κ κ''
      ((e1', (ρ1, ρ2)), lΓ1) <- firstM (secondM $ checkNumber p) =<< typeCheckAnnotateLinear e1
      ((e2', (ρ1', ρ2')), lΓ2) <- firstM (secondM $ checkNumber p) =<< typeCheckAnnotateLinear e2
      matchKind p κ ρ1
      matchKind p ρ1 ρ1'
      matchKind p ρ2 ρ2'
      pure ((CoreTerm p $ TermRuntime (Arithmatic o e1' e2' κ), CoreType Internal $ Number ρ1 ρ2), lΓ1 `combine` lΓ2)
    typeCheckAnnotateLinear (CoreTerm p (TypeAbstraction (Bound pm (σ, e)))) = do
      pm' <- fst <$> typeCheckAnnotateTypePattern pm
      case σ of
        Nothing -> quit $ ExpectedTypeAnnotation p
        Just σ -> augmentTypePatternLevel pm' $ do
          enterLevel
          σ <- fst <$> typeCheckValidateType σ
          ((e', σ'), lΓ) <- typeCheckAnnotateLinearTerm e
          matchType p σ σ'
          leaveLevel

          θ <- solveType
          let σ'' = applySubstitution θ σ'
          let e'' = applySubstitution θ e'

          θ <- removeDeadTypeVariables θ
          reunifyTypeEquations p θ
          ambigousTypeCheck (Set.empty)

          pure ((CoreTerm p (TypeAbstraction (Bound pm' (σ'', e''))), CoreType Internal $ ExplicitForall (Bound (Internal <$ pm') σ'')), lΓ)
    typeCheckAnnotateLinear (CoreTerm p (TypeApplication (e, (σ, (Bound pm@(Pattern _ α _) τ))))) = do
      ((e, ς), lΓ) <- typeCheckAnnotateLinearTerm e
      (pm', κ) <- typeCheckAnnotateTypePattern pm
      case τ of
        Nothing -> quit $ ExpectedTypeAnnotation p
        Just τ -> do
          (σ, κ') <- case σ of
            Just σ -> typeCheckValidateType σ
            Nothing -> do
              κ <- freshKindVariable p Kind
              σ <- freshTypeVariable p κ
              pure (σ, κ)
          matchKind p κ κ'
          augmentTypePatternBottom pm' $ do
            τ <- fst <$> typeCheckValidateType τ
            matchType p (CoreType Internal $ ExplicitForall (Bound (Internal <$ pm') τ)) ς
            pure ((CoreTerm p (TypeApplication (e, (σ, (Bound pm' τ)))), substitute σ α τ), lΓ)

attachRigidType :: [String] -> [TypeLogicalRaw] -> Core p ([Pattern TypeIdentifier KindUnify Internal], Substitution TypeLogicalRaw TypeUnify)
attachRigidType (x : xs) (α : αs) = do
  (_, κ, _) <- indexTypeVariableMap α
  (pms, θ) <- attachRigidType xs αs
  pure (Pattern Internal (TypeIdentifier x) κ : pms, singleSubstitution α (CoreType Internal $ TypeVariable $ TypeIdentifier x) <> θ)
attachRigidType _ [] = pure ([], identitySubstitution)
attachRigidType _ _ = error "empty name generator"

attachRigidKind :: [String] -> [KindLogicalRaw] -> Core p ([Pattern KindIdentifier Sort Internal], Substitution KindLogicalRaw KindUnify)
attachRigidKind (x : xs) (α : αs) = do
  (_, μ, _) <- indexKindVariableMap α
  (pms, θ) <- attachRigidKind xs αs
  pure (Pattern Internal (KindIdentifier x) μ : pms, singleSubstitution α (CoreKind Internal $ KindVariable $ KindIdentifier x) <> θ)
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
augmentScheme (CoreTypeScheme _ (Forall (Bound pm σ))) e = augmentTypePatternLevel pm (augmentScheme σ e)
augmentScheme (CoreTypeScheme _ (KindForall (Bound pm σ))) e = augmentKindPatternLevel pm (augmentScheme σ e)

reunifyTypeEquations p (Substitution answers) =
  for (Map.toList answers) $ \(x, τ) -> do
    matchType p (CoreType Internal (TypeLogical x)) τ

removeDeadTypeVariables (Substitution answers) = do
  lev <- Level <$> currentLevel
  answers' <- for (Map.toList answers) $ \(x, τ) -> do
    (_, _, lev') <- indexTypeVariableMap x
    if lev' > lev
      then do
        removeTypeVariable x
        pure []
      else pure [(x, τ)]
  pure $ Substitution $ Map.fromList $ concat answers'

ambigousTypeCheck variables = do
  lev <- Level <$> currentLevel
  vars <- getTypeVariableMap
  for (Map.toList vars) $ \(x, (p, _, lev')) -> do
    if lev' > lev
      then do
        if x `Set.notMember` variables
          then do
            quit $ AmbiguousType p x
          else pure ()
      else pure ()

removeDeadKindVariables (Substitution answers) = do
  lev <- Level <$> currentLevel
  answers' <- for (Map.toList answers) $ \(x, κ) -> do
    (_, _, lev') <- indexKindVariableMap x
    if lev' > lev
      then do
        removeKindVariable x
        pure []
      else pure [(x, κ)]
  pure $ Substitution $ Map.fromList $ concat answers'

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
  θ <- solveType
  (e, σ) <- pure $ applySubstitution θ (e, σ)
  _ <- removeDeadTypeVariables θ
  ambigousTypeCheck (Map.keysSet $ freeVariablesInternal @TypeLogicalRaw σ)

  typeVars <- getTypeVariableMap
  let α = Set.toList $ Map.keysSet typeVars
  (pm, θσ) <- attachRigidType typeTemporaries α

  θ <- solveKind
  ((e, σ), pm) <- pure $ applySubstitution θ ((e, σ), pm)
  _ <- removeDeadKindVariables θ
  ambigousKindCheck (Map.keysSet $ freeVariablesInternal @KindLogicalRaw σ <> freeVariablesInternal @KindLogicalRaw pm)

  kindVars <- getKindVariableMap
  let κα = Set.toList $ Map.keysSet kindVars
  (pm2, θκ) <- attachRigidKind kindTemporaries κα

  (((e, σ), pm), pm2) <- pure $ applySubstitution θσ $ applySubstitution θκ (((e, σ), pm), pm2)
  let ς = foldr prependKindPattern (foldr prependPattern (CoreTypeScheme Internal $ MonoType σ) pm) pm2
  pure (e, ς)
  where
    prependKindPattern pm = CoreTypeScheme Internal . KindForall . Bound pm
    prependPattern pm = CoreTypeScheme Internal . Forall . Bound pm

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
typeCheckGlobalText e = do
  (e', ς') <- typeCheckGlobal e
  pure (e', convertFunctionLiteral False ς')

typeCheckGlobalAnnotateImpl ::
  (p -> KindUnify -> Core p ()) ->
  TermAuto p ->
  TypeScheme (KindAuto p) Void p p ->
  Core p (TermInfer p, TypeSchemeInfer)
typeCheckGlobalAnnotateImpl check e@(CoreTerm p _) ς = do
  enterLevel
  (ς', κ) <- typeCheckValidateTypeScheme ς
  check p κ
  augmentScheme ς' $ \σ -> do
    ((e, σ'), _) <- typeCheckAnnotateLinearTerm e
    matchType p σ σ'
    leaveLevel
    θ <- solveType
    (e, _) <- pure $ applySubstitution θ (e, σ)
    _ <- removeDeadTypeVariables θ
    ambigousTypeCheck Set.empty
    θ <- solveKind
    (e, _) <- pure $ applySubstitution θ (e, σ)
    _ <- removeDeadKindVariables θ
    ambigousKindCheck Set.empty
    pure (stripUnifier e, stripUnifier (Internal <$ ς'))

typeCheckGlobalAnnotate ::
  TermAuto p ->
  TypeScheme (KindAuto p) Void p p ->
  Core p (TermInfer p, TypeSchemeInfer)
typeCheckGlobalAnnotate = typeCheckGlobalAnnotateImpl (const $ const $ pure ())

typeCheckGlobalAnnotateText ::
  TermAuto p ->
  TypeScheme (KindAuto p) Void p p ->
  Core p (TermInfer p, TypeSchemeInfer)
typeCheckGlobalAnnotateText e ς = do
  (e', ς') <- typeCheckGlobalAnnotateImpl check e (convertFunctionLiteral True ς)
  pure (e', convertFunctionLiteral False ς')
  where
    check p κ = matchKind p κ (CoreKind Internal $ Type $ CoreKind Internal $ Text)

convertFunctionLiteral hide ς = case ς of
  CoreTypeScheme p (MonoType σ) -> CoreTypeScheme p $ MonoType $ go σ
    where
      go (CoreType p (FunctionPointer σ τ)) | hide = CoreType p $ FunctionLiteralType σ τ
      go (CoreType p (FunctionLiteralType σ τ)) | not hide = CoreType p $ FunctionPointer σ τ
      go (CoreType p (Implied π σ)) = CoreType p $ Implied π (go σ)
      go σ = σ
  CoreTypeScheme p (Forall (Bound pm ς)) -> CoreTypeScheme p $ Forall (Bound pm $ convertFunctionLiteral hide ς)
  CoreTypeScheme p (KindForall (Bound pm ς)) -> CoreTypeScheme p $ KindForall $ Bound pm (convertFunctionLiteral hide ς)
