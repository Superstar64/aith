module Language.TypeCheck where

import Control.Arrow (second)
import Control.Monad ((<=<))
import Control.Monad.Trans (lift)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Data.Maybe (fromJust)
import Data.Set (Set)
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
import Language.TypeCheck.Variable
import qualified Misc.MonoidMap as Map
import Misc.Util (firstM, secondM, temporaries')

class Augment m pm where
  augment :: pm -> m a -> m a

class AugmentLinear m pm x where
  augmentLinear :: Multiplicity -> pm -> m (a, Use x) -> m (a, Use x)

validate e = fst <$> typeCheckValidate e

annotate e = fst <$> typeCheckAnnotate e

class TypeCheckValidate m e e' σ | e -> e', e -> σ where
  typeCheckValidate :: e -> m (e', σ)

class TypeCheckAnnotate m e e' σ | e -> e', e -> σ where
  typeCheckAnnotate :: e -> m (e', σ)

class TypeCheckAnnotateLinear m e e' σ x | e -> e', e -> σ, e -> x where
  typeCheckAnnotateLinear :: e -> m ((e', σ), Use x)

class TypeCheckValidateLinear m e e' σ x | e -> e', e -> σ, e -> x where
  typeCheckValidateLinear :: e -> m ((e', σ), Use x)

class Match m p e where
  match :: p -> e -> e -> m ()

instance System p m => Match m p TypeUnify where
  match p σ σ' = insertTypeEquation (TypeEquation p σ σ')

instance System p m => Match m p KindUnify where
  match p κ κ' = insertKindEquation (KindEquation p κ κ')

instance TypeErrorQuit p m => Match m p Sort where
  match _ Kind Kind = pure ()
  match _ Stage Stage = pure ()
  match _ Impact Impact = pure ()
  match _ Existance Existance = pure ()
  match _ Representation Representation = pure ()
  match p μ μ' = quit $ SortMismatch p μ μ'

checkKind p μt = do
  match p μt Kind
  pure ()

checkStage p μt = do
  match p μt Stage
  pure ()

checkExistance p μt = do
  match p μt Existance
  pure ()

checkImpact p μt = do
  match p μt Impact
  pure ()

checkRepresentation p μ = do
  match p μ Representation
  pure ()

checkType p κt = do
  κ <- freshKindVariable p Stage
  match p κt (CoreKind Internal (Type κ))
  pure κ

checkEvidence p κt = do
  match p κt (CoreKind Internal $ Evidence)

checkRegion p κt = do
  match p κt (CoreKind Internal Region)
  pure ()

checkRuntime p κt = do
  κ <- freshKindVariable p Impact
  κ' <- freshKindVariable p Existance
  match p κt (CoreKind Internal (Runtime κ κ'))
  pure (κ, κ')

checkData p κt = match p κt (CoreKind Internal $ Data)

checkReal p κt = do
  κ <- freshKindVariable p Representation
  match p κt (CoreKind Internal $ Real κ)
  pure κ

checkTypeRT p κt = do
  (κ, κ') <- checkRuntime p =<< checkType p κt
  checkData p κ
  checkReal p κ'

makeTypeRT κt = CoreKind Internal $ Type $ CoreKind Internal $ Runtime (CoreKind Internal Data) $ CoreKind Internal $ Real κt

freshTypeVariable p κ = (CoreType Internal . TypeExtra) <$> freshTypeVariableRaw p κ

freshKindVariable p μ = (CoreKind Internal . KindExtra) <$> freshKindVariableRaw p μ

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
  match p σt σ
  -- todo rework this
  -- can't return σt reconstruction needs to destructure σ's kind
  pure σ

enforceRuntime p σt = do
  σ <- freshRuntimeTypeVariable p
  match p σt σ
  pure σ

enforceEvidence p σt = do
  σ <- freshTypeVariable p $ CoreKind Internal $ Type $ CoreKind Internal Evidence
  match p σt σ
  pure σ

freshRegionTypeVariable p = do
  freshTypeVariable p $ CoreKind Internal $ Region

checkMacro p σt = do
  σ <- freshMetaTypeVariable p
  τ <- freshMetaTypeVariable p
  match p σt (CoreType Internal (Macro σ τ))
  pure (σ, τ)

checkImplied p σt = do
  σ <- freshTypeVariable p (CoreKind Internal $ Type $ CoreKind Internal Evidence)
  τ <- freshMetaTypeVariable p
  match p σt (CoreType Internal (Implied σ τ))
  pure (σ, τ)

checkFunctionPointer p σt = do
  σ <- freshRTTypeVariable p
  τ <- freshRuntimeTypeVariable p
  match p σt (CoreType Internal $ FunctionPointer σ τ)
  pure (σ, τ)

checkFunctionLiteralType p σt = do
  σ <- freshRTTypeVariable p
  τ <- freshRuntimeTypeVariable p
  match p σt (CoreType Internal $ FunctionLiteralType σ τ)
  pure (σ, τ)

checkRegionReference p σt = do
  π <- freshRegionTypeVariable p
  σ <- freshRTTypeVariable p
  match p σt (CoreType Internal $ RegionReference π σ)
  pure (π, σ)

checkRegionTransformer p σt = do
  π <- freshRegionTypeVariable p
  κ <- freshKindVariable p Existance
  σ <- freshTypeVariable p $ CoreKind Internal $ Type $ CoreKind Internal $ Runtime (CoreKind Internal Data) κ
  match p σt (CoreType Internal $ RegionTransformer π σ)
  pure (π, σ)

checkCopy p σt = do
  σ <- freshRTTypeVariable p
  match p σt (CoreType Internal $ Copy σ)
  pure σ

augmentVariableLinear p x l σ e = do
  (σ', lΓ) <- augmentTypeEnvironment x p l (CoreTypeScheme Internal $ MonoType σ) e
  case (count x lΓ, l) of
    (Single, _) -> pure ()
    (_, Unrestricted) -> pure ()
    (_, _) -> quit $ InvalidUsage p x
  pure (σ', Remove x lΓ)

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
      (σ', κ) <- typeCheckValidate σ
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
      σ' <- validate σ
      enforceRT p σ'
  pure ((CoreTermPattern p $ PatternCommon $ PatternVariable x σ', σ'), useNothing)
typeCheckAnnotateLinearPatternRuntime (CoreTermPattern p (PatternCommon (RuntimePatternPair pm1 pm2))) = do
  ((pm1', σ1), lΓ1) <- typeCheckAnnotateLinearPatternRuntime pm1
  ((pm2', σ2), lΓ2) <- typeCheckAnnotateLinearPatternRuntime pm2
  pure ((CoreTermPattern p $ PatternCommon $ RuntimePatternPair pm1' pm2', CoreType Internal $ RuntimePair σ1 σ2), combine lΓ1 lΓ2)
typeCheckAnnotateLinearPatternRuntime (CoreTermPattern p (PatternCopy e pm)) = do
  ((e', π), lΓ1) <- typeCheckAnnotateLinear e
  ((pm', σ), lΓ2) <- typeCheckAnnotateLinearPatternRuntime pm
  match p π (CoreType Internal $ Copy σ)
  pure ((CoreTermPattern p $ PatternCopy e' pm', σ), lΓ1 `combine` lΓ2)
typeCheckAnnotateLinearPatternRuntime (CoreTermPattern p _) = quit $ ExpectedRuntimePattern p

instance
  ( TypeErrorQuit p m,
    Environment p m,
    System p m
  ) =>
  TypeCheckAnnotate m (Pattern TypeIdentifier (KindAuto p) p) (Pattern TypeIdentifier KindUnify p) Sort
  where
  typeCheckAnnotate (Pattern p x (Just κ)) = do
    (κ', μ) <- typeCheckValidate κ
    match p μ Kind
    pure (Pattern p x κ', μ)
  typeCheckAnnotate (Pattern p x Nothing) = do
    κ <- freshKindVariable p Kind
    pure (Pattern p x κ, Kind)

instance Monad m => TypeCheckAnnotate m (Pattern KindIdentifier Sort p) (Pattern KindIdentifier Sort p) () where
  typeCheckAnnotate pm = pure (pm, ())

instance
  ( Environment p m,
    System p m,
    TypeErrorQuit p m
  ) =>
  TypeCheckValidate m (TypeScheme (KindAuto p) Void p p) (TypeScheme KindUnify LogicVariableType Internal p) KindUnify
  where
  typeCheckValidate (CoreTypeScheme p (MonoType σ)) = do
    (σ', κ) <- typeCheckValidate σ
    pure (CoreTypeScheme p (MonoType σ'), κ)
  typeCheckValidate (CoreTypeScheme p (Forall (Bound pm σ))) = do
    pm' <- annotate pm
    (σ', κ) <- augment pm' $ typeCheckValidate σ
    pure $ (CoreTypeScheme p $ Forall $ Bound pm' σ', κ)
  typeCheckValidate (CoreTypeScheme p (KindForall (Bound pm σ))) = do
    pm' <- annotate pm
    (σ', _) <- augment pm' $ typeCheckValidate σ
    pure (CoreTypeScheme p $ KindForall $ Bound pm' σ', CoreKind Internal $ Type $ CoreKind Internal Meta)

instance Environment p m => Augment m (Pattern TypeIdentifier KindUnify p) where
  augment (Pattern p x κ) = augmentKindEnvironment x p κ

instance Environment p m => Augment m (Pattern KindIdentifier Sort p) where
  augment (Pattern p x μ) = augmentSortEnvironment x p μ

instance
  ( Environment p m,
    System p m,
    TypeErrorQuit p m
  ) =>
  AugmentLinear m (TermPattern InstantiationUnify TypeUnify p) TermIdentifier
  where
  augmentLinear l pm = go l pm
    where
      go l (CoreTermPattern p (PatternCommon (PatternVariable x σ))) = augmentVariableLinear p x l σ
      go _ (CoreTermPattern _ (PatternCommon (RuntimePatternPair pm pm'))) = go Linear pm . go Linear pm'
      go _ (CoreTermPattern _ (PatternCopy _ pm)) = go Unrestricted pm
      go _ (CoreTermPattern _ (PatternOfCourse pm)) = go Unrestricted pm

instance
  ( System p m,
    Environment p m,
    TypeErrorQuit p m
  ) =>
  TypeCheckValidate m (Type (KindAuto p) Void p) TypeUnify KindUnify
  where
  typeCheckValidate (CoreType p (TypeVariable x)) = do
    κ <- lookupKindEnvironment x
    case κ of
      Just (_, κ) -> pure (CoreType Internal (TypeVariable x), κ)
      Nothing -> quit $ UnknownTypeIdentifier p x
  typeCheckValidate (CoreType p (Macro σ τ)) = do
    (σ', _) <- secondM (checkType p) =<< typeCheckValidate σ
    (τ', _) <- secondM (checkType p) =<< typeCheckValidate τ
    pure (CoreType Internal $ Macro σ' τ', CoreKind Internal $ Type $ CoreKind Internal Meta)
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
    (σ', κ) <- secondM (checkTypeRT p) =<< typeCheckValidate σ
    pure (CoreType Internal $ RegionReference π' σ', makeTypeRT κ)
  typeCheckValidate (CoreType _ (TypeExtra v)) = absurd v

instance
  ( TypeErrorQuit p m,
    Environment p m
  ) =>
  TypeCheckValidate m (Kind Void p) KindUnify Sort
  where
  typeCheckValidate (CoreKind p (KindVariable x)) = do
    μ <- lookupSortEnvironment x
    case μ of
      Just (_, μ) -> pure (CoreKind Internal $ KindVariable x, μ)
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
  typeCheckValidate (CoreKind _ (KindExtra v)) = absurd v

instantiateTypeScheme _ (CoreTypeScheme _ (MonoType σ)) = pure (σ, InstantiateEmpty)
instantiateTypeScheme p (CoreTypeScheme _ (Forall (Bound (Pattern _ x κ) σ))) = do
  τ <- freshTypeVariable p κ
  (ς, θ) <- instantiateTypeScheme p $ substitute τ x σ
  pure (ς, InstantiateType x τ θ)
instantiateTypeScheme p (CoreTypeScheme _ (KindForall (Bound (Pattern _ x μ) σ))) = do
  κ <- freshKindVariable p μ
  (ς, θ) <- instantiateTypeScheme p $ substitute κ x σ
  pure (ς, InstantiateKind x κ θ)

instance
  ( System p m,
    Environment p m,
    TypeErrorQuit p m
  ) =>
  TypeCheckAnnotateLinear m (Term () (TypeAuto p) p) (Term InstantiationUnify TypeUnify p) TypeUnify TermIdentifier
  where
  typeCheckAnnotateLinear (CoreTerm p (TermRuntime (Variable x ()))) = do
    mσ <- lookupTypeEnviroment x
    case mσ of
      Just (_, _, σ) -> do
        (τ, θ) <- instantiateTypeScheme p σ
        pure ((CoreTerm p $ TermRuntime $ Variable x θ, τ), Use x)
      Nothing -> quit $ UnknownIdentifier p x
  typeCheckAnnotateLinear (CoreTerm p (MacroAbstraction (Bound pm e))) = do
    (pm', σ) <- typeCheckAnnotateMetaPattern pm
    ((e', τ), lΓ) <- augmentLinear Linear pm' (typeCheckAnnotateLinear e)
    pure ((CoreTerm p (MacroAbstraction (Bound pm' e')), CoreType Internal $ Macro σ τ), lΓ)
  typeCheckAnnotateLinear (CoreTerm p (MacroApplication e1 e2)) = do
    ((e1', (σ, τ)), lΓ1) <- firstM (secondM (checkMacro p)) =<< typeCheckAnnotateLinear e1
    ((e2', σ'), lΓ2) <- typeCheckAnnotateLinear e2
    match p σ σ'
    pure ((CoreTerm p (MacroApplication e1' e2'), τ), lΓ1 `combine` lΓ2)
  typeCheckAnnotateLinear (CoreTerm p (ImplicationAbstraction (Bound pm e))) = do
    (pm', σ) <- typeCheckAnnotateMetaPattern pm
    σ <- enforceEvidence p σ
    ((e', τ), lΓ) <- augmentLinear Unrestricted pm' (typeCheckAnnotateLinear e)
    pure ((CoreTerm p (ImplicationAbstraction (Bound pm' e')), CoreType Internal $ Implied σ τ), lΓ)
  typeCheckAnnotateLinear (CoreTerm p (ImplicationApplication e1 e2)) = do
    ((e1', (σ, τ)), lΓ1) <- firstM (secondM (checkImplied p)) =<< typeCheckAnnotateLinear e1
    ((e2', σ'), lΓ2) <- typeCheckAnnotateLinear e2
    match p σ σ'
    pure ((CoreTerm p (ImplicationApplication e1' e2'), τ), lΓ1 `combine` lΓ2)
  typeCheckAnnotateLinear (CoreTerm p (TermRuntime (Alias e1 (Bound pm e2)))) = do
    ((e1', τ), lΓ1) <- typeCheckAnnotateLinear e1
    ((pm', τ'), lΓ3) <- typeCheckAnnotateLinearPatternRuntime pm
    match p τ τ'
    ((e2', σ), lΓ2) <- augmentLinear Linear pm' (typeCheckAnnotateLinear e2)
    σ <- enforceRuntime p σ
    pure ((CoreTerm p (TermRuntime (Alias e1' (Bound pm' e2'))), σ), lΓ1 `combine` lΓ2 `combine` lΓ3)
  typeCheckAnnotateLinear (CoreTerm p (TermRuntime (Extern sym τ σ))) = do
    τ' <- case τ of
      Nothing -> freshRTTypeVariable p
      Just τ -> do
        τ <- validate τ >>= enforceRT p
        pure τ
    σ' <- case σ of
      Nothing -> freshRuntimeTypeVariable p
      Just σ -> do
        σ <- validate σ >>= enforceRuntime p
        pure σ
    pure ((CoreTerm p (TermRuntime (Extern sym τ' σ')), CoreType Internal $ FunctionPointer τ' σ'), useNothing)
  typeCheckAnnotateLinear (CoreTerm p (TermRuntime (FunctionApplication e1 e2 σ''))) = do
    ((e1', (σ, τ)), lΓ1) <- firstM (secondM (checkFunctionPointer p)) =<< typeCheckAnnotateLinear e1
    ((e2', σ'), lΓ2) <- typeCheckAnnotateLinear e2
    match p σ σ'
    case σ'' of
      Nothing -> pure ()
      Just σ'' -> do
        σ''' <- validate σ''
        match p σ σ'''
    pure ((CoreTerm p $ TermRuntime $ FunctionApplication e1' e2' σ, τ), lΓ1 `combine` lΓ2)
  typeCheckAnnotateLinear (CoreTerm p (TermRuntime (FunctionLiteral (Bound pm e)))) = do
    ((pm', σ), lΓ1) <- typeCheckAnnotateLinearPatternRuntime pm
    ((e', τ), lΓ2) <- augmentLinear Linear pm' (typeCheckAnnotateLinear e)
    τ <- enforceRuntime p τ
    pure ((CoreTerm p $ TermRuntime $ FunctionLiteral $ Bound pm' e', CoreType Internal $ FunctionLiteralType σ τ), lΓ1 `combine` lΓ2)
  typeCheckAnnotateLinear (CoreTerm p (TermRuntime (ReadReference ev e σ''))) = do
    ((e', (π, σ)), lΓ1) <- firstM (secondM (checkRegionReference p)) =<< typeCheckAnnotateLinear e
    ((ev', σ'), lΓ2) <- firstM (secondM (checkCopy p)) =<< typeCheckAnnotateLinear ev
    match p σ σ'
    case σ'' of
      Nothing -> pure ()
      Just σ'' -> do
        σ''' <- validate σ''
        match p σ σ'''
    pure ((CoreTerm p (TermRuntime (ReadReference ev' e' σ)), CoreType Internal (RegionTransformer π σ)), lΓ1 `combine` lΓ2)
  typeCheckAnnotateLinear (CoreTerm p (OfCourseIntroduction e)) = do
    ((e', σ), lΓ) <- typeCheckAnnotateLinear e
    capture p lΓ
    pure ((CoreTerm p (OfCourseIntroduction e'), CoreType Internal $ OfCourse $ σ), lΓ)
  typeCheckAnnotateLinear (CoreTerm p (Bind e1 (Bound pm e2))) = do
    ((e1', τ), lΓ1) <- typeCheckAnnotateLinear e1
    (pm', τ') <- typeCheckAnnotateMetaPattern pm
    match p τ τ'
    ((e2', σ), lΓ2) <- augmentLinear Linear pm' $ typeCheckAnnotateLinear e2
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
    (pm', σ') <- typeCheckAnnotateMetaPattern pm
    match p σ σ'
    ((e2', (π', τ)), lΓ2) <- firstM (secondM (checkRegionTransformer p)) =<< augmentLinear Linear pm' (typeCheckAnnotateLinear e2)
    match p π π'
    pure ((CoreTerm p $ DoRegionTransformer e1' (Bound pm' e2'), CoreType Internal $ RegionTransformer π τ), lΓ1 `combine` lΓ2)
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

-- todo this is ugly, find a better way to do this
class Reconstruct m σ κ | σ -> κ where
  reconstruct :: σ -> m κ

instance
  ( Index m vσ (Kind vκ Internal),
    Index m TypeIdentifier (Kind vκ Internal)
  ) =>
  Reconstruct m (Type (Kind vκ Internal) vσ Internal) (Kind vκ Internal)
  where
  reconstruct (CoreType _ (TypeVariable x)) = do
    index x
  reconstruct (CoreType _ (TypeExtra v)) = do
    index v
  reconstruct (CoreType _ (Macro _ _)) = do
    pure $ CoreKind Internal $ Type $ CoreKind Internal Meta
  reconstruct (CoreType _ (Implied _ σ)) = do
    reconstruct σ
  reconstruct (CoreType _ (OfCourse _)) = do
    pure $ CoreKind Internal $ Type $ CoreKind Internal Meta
  reconstruct (CoreType _ (FunctionPointer _ _)) = do
    pure $ CoreKind Internal $ Type $ CoreKind Internal $ Runtime (CoreKind Internal Data) (CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime PointerRep)
  reconstruct (CoreType _ (FunctionLiteralType _ _)) = do
    pure $ CoreKind Internal $ Type $ CoreKind Internal $ Text
  reconstruct (CoreType _ (Copy _)) = do
    pure $ CoreKind Internal $ Type $ CoreKind Internal $ Evidence
  reconstruct (CoreType _ (RuntimePair σ σ')) = do
    κ <- reconstruct σ
    κ' <- reconstruct σ'
    case (κ, κ') of
      ( CoreKind _ (Type (CoreKind _ (Runtime _ (CoreKind Internal (Real κ))))),
        CoreKind _ (Type (CoreKind _ (Runtime _ (CoreKind Internal (Real κ')))))
        ) -> do
          pure $
            CoreKind Internal $
              Type $ CoreKind Internal $ Runtime (CoreKind Internal Data) $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ StructRep [κ, κ']
      _ -> error "internal error: reconstruction of pair didn't return runtime kind"
  reconstruct (CoreType _ (RegionTransformer _ σ)) = do
    κ <- reconstruct σ
    case κ of
      (CoreKind _ (Type (CoreKind _ (Runtime _ κ)))) -> pure $ CoreKind Internal $ Type $ CoreKind Internal $ Runtime (CoreKind Internal Code) κ
      _ -> error "internal error: reconstruction of region transformer didn't return runtime kind"
  reconstruct (CoreType _ (RegionReference _ σ)) = reconstruct σ

instance
  ( Index m vκ Sort,
    Index m KindIdentifier Sort
  ) =>
  Reconstruct m (Kind vκ Internal) Sort
  where
  reconstruct (CoreKind _ (KindVariable x)) = do
    index x
  reconstruct (CoreKind _ (KindExtra v)) = do
    index v
  reconstruct (CoreKind _ (Type _)) = pure $ Kind
  reconstruct (CoreKind _ Evidence) = pure $ Stage
  reconstruct (CoreKind _ Region) = pure $ Kind
  reconstruct (CoreKind _ Meta) = pure $ Stage
  reconstruct (CoreKind _ Text) = pure $ Stage
  reconstruct (CoreKind _ (Runtime _ _)) = pure $ Stage
  reconstruct (CoreKind _ Code) = pure $ Impact
  reconstruct (CoreKind _ Data) = pure $ Impact
  reconstruct (CoreKind _ Imaginary) = pure $ Existance
  reconstruct (CoreKind _ (Real _)) = pure $ Existance
  reconstruct (CoreKind _ (KindRuntime _)) = pure $ Representation

class Unifier x σ where
  unify :: TypeErrorQuit p m => p -> σ -> σ -> WriterT (Substitution x σ) (Core p m) ()
  solve :: TypeErrorQuit p m => WriterT (Substitution x σ) (Core p m) ()

unifyVariable indexVariableMap removeVariable apply p occurs x σ = do
  κ <- reconstruct σ
  κ' <- indexVariableMap x
  removeVariable x
  match p κ κ'
  if x `Map.member` freeVariablesInternal σ
    then quit $ occurs p x σ
    else pure ()
  apply (substitute σ x)
  pure $ singleSubstitution x σ

instance Unifier LogicVariableType TypeUnify where
  unify _ (CoreType _ (TypeExtra x)) (CoreType _ (TypeExtra x')) | x == x' = pure ()
  unify p (CoreType _ (TypeExtra x)) σ = do
    θ <- lift $ unifyVariable indexTypeVariableMap removeTypeVariable apply p TypeOccursCheck x σ
    tell θ
    where
      apply f = do
        modifyTypeEquations (map $ fmap f)
  unify p σ σ'@(CoreType _ (TypeExtra _)) = unify p σ' σ
  unify _ (CoreType _ (TypeVariable x)) (CoreType _ (TypeVariable x')) | x == x' = pure ()
  unify p (CoreType _ (Macro σ τ)) (CoreType _ (Macro σ' τ')) = do
    match p σ σ'
    match p τ τ'
  unify p (CoreType _ (Implied σ τ)) (CoreType _ (Implied σ' τ')) = do
    match p σ σ'
    match p τ τ'
  unify p (CoreType _ (OfCourse σ)) (CoreType _ (OfCourse σ')) = do
    match p σ σ'
  unify p (CoreType _ (FunctionPointer σ τ)) (CoreType _ (FunctionPointer σ' τ')) = do
    match p σ σ'
    match p τ τ'
  unify p (CoreType _ (FunctionLiteralType σ τ)) (CoreType _ (FunctionLiteralType σ' τ')) = do
    match p σ σ'
    match p τ τ'
  unify p (CoreType _ (Copy σ)) (CoreType _ (Copy σ')) = do
    match p σ σ'
  unify p (CoreType _ (RuntimePair σ τ)) (CoreType _ (RuntimePair σ' τ')) = do
    match p σ σ'
    match p τ τ'
  unify p (CoreType _ (RegionTransformer π σ)) (CoreType _ (RegionTransformer π' σ')) = do
    match p π π'
    match p σ σ'
  unify p (CoreType _ (RegionReference π σ)) (CoreType _ (RegionReference π' σ')) = do
    match p π π'
    match p σ σ'
  unify p σ σ' = quit $ TypeMismatch p σ σ'

  solve = do
    equations <- lift $ getTypeEquations
    case equations of
      [] -> pure ()
      (TypeEquation p σ σ' : remaining) -> do
        lift $ modifyTypeEquations (const remaining)
        unify p σ σ'
        solve

instance Unifier LogicVariableKind KindUnify where
  unify _ (CoreKind _ (KindExtra x)) (CoreKind _ (KindExtra x')) | x == x' = pure ()
  unify p (CoreKind _ (KindExtra x)) κ = do
    θ <- lift $ unifyVariable indexKindVariableMap removeKindVariable apply p KindOccursCheck x κ
    tell θ
    where
      apply f = do
        modifyKindEquations (map $ fmap f)
        modifyTypeVariableMap (fmap $ second $ f)
  unify p κ κ'@(CoreKind _ (KindExtra _)) = unify p κ' κ
  unify _ (CoreKind _ (KindVariable x)) (CoreKind _ (KindVariable x')) | x == x' = pure ()
  unify p (CoreKind _ (Type κ)) (CoreKind _ (Type κ')) = do
    match p κ κ'
  unify _ (CoreKind _ Evidence) (CoreKind _ Evidence) = pure ()
  unify _ (CoreKind _ Region) (CoreKind _ Region) = pure ()
  unify p (CoreKind _ (Runtime κ1 κ2)) (CoreKind _ (Runtime κ1' κ2')) = do
    match p κ1 κ1'
    match p κ2 κ2'
  unify _ (CoreKind _ Code) (CoreKind _ Code) = pure ()
  unify _ (CoreKind _ Data) (CoreKind _ Data) = pure ()
  unify _ (CoreKind _ Imaginary) (CoreKind _ Imaginary) = pure ()
  unify p (CoreKind _ (Real κ)) (CoreKind _ (Real κ')) = do
    match p κ κ'
  unify _ (CoreKind _ Meta) (CoreKind _ Meta) = pure ()
  unify _ (CoreKind _ Text) (CoreKind _ Text) = pure ()
  unify _ (CoreKind _ (KindRuntime PointerRep)) (CoreKind _ (KindRuntime PointerRep)) = pure ()
  unify p (CoreKind _ (KindRuntime (StructRep κs))) (CoreKind _ (KindRuntime (StructRep κs'))) | length κs == length κs' = do
    sequence_ $ zipWith (match p) κs κs'
  unify p κ κ' = quit $ KindMismatch p κ κ'
  solve = do
    equations <- lift $ getKindEquations
    case equations of
      [] -> pure ()
      (KindEquation p κ κ' : remaining) -> do
        lift $ modifyKindEquations (const remaining)
        unify p κ κ'
        solve

-- types must be solved first

solveTypes e = do
  ((), θ) <- runWriterT (solve @LogicVariableType @TypeUnify)
  pure $ applySubstitution θ e

solveKinds e = do
  ((), θ) <- runWriterT (solve @LogicVariableKind @KindUnify)
  pure $ applySubstitution θ e

solveAll :: (TypeErrorQuit p m, Substitute TypeUnify LogicVariableType e, Substitute KindUnify LogicVariableKind e) => e -> Core p m e
solveAll = solveKinds <=< solveTypes

attachRigidType :: TypeErrorQuit p m => p -> [String] -> [LogicVariableType] -> Core p m ([Pattern TypeIdentifier KindUnify Internal], Substitution LogicVariableType TypeUnify)
attachRigidType p (x : xs) (α : αs) = do
  κ <- indexTypeVariableMap α
  (pms, θ) <- attachRigidType p xs αs
  pure (Pattern Internal (TypeIdentifier x) κ : pms, singleSubstitution α (CoreType Internal $ TypeVariable $ TypeIdentifier x) <> θ)
attachRigidType _ _ [] = pure ([], identitySubstitution)
attachRigidType _ _ _ = error "empty name generator"

attachRigidKind :: TypeErrorQuit p m => p -> [String] -> [LogicVariableKind] -> Core p m ([Pattern KindIdentifier Sort Internal], Substitution LogicVariableKind KindUnify)
attachRigidKind p (x : xs) (α : αs) = do
  μ <- indexKindVariableMap α
  (pms, θ) <- attachRigidKind p xs αs
  pure (Pattern Internal (KindIdentifier x) μ : pms, singleSubstitution α (CoreKind Internal $ KindVariable $ KindIdentifier x) <> θ)
attachRigidKind _ _ [] = pure ([], identitySubstitution)
attachRigidKind _ _ _ = error "empty name generator"

ambiguousTypeCheck :: TypeErrorQuit p m => Set LogicVariableType -> Core p m ()
ambiguousTypeCheck legal = do
  αs <- Map.toList <$> getTypeVariableMap
  for αs $ \(α, (p, _)) -> do
    if α `Set.notMember` legal
      then quit $ AmbiguousType p α legal
      else pure ()
  pure ()

ambiguousKindCheck :: TypeErrorQuit p m => Set LogicVariableKind -> Core p m ()
ambiguousKindCheck legal = do
  αs <- Map.toList <$> getKindVariableMap
  for αs $ \(α, (p, _)) -> do
    if α `Set.notMember` legal
      then quit $ AmbiguousKind p α legal
      else pure ()
  pure ()

class StripUnifier e e' | e -> e' where
  stripUnifier :: e -> e'

instance StripUnifier (Term InstantiationUnify TypeUnify p) (Term InstantiationInfer TypeInfer p) where
  stripUnifier = mapTerm stripUnifier stripUnifier id

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

errorUnifierType :: LogicVariableType -> a
errorUnifierType _ = error "unexpected logic type variable"

errorUnifierKind :: LogicVariableKind -> a
errorUnifierKind _ = error "unexpected logic kind variable"

typeTemporaries = temporaries' $ (: []) <$> ['α' .. 'γ']

kindTemporaries = temporaries' $ (: []) <$> ['χ' .. 'ω']

generalizeCommon i f g e@(CoreTerm p _) = do
  (e, σ) <- fst <$> typeCheckAnnotateLinear e
  i p σ
  (e, σ) <- solveAll (e, σ)
  let α1 = Map.keysSet $ freeVariablesInternal @LogicVariableType σ
  ambiguousTypeCheck α1
  (pm, θσ) <- attachRigidType p typeTemporaries (Set.toList α1)
  let α2 = f $ Map.keysSet $ freeVariablesInternal @LogicVariableKind pm
  ambiguousKindCheck α2
  (pm2, θκ) <- attachRigidKind p kindTemporaries (Set.toList α2)
  (((e, σ), pm), pm2) <- pure $ applySubstitution θσ $ applySubstitution θκ (((e, σ), pm), pm2)
  let e' = stripUnifier e
  let σ' = stripUnifier σ
  let pm' = map stripUnifier pm
  let pm2' = map stripUnifier pm2
  let ς = foldr prependKindPattern (foldr prependPattern (CoreTypeScheme Internal $ MonoType σ') pm') pm2'
  pure (e', g ς)
  where
    prependKindPattern pm = CoreTypeScheme Internal . KindForall . Bound pm
    prependPattern pm = CoreTypeScheme Internal . Forall . Bound pm

generalize ::
  TypeErrorQuit p m =>
  Term () (TypeAuto p) p ->
  Core p m (Term InstantiationInfer TypeInfer p, TypeSchemeInfer)
generalize = generalizeCommon (const $ const $ pure ()) id id

generalizeText ::
  TypeErrorQuit p m =>
  Term () (TypeAuto p) p ->
  Core p m (Term InstantiationInfer TypeInfer p, TypeSchemeInfer)
generalizeText = generalizeCommon check (const Set.empty) (convertFunctionLiteral False)
  where
    check p σ = do
      σ' <- freshTypeVariable p (CoreKind Internal $ Type $ CoreKind Internal Text)
      match p σ σ'

augmentScheme (CoreTypeScheme _ (MonoType σ)) e = e σ
augmentScheme (CoreTypeScheme _ (Forall (Bound pm σ))) e = augment pm (augmentScheme σ e)
augmentScheme (CoreTypeScheme _ (KindForall (Bound pm σ))) e = augment pm (augmentScheme σ e)

generalizeAnnotateCommon i f g e@(CoreTerm p _) ς = do
  (ς', κ) <- typeCheckValidate (f ς)
  i p κ
  augmentScheme ς' $ \σ -> do
    (e, σ') <- fst <$> typeCheckAnnotateLinear e
    match p σ σ'
    e <- solveTypes e
    (e, ς') <- solveKinds (e, ς')
    ambiguousTypeCheck Set.empty
    ambiguousKindCheck Set.empty
    pure (stripUnifier e, g $ stripUnifier $ (Internal <$ ς'))

generalizeAnnotate ::
  TypeErrorQuit p m =>
  Term () (TypeAuto p) p ->
  TypeScheme (KindAuto p) Void p p ->
  Core p m (Term InstantiationInfer TypeInfer p, TypeSchemeInfer)
generalizeAnnotate = generalizeAnnotateCommon (const $ const $ pure ()) id id

generalizeAnnotateText ::
  TypeErrorQuit p m =>
  Term () (TypeAuto p) p ->
  TypeScheme (KindAuto p) Void p p ->
  Core p m (Term InstantiationInfer TypeInfer p, TypeSchemeInfer)
generalizeAnnotateText = generalizeAnnotateCommon (flip match $ CoreKind Internal $ Type $ CoreKind Internal Text) (convertFunctionLiteral True) (convertFunctionLiteral False)

convertFunctionLiteral hide ς = case ς of
  CoreTypeScheme p (MonoType σ) -> CoreTypeScheme p $ MonoType $ go σ
    where
      go (CoreType p (FunctionPointer σ τ)) | hide = CoreType p $ FunctionLiteralType σ τ
      go (CoreType p (FunctionLiteralType σ τ)) | not hide = CoreType p $ FunctionPointer σ τ
      go (CoreType p (Implied π σ)) = CoreType p $ Implied π (go σ)
      go σ = σ
  CoreTypeScheme p (Forall (Bound pm ς)) -> CoreTypeScheme p $ Forall (Bound pm $ convertFunctionLiteral hide ς)
  CoreTypeScheme p (KindForall (Bound pm ς)) -> CoreTypeScheme p $ KindForall $ Bound pm (convertFunctionLiteral hide ς)
