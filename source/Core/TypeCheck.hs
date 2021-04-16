module Core.TypeCheck where

import Control.Monad ((<=<))
import Control.Monad.Trans.Class (MonadTrans, lift)
import Control.Monad.Trans.State (StateT, evalStateT, get, put)
import Core.Ast.Common
import Core.Ast.FunctionLiteral
import Core.Ast.Kind
import Core.Ast.KindPattern
import Core.Ast.Multiplicity
import Core.Ast.Pattern
import Core.Ast.Sort
import Core.Ast.Term
import Core.Ast.Type
import Core.Ast.TypePattern
import Data.Functor.Identity (runIdentity)
import Data.Map (Map, (!), (!?))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (for)
import Environment
import Error
import Misc.Identifier (Identifier)
import Misc.Util (firstM, zipWithM)

data CoreState p = CoreState
  { typeEnvironment :: Map Identifier (p, MultiplicityInternal, TypeInternal),
    kindEnvironment :: Map Identifier (p, KindInternal),
    sortEnvironment :: Map Identifier (p, Sort)
  }
  deriving (Show, Functor)

emptyState = CoreState Map.empty Map.empty Map.empty

newtype Core p m a = Core {runCore' :: StateT (CoreState p) m a} deriving (Functor, Applicative, Monad, MonadTrans)

runCore c = evalStateT (runCore' c)

instance Base p m => Base p (Core p m) where
  quit error = Core (lift $ quit error)
  moduleQuit error = Core (lift $ moduleQuit error)

matchSort _ Kind Kind = pure ()
matchSort _ Stage Stage = pure ()
matchSort _ Representation Representation = pure ()
matchSort p μ μ' = quit $ IncompatibleSort p μ μ'

matchLinear' _ Linear Linear = pure ()
matchLinear' _ Unrestricted Unrestricted = pure ()
matchLinear' p l l' = quit $ IncompatibleLinear p (CoreMultiplicity Internal l) (CoreMultiplicity Internal l')

matchLinear p (CoreMultiplicity Internal l) (CoreMultiplicity Internal l') = matchLinear' p l l'

matchKind' _ (KindVariable x) (KindVariable x') | x == x' = pure ()
matchKind' p (Type s) (Type s') = do
  matchKind p s s'
matchKind' p (Higher κ1 κ2) (Higher κ1' κ2') = do
  matchKind p κ1 κ1'
  matchKind p κ2 κ2'
matchKind' p (Runtime ρ) (Runtime ρ') = matchKind p ρ ρ'
matchKind' _ Meta Meta = pure ()
matchKind' _ PointerRep PointerRep = pure ()
matchKind' _ FunctionRep FunctionRep = pure ()
matchKind' p κ κ' = quit $ IncompatibleKind p (CoreKind Internal κ) (CoreKind Internal κ')

matchKind p (CoreKind Internal κ) (CoreKind Internal κ') = matchKind' p κ κ'

matchType' _ (TypeVariable x) (TypeVariable x') | x == x' = pure ()
matchType' p (Macro σ τ) (Macro σ' τ') = zipWithM (matchType p) [σ, τ] [σ', τ'] >> pure ()
matchType' p (Forall (Bound (CoreTypePattern Internal (TypePatternVariable x κ)) σ)) (Forall (Bound (CoreTypePattern Internal (TypePatternVariable x' κ')) σ')) = do
  matchKind p κ κ'
  matchType p σ (substitute (CoreType Internal $ TypeVariable x) x' σ')
  pure ()
matchType' p (KindForall (Bound (CoreKindPattern Internal (KindPatternVariable x μ)) σ)) (KindForall (Bound (CoreKindPattern Internal (KindPatternVariable x' μ')) σ')) = do
  matchSort p μ μ'
  matchType p σ (substitute (CoreKind Internal $ KindVariable x) x' σ')
  pure ()
matchType' p (OfCourse σ) (OfCourse σ') = do
  matchType p σ σ'
matchType' p (TypeConstruction σ τ) (TypeConstruction σ' τ') = do
  matchType p σ σ'
  matchType p τ τ'
matchType' p (TypeOperator (Bound (CoreTypePattern Internal (TypePatternVariable x κ)) σ)) (TypeOperator (Bound (CoreTypePattern Internal (TypePatternVariable x' κ')) σ')) = do
  matchKind p κ κ'
  matchType p σ (substitute (CoreType Internal $ TypeVariable x) x' σ')
matchType' p (FunctionPointer σ τs) (FunctionPointer σ' τs') = do
  matchType p σ σ'
  sequence $ zipWith (matchType p) τs τs'
  pure ()
matchType' p σ σ' = quit $ IncompatibleType p (CoreType Internal σ) (CoreType Internal σ')

matchType p (CoreType Internal σ) (CoreType Internal σ') = matchType' p σ σ'

checkKind _ Kind = pure ()
checkKind p μ = quit $ ExpectedKind p μ

checkStage _ Stage = pure ()
checkStage p μ = quit $ ExpectedStage p μ

checkRepresentation _ Representation = pure ()
checkRepresentation p μ = quit $ ExpectedRepresentation p μ

checkType _ (CoreKind Internal (Type κ)) = pure κ
checkType p κ = quit $ ExpectedType p κ

checkHigher _ (CoreKind Internal (Higher κ κ')) = pure (κ, κ')
checkHigher p κ = quit $ ExpectedHigher p κ

checkRuntime _ (CoreKind Internal (Runtime κ)) = pure κ
checkRuntime p κ = quit $ ExpectedRuntime p κ

checkMacro _ (CoreType Internal (Macro σ τ)) = pure (σ, τ)
checkMacro p σ = quit $ ExpectedMacro p σ

checkForall _ (CoreType Internal (Forall (Bound pm σ))) = pure $ Bound pm σ
checkForall p σ = quit $ ExpectedForall p σ

checkKindForall _ (CoreType Internal (KindForall (Bound pm σ))) = pure $ Bound pm σ
checkKindForall p σ = quit $ ExpectedKindForall p σ

checkOfCourse _ (CoreType Internal (OfCourse σ)) = pure σ
checkOfCourse p σ = quit $ ExpectedOfCourse p σ

checkFunctionPointer _ n (CoreType Internal (FunctionPointer σ τs)) | n == length τs = pure (σ, τs)
checkFunctionPointer p n σ = quit $ ExpectedFunctionPointer p n σ

class Augment p pm | pm -> p where
  augment :: Base p m => pm -> Core p m a -> Core p m a

class AugmentLinear p pm | pm -> p where
  augmentLinear :: Base p m => pm -> MultiplicityInternal -> Core p m (a, Use) -> Core p m (a, Use)

class Instantiate p e e' | e -> e', e -> p where
  instantiate :: Base p m => e -> Core p m e'

instantiateDefault = fmap fst . typeCheckInstantiate

class TypeCheck p e σ | e -> σ, e -> p where
  typeCheck :: Base p m => e -> Core p m σ

class (TypeCheck p e σ, Instantiate p e e') => TypeCheckInstantiate p e e' σ | e -> e', e -> σ, e -> p where
  typeCheckInstantiate :: Base p m => e -> Core p m (e', σ)

class TypeCheck p e σ => TypeCheckLinear p e σ | e -> σ, e -> p where
  typeCheckLinear :: Base p m => e -> Core p m (σ, Use)

augmentKindVariable p x μ κ = do
  env <- Core get
  let μΓ = sortEnvironment env
  Core $ put env {sortEnvironment = Map.insert x (p, μ) μΓ}
  μ' <- κ
  Core $ put env
  pure μ'

augmentTypeVariable p x κ σ = do
  env <- Core get
  let κΓ = kindEnvironment env
  Core $ put env {kindEnvironment = Map.insert x (p, κ) κΓ}
  κ' <- σ
  Core $ put env
  pure κ'

augmentVariableLinear p x l σ e = do
  env <- Core get
  let σΓ = typeEnvironment env
  Core $ put env {typeEnvironment = Map.insert x (p, l, σ) σΓ}
  (σ', lΓ) <- e
  Core $ put env
  case (count x lΓ, l) of
    (Single, _) -> pure ()
    (_, CoreMultiplicity Internal Unrestricted) -> pure ()
    (_, _) -> quit $ InvalidUsage p x
  pure (σ', Remove x lΓ)

instance Augment p (KindPattern p) where
  augment (CoreKindPattern p (KindPatternVariable x μ)) κ = augmentKindVariable p x μ κ

instance Augment p (TypePattern Internal p) where
  augment (CoreTypePattern p (TypePatternVariable x κ)) σ = augmentTypeVariable p x κ σ

instance AugmentLinear p (Pattern Internal p) where
  augmentLinear (CorePattern p (PatternVariable x σ)) l e = augmentVariableLinear p x l σ e
  augmentLinear (CorePattern _ (PatternOfCourse pm)) _ e = augmentLinear pm (CoreMultiplicity Internal Unrestricted) e

instance Instantiate p (Kind p) KindInternal where
  instantiate = instantiateDefault

instance Instantiate p (Type p) TypeInternal where
  instantiate = instantiateDefault

instance TypeCheckInstantiate p (Kind p) KindInternal Sort where
  typeCheckInstantiate κ = do
    μ <- typeCheck κ
    pure (Internal <$ κ, μ)

instance TypeCheckInstantiate p (Type p) TypeInternal KindInternal where
  typeCheckInstantiate σ = do
    κ <- typeCheck σ
    pure (reduce $ Internal <$ σ, κ)

instance Instantiate p (Pattern p p) (Pattern Internal p) where
  instantiate = instantiateDefault

instance TypeCheck p (Pattern p p) TypeInternal where
  typeCheck = fmap snd . typeCheckInstantiate

instance TypeCheckInstantiate p (Pattern p p) (Pattern Internal p) TypeInternal where
  typeCheckInstantiate (CorePattern p (PatternVariable x σ')) = do
    (σ, κ) <- typeCheckInstantiate σ'
    checkType p κ
    pure (CorePattern p (PatternVariable x σ), σ)
  typeCheckInstantiate (CorePattern p (PatternOfCourse pm')) = do
    (pm, σ) <- typeCheckInstantiate pm'
    pure (CorePattern p (PatternOfCourse pm), CoreType Internal $ OfCourse $ σ)

instance Instantiate p (TypePattern p p) (TypePattern Internal p) where
  instantiate = instantiateDefault

instance TypeCheck p (TypePattern p p) KindInternal where
  typeCheck = fmap snd . typeCheckInstantiate

instance TypeCheckInstantiate p (TypePattern p p) (TypePattern Internal p) KindInternal where
  typeCheckInstantiate (CoreTypePattern p (TypePatternVariable x κ')) = do
    (κ, μ) <- typeCheckInstantiate κ'
    checkKind p μ
    pure (CoreTypePattern p (TypePatternVariable x κ), κ)

instance Instantiate p (KindPattern p) (KindPattern p) where
  instantiate = instantiateDefault

instance TypeCheck p (KindPattern p) Sort where
  typeCheck = fmap snd . typeCheckInstantiate

instance TypeCheckInstantiate p (KindPattern p) (KindPattern p) Sort where
  typeCheckInstantiate pmκ@(CoreKindPattern _ (KindPatternVariable _ μ)) = pure (pmκ, μ)

instance TypeCheck p (Kind p) Sort where
  typeCheck (CoreKind p (KindVariable x)) = do
    enviroment <- Core get
    case sortEnvironment enviroment !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, μ) -> pure μ
  typeCheck (CoreKind p (Type κ)) = do
    checkStage p =<< typeCheck κ
    pure $ Kind
  typeCheck (CoreKind p (Higher κ κ')) = do
    checkKind p =<< typeCheck κ
    checkKind p =<< typeCheck κ'
    pure $ Kind
  typeCheck (CoreKind _ Meta) = do
    pure $ Stage
  typeCheck (CoreKind p (Runtime κ)) = do
    checkRepresentation p =<< typeCheck κ
    pure $ Stage
  typeCheck (CoreKind _ PointerRep) = do
    pure $ Representation
  typeCheck (CoreKind _ FunctionRep) = do
    pure $ Representation

instance TypeCheck p (Type p) KindInternal where
  typeCheck (CoreType p (TypeVariable x)) = do
    enviroment <- Core get
    case kindEnvironment enviroment !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, κ) -> pure κ
  typeCheck (CoreType p (Macro σ τ)) = do
    checkType p =<< typeCheck σ
    checkType p =<< typeCheck τ
    pure $ CoreKind Internal (Type (CoreKind Internal Meta))
  typeCheck (CoreType p (Forall (Bound pm' σ))) = do
    pm <- instantiate pm'
    κ <- checkType p =<< augment pm (typeCheck σ)
    pure $ CoreKind Internal (Type κ)
  typeCheck (CoreType p (KindForall (Bound pm' σ))) = do
    pm <- instantiate pm'
    checkType p =<< augment pm (typeCheck σ)
    pure $ CoreKind Internal (Type (CoreKind Internal Meta))
  typeCheck (CoreType p (OfCourse σ)) = do
    checkType p =<< typeCheck σ
    pure $ CoreKind Internal (Type (CoreKind Internal Meta))
  typeCheck (CoreType p (TypeConstruction σ τ)) = do
    (κ1, κ2) <- checkHigher p =<< typeCheck σ
    κ1' <- typeCheck τ
    matchKind p κ1 κ1'
    pure $ κ2
  typeCheck (CoreType _ (TypeOperator (Bound pm' σ))) = do
    (pm, κ') <- typeCheckInstantiate pm'
    κ <- augment pm (typeCheck σ)
    pure (CoreKind Internal (Higher κ' κ))
  typeCheck (CoreType p (FunctionPointer σ τs)) = do
    checkRuntime p =<< checkType p =<< typeCheck σ
    traverse (checkRuntime p <=< checkType p <=< typeCheck) τs
    pure $ CoreKind Internal (Type (CoreKind Internal (Runtime (CoreKind Internal FunctionRep))))

instance TypeCheck p (Term d p) TypeInternal where
  typeCheck = fmap fst . typeCheckLinear

capture p lΓ = do
  let captures = variablesUsed lΓ
  env <- Core get
  let lΓ = typeEnvironment env
  for (Set.toList captures) $ \x' -> do
    let (_, l, _) = lΓ ! x'
    case l of
      CoreMultiplicity Internal Unrestricted -> pure ()
      _ -> quit $ CaptureLinear p x'
  pure ()

instance TypeCheckLinear p (Term d p) TypeInternal where
  typeCheckLinear (CoreTerm p (Variable _ x)) = do
    enviroment <- Core get
    case typeEnvironment enviroment !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, _, σ) -> pure (σ, Use x)
  typeCheckLinear (CoreTerm _ (MacroAbstraction _ (Bound pm' e))) = do
    (pm, σ) <- typeCheckInstantiate pm'
    (τ, lΓ) <- augmentLinear pm (CoreMultiplicity Internal Linear) (typeCheckLinear e)
    pure (CoreType Internal $ Macro σ τ, lΓ)
  typeCheckLinear (CoreTerm p (MacroApplication _ e1 e2)) = do
    ((σ, τ), lΓ1) <- firstM (checkMacro p) =<< typeCheckLinear e1
    (σ', lΓ2) <- typeCheckLinear e2
    matchType p σ σ'
    pure (τ, lΓ1 `combine` lΓ2)
  typeCheckLinear (CoreTerm _ (TypeAbstraction _ (Bound pm' e))) = do
    pm <- instantiate pm'
    (σ, lΓ) <- augment pm (typeCheckLinear e)
    pure (CoreType Internal (Forall (Bound (Internal <$ pm) σ)), lΓ)
  typeCheckLinear (CoreTerm p (TypeApplication _ e σ')) = do
    (σ, κ) <- typeCheckInstantiate σ'
    (λ@(Bound pm _), lΓ) <- firstM (checkForall p) =<< typeCheckLinear e
    κ' <- typeCheckInternal pm
    matchKind p κ κ'
    pure (apply λ σ, lΓ)
  typeCheckLinear (CoreTerm _ (KindAbstraction _ (Bound pm' e))) = do
    pm <- instantiate pm'
    (σ, lΓ) <- augment pm (typeCheckLinear e)
    pure (CoreType Internal (KindForall (Bound (Internal <$ pm) σ)), lΓ)
  typeCheckLinear (CoreTerm p (KindApplication _ e κ')) = do
    (κ, μ) <- typeCheckInstantiate κ'
    (λ@(Bound pm _), lΓ) <- firstM (checkKindForall p) =<< typeCheckLinear e
    μ' <- typeCheckInternal pm
    matchSort p μ μ'
    pure (apply λ κ, lΓ)
  typeCheckLinear (CoreTerm p (OfCourseIntroduction _ e)) = do
    (σ, lΓ) <- typeCheckLinear e
    capture p lΓ
    pure (CoreType Internal $ OfCourse σ, lΓ)
  typeCheckLinear (CoreTerm p (Bind _ e1 (Bound pm' e2))) = do
    (pm, τ) <- typeCheckInstantiate pm'
    (τ', lΓ1) <- typeCheckLinear e1
    matchType p τ τ'
    (σ, lΓ2) <- augmentLinear pm (CoreMultiplicity Internal Linear) (typeCheckLinear e2)
    pure (σ, lΓ1 `combine` lΓ2)
  typeCheckLinear (CoreTerm p (Extern _ _ _ σ' τs')) = do
    (σ, κ) <- typeCheckInstantiate σ'
    checkRuntime p =<< checkType p κ
    (τs, κ's) <- unzip <$> traverse typeCheckInstantiate τs'
    traverse (checkRuntime p <=< checkType p) κ's
    pure (CoreType Internal (FunctionPointer σ τs), useNothing)
  typeCheckLinear (CoreTerm p (FunctionApplication _ _ e1 e2s)) = do
    ((σ, τs), lΓ1) <- firstM (checkFunctionPointer p (length e2s)) =<< typeCheckLinear e1
    (τs', lΓ2s) <- unzip <$> traverse typeCheckLinear e2s
    sequence $ zipWith (matchType p) τs τs'
    pure (σ, lΓ1 `combine` combineAll lΓ2s)

typeCheckInternal σ = do
  env <- Core get
  pure $ runIdentity $ runCore (typeCheck σ) (Internal <$ env)

instance TypeCheck p (FunctionLiteral d p) TypeInternal where
  typeCheck (FunctionLiteral _ _ p [] σ' pms' e) = do
    (pms, τs) <- unzip <$> traverse typeCheckInstantiate pms'
    traverse (checkRuntime p <=< checkType p <=< typeCheckInternal) τs
    (σ, κ) <- typeCheckInstantiate σ'
    checkRuntime p =<< checkType p κ
    (σ', _) <- foldr (flip augmentLinear $ CoreMultiplicity Internal Linear) (typeCheckLinear e) pms
    matchType p σ σ'
    pure $ CoreType Internal (FunctionPointer σ τs)
  typeCheck (FunctionLiteral dσ dpms p (pmσ' : pmσs) σ pms e) = do
    pmσ <- instantiate pmσ'
    σ <- augment pmσ (typeCheck $ FunctionLiteral dσ dpms p pmσs σ pms e)
    pure $ CoreType Internal (Forall (Bound (Internal <$ pmσ) σ))
