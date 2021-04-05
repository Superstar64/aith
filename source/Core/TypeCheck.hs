module Core.TypeCheck where

import Control.Monad.Trans.Class (MonadTrans, lift)
import Control.Monad.Trans.State (StateT, evalStateT, get, put)
import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.KindPattern
import Core.Ast.Multiplicity
import Core.Ast.Pattern
import Core.Ast.Sort
import Core.Ast.Term
import Core.Ast.Type
import Core.Ast.TypePattern
import Data.Bifunctor (first)
import Data.Map (Map, (!), (!?))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (for)
import Environment
import Error
import Misc.Identifier (Identifier)
import Misc.Util (zipWithM)
import qualified TypeSystem.Forall as TypeSystem
import qualified TypeSystem.Function as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.OfCourse as TypeSystem
import qualified TypeSystem.PatternVariable as TypeSystem
import qualified TypeSystem.Representation as TypeSystem
import qualified TypeSystem.Runtime as TypeSystem
import qualified TypeSystem.Stage as TypeSystem
import qualified TypeSystem.StageForall as TypeSystem
import qualified TypeSystem.Type as TypeSystem

data CoreState p = CoreState
  { typeEnvironment :: Map Identifier (p, MultiplicityInternal, TypeInternal),
    kindEnvironment :: Map Identifier (p, KindInternal),
    sortEnvironment :: Map Identifier (p, Sort)
  }
  deriving (Show, Functor)

emptyState = CoreState Map.empty Map.empty Map.empty

newtype Core p m a = Core {runCore' :: StateT (CoreState p) m a} deriving (Functor, Applicative, Monad, MonadTrans)

runCore c = evalStateT (runCore' c)

quit :: Base p m => Error p -> Core p m a
quit e = Core (lift $ quit' e)

matchSort _ Kind Kind = pure ()
matchSort _ Stage Stage = pure ()
matchSort _ Representation Representation = pure ()
matchSort p μ μ' = quit $ IncompatibleSort p μ μ'

matchLinear' _ Linear Linear = pure ()
matchLinear' _ Unrestricted Unrestricted = pure ()
matchLinear' p l l' = quit $ IncompatibleLinear p (CoreMultiplicity Internal l) (CoreMultiplicity Internal l')

matchLinear p (CoreMultiplicity Internal l) (CoreMultiplicity Internal l') = matchLinear' p l l'

matchRepresentation _ PointerRep PointerRep = pure ()
matchRepresentation _ FunctionRep FunctionRep = pure ()
matchRepresentation p ρ ρ' = quit $ IncompatibleRepresentation p ρ ρ'

matchKind' _ (KindVariable x) (KindVariable x') | x == x' = pure ()
matchKind' p (Type s) (Type s') = do
  matchKind p s s'
matchKind' p (Higher κ1 κ2) (Higher κ1' κ2') = do
  matchKind p κ1 κ1'
  matchKind p κ2 κ2'
matchKind' p (Runtime ρ) (Runtime ρ') = matchKind p ρ ρ'
matchKind' _ Meta Meta = pure ()
matchKind' p (RepresentationLiteral ρ) (RepresentationLiteral ρ') = matchRepresentation p ρ ρ'
matchKind' p κ κ' = quit $ IncompatibleKind p (CoreKind Internal κ) (CoreKind Internal κ')

matchKind p (CoreKind Internal κ) (CoreKind Internal κ') = matchKind' p κ κ'

matchType' _ (TypeVariable x) (TypeVariable x') | x == x' = pure ()
matchType' p (Macro σ τ) (Macro σ' τ') = zipWithM (matchType p) [σ, τ] [σ', τ'] >> pure ()
matchType' p (Forall (CoreTypePattern Internal (TypePatternVariable x κ)) σ) (Forall (CoreTypePattern Internal (TypePatternVariable x' κ')) σ') = do
  matchKind p κ κ'
  matchType p σ (substitute (CoreType Internal $ TypeVariable x) x' σ')
  pure ()
matchType' p (KindForall (CoreKindPattern Internal (KindPatternVariable x μ)) σ) (KindForall (CoreKindPattern Internal (KindPatternVariable x' μ')) σ') = do
  matchSort p μ μ'
  matchType p σ (substitute (CoreKind Internal $ KindVariable x) x' σ')
  pure ()
matchType' p (OfCourse σ) (OfCourse σ') = do
  matchType p σ σ'
matchType' p (TypeConstruction σ τ) (TypeConstruction σ' τ') = do
  matchType p σ σ'
  matchType p τ τ'
matchType' p (TypeOperator (CoreTypePattern Internal (TypePatternVariable x κ)) σ) (TypeOperator (CoreTypePattern Internal (TypePatternVariable x' κ')) σ') = do
  matchKind p κ κ'
  matchType p σ (substitute (CoreType Internal $ TypeVariable x) x' σ')
matchType' p σ σ' = quit $ IncompatibleType p (CoreType Internal σ) (CoreType Internal σ')

matchType p (CoreType Internal σ) (CoreType Internal σ') = matchType' p σ σ'

instance Base p m => TypeCheckLinear TypeInternal (Core p m) (Term p) Use where
  typeCheckLinear (CoreTerm p e) = typeCheckLinearImpl p $ projectTerm e

instance Base p m => TypeCheck PatternSort (Core p m) (Pattern (Type p) p) where
  typeCheck (CorePattern p pm) = typeCheckImpl p $ projectPattern pm

instance Base p m => TypeCheck KindInternal (Core p m) (Type p) where
  typeCheck (CoreType p σ) = typeCheckImpl p $ projectType σ

instance Base p m => TypeCheck TypePatternSort (Core p m) (TypePattern (Kind p) p) where
  typeCheck (CoreTypePattern p pm) = typeCheckImpl p $ projectTypePattern pm

instance Base p m => TypeCheck Sort (Core p m) (Kind p) where
  typeCheck (CoreKind p κ) = typeCheckImpl p $ projectKind κ

instance Base p m => TypeCheckImpl (Core p m) p Representation Sort where
  typeCheckImpl _ _ = pure $ Representation

instance Base p m => TypeCheckInstantiate KindInternal TypeInternal (Core p m) (Type p) where
  typeCheckInstantiate σ = do
    κ <- typeCheck σ
    pure (κ, reduce $ Internal <$ σ)

instance Base p m => TypeCheckInstantiate Sort KindInternal (Core p m) (Kind p) where
  typeCheckInstantiate κ = do
    μ <- typeCheck κ
    pure (μ, Internal <$ κ)

instance Base p m => TypeCheckInstantiate PatternSort (Pattern TypeInternal p) (Core p m) (Pattern (Type p) p) where
  typeCheckInstantiate pm = do
    Pattern <- typeCheck pm
    pure (Pattern, first (reduce . (Internal <$)) pm)

instance Base p m => TypeCheckInstantiate TypePatternSort (TypePattern KindInternal p) (Core p m) (TypePattern (Kind p) p) where
  typeCheckInstantiate pm = do
    TypePattern <- typeCheck pm
    pure (TypePattern, first (reduce . (Internal <$)) pm)

instance Base p m => Instantiate (Pattern TypeInternal p) (Core p m) (Pattern (Type p) p) where
  instantiate = fmap snd . typeCheckInstantiate @PatternSort

instance Base p m => Instantiate (TypePattern KindInternal p) (Core p m) (TypePattern (Kind p) p) where
  instantiate = fmap snd . typeCheckInstantiate @TypePatternSort

instance Base p m => Instantiate (KindPattern p) (Core p m) (KindPattern p) where
  instantiate = pure

instance Base p m => Instantiate KindInternal (Core p m) (Kind p) where
  instantiate = fmap snd . typeCheckInstantiate @Sort

instance Base p m => SameType (Core p m) p TypeInternal where
  sameType p σ σ' = matchType p σ σ'

instance Base p m => SameType (Core p m) p KindInternal where
  sameType p κ κ' = matchKind p κ κ'

instance Base p m => SameType (Core p m) p Sort where
  sameType p μ μ' = matchSort p μ μ'

instance Base p m => TypeSystem.CheckFunction (Core p m) p TypeInternal where
  checkFunction _ (CoreType Internal (Macro σ τ)) = pure (TypeSystem.Function σ τ)
  checkFunction p σ = quit $ ExpectedMacro p σ

instance Base p m => TypeSystem.CheckForall' (Core p m) p KindInternal TypeInternal where
  checkForall' _ (CoreType Internal (Forall pm σ)) = pure (internalType pm, \τ -> reducePattern pm τ σ)
  checkForall' p σ = quit $ ExpectedForall p σ

instance Base p m => TypeSystem.CheckStageForall' Sort KindInternal (Core p m) p TypeInternal where
  checkStageForall' _ (CoreType Internal (KindForall pm σ)) = pure $ (internalType pm, \s -> reducePattern pm s σ)
  checkStageForall' p σ = quit $ ExpectedKindForall p σ

instance Base p m => TypeSystem.CheckOfCourse (Core p m) p TypeInternal where
  checkOfCourse _ (CoreType Internal (OfCourse σ)) = pure (TypeSystem.OfCourse σ)
  checkOfCourse p σ = quit $ ExpectedOfCourse p σ

instance Base p m => TypeSystem.CheckType KindInternal KindInternal (Core p m) p where
  checkType _ (CoreKind Internal (Type s)) = pure (TypeSystem.Type s)
  checkType p κ = quit $ ExpectedType p κ

instance Base p m => TypeSystem.CheckRuntime KindInternal KindInternal (Core p m) p where
  checkRuntime _ (CoreKind Internal (Runtime ρ)) = pure (TypeSystem.Runtime ρ)
  checkRuntime p s = quit $ ExpectedRuntime p s

instance Base p m => TypeSystem.CheckType () Sort (Core p m) p where
  checkType _ Kind = pure (TypeSystem.Type ())
  checkType p μ = quit $ ExpectedKind p μ

instance Base p m => TypeSystem.CheckFunction (Core p m) p KindInternal where
  checkFunction _ (CoreKind Internal (Higher κ κ')) = pure (TypeSystem.Function κ κ')
  checkFunction p κ = quit $ ExpectedHigher p κ

instance Base p m => TypeSystem.CheckStage Sort p (Core p m) where
  checkStage _ Stage = pure TypeSystem.Stage
  checkStage p μ = quit $ ExpectedStage p μ

instance Base p m => TypeSystem.CheckRepresentation Sort p (Core p m) where
  checkRepresentation _ Representation = pure TypeSystem.Representation
  checkRepresentation p μ = quit $ ExpectedRepresentation p μ

instance Base p m => ReadEnvironmentLinear (Core p m) p TypeInternal Use where
  readEnvironmentLinear p x = do
    env <- Core get
    case typeEnvironment env !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, _, σ) -> pure (σ, Use x)

instance Base p m => TypeSystem.AugmentVariableLinear (Core p m) p MultiplicityInternal TypeInternal Use where
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

instance Base p m => AugmentLinear (Core p m) (Pattern TypeInternal p) MultiplicityInternal Use where
  augmentLinear (CorePattern p pm) l e = augmentLinearImpl p (projectPattern pm) l e

instance Base p m => ReadEnvironment (Core p m) p KindInternal where
  readEnvironment p x = do
    env <- Core get
    case kindEnvironment env !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, κ) -> pure κ

instance Base p m => ReadEnvironment (Core p m) p Sort where
  readEnvironment p x = do
    env <- Core get
    case sortEnvironment env !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, μ) -> pure μ

augmentEnvironmentKind p x κ e = do
  env <- Core get
  let κΓ = kindEnvironment env
  Core $ put env {kindEnvironment = Map.insert x (p, κ) κΓ}
  c <- e
  Core $ put env
  pure c

instance Base p m => Augment (Core p m) (TypePattern KindInternal p) where
  augment (CoreTypePattern p (TypePatternVariable x κ)) e = augmentEnvironmentKind p x κ e

augmentEnvironmentSort p x μ e = do
  env <- Core get
  let μΓ = sortEnvironment env
  Core $ put env {sortEnvironment = Map.insert x (p, μ) μΓ}
  c <- e
  Core $ put env
  pure c

instance Base p m => Augment (Core p m) (KindPattern p) where
  augment (CoreKindPattern p (KindPatternVariable x μ)) e = augmentEnvironmentSort p x μ e

instance Base p m => Capture (Core p m) p MultiplicityInternal Use where
  capture _ (CoreMultiplicity Internal Linear) _ = pure ()
  capture p (CoreMultiplicity Internal Unrestricted) lΓ = do
    let captures = variables lΓ
    env <- Core get
    let lΓ = typeEnvironment env
    for (Set.toList captures) $ \x' -> do
      let (_, l, _) = lΓ ! x'
      case l of
        CoreMultiplicity Internal Unrestricted -> pure ()
        _ -> quit $ CaptureLinear p x'
    pure ()

typeCheckTerm :: forall p m. Base p m => Term p -> Core p m TypeInternal
typeCheckTerm e = do
  (σ, _) <- typeCheckLinear e :: Core p m (TypeInternal, Use)
  pure σ

typeCheckType :: forall p m. Base p m => Type p -> Core p m KindInternal
typeCheckType = typeCheck

substituteTerm :: TermInternal -> Identifier -> TermInternal -> TermInternal
substituteTerm = substitute

reduceTerm :: TermInternal -> TermInternal
reduceTerm = reduce
