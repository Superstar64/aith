module Core.TypeCheck where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (Except, except, runExcept)
import Control.Monad.Trans.State (StateT, get, put, runStateT)
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
import Data.Void (Void)
import Environment
import Misc.Identifier
import Misc.Util (zipWithM)
import qualified TypeSystem.Forall as TypeSystem
import qualified TypeSystem.Function as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.OfCourse as TypeSystem
import qualified TypeSystem.PatternVariable as TypeSystem
import qualified TypeSystem.Representation as TypeSystem
import qualified TypeSystem.Stage as TypeSystem
import qualified TypeSystem.StageForall as TypeSystem
import qualified TypeSystem.Type as TypeSystem

data Error p
  = UnknownIdentfier p Identifier
  | ExpectedMacro p TypeInternal
  | ExpectedForall p TypeInternal
  | ExpectedKindForall p TypeInternal
  | ExpectedOfCourse p TypeInternal
  | ExpectedType p KindInternal
  | ExpectedHigher p KindInternal
  | ExpectedKind p Sort
  | ExpectedStage p Sort
  | ExpectedRepresentation p Sort
  | IncompatibleType p TypeInternal TypeInternal
  | IncompatibleKind p KindInternal KindInternal
  | IncompatibleLinear p MultiplicityInternal MultiplicityInternal
  | IncompatibleSort p Sort Sort
  | IncompatibleRepresentation p Representation Representation
  | CaptureLinear p Identifier
  | InvalidUsage p Identifier
  deriving (Show)

class FromError p a where
  fromError :: Error p -> a

instance FromError p (Error p) where
  fromError = id

instance FromError Internal Void where
  fromError q = error (show q)

data CoreState p = CoreState
  { typeEnvironment :: Map Identifier (p, MultiplicityInternal, TypeInternal),
    kindEnvironment :: Map Identifier (p, KindInternal),
    sortEnvironment :: Map Identifier (p, Sort)
  }
  deriving (Show, Functor)

newtype Core p q a = Core {runCore' :: StateT (CoreState p) (Except q) a} deriving (Functor, Applicative, Monad)

runCore c env = runExcept (runStateT (runCore' c) env)

quit e = Core (lift $ except (Left (fromError e)))

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

matchType' :: FromError p q => p -> TypeF Internal -> TypeF Internal -> Core p q ()
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

matchType :: FromError p q => p -> TypeInternal -> TypeInternal -> Core p q ()
matchType p (CoreType Internal σ) (CoreType Internal σ') = matchType' p σ σ'

instance (FromError p q) => TypeCheckLinear TypeInternal (Core p q) (Term p) Use where
  typeCheckLinear (CoreTerm p e) = typeCheckLinearImpl p $ projectTerm e

instance (FromError p q) => TypeCheck PatternSort (Core p q) (Pattern (Type p) p) where
  typeCheck (CorePattern p pm) = typeCheckImpl p $ projectPattern pm

instance (FromError p q) => TypeCheck KindInternal (Core p q) (Type p) where
  typeCheck (CoreType p σ) = typeCheckImpl p $ projectType σ

instance (FromError p q) => TypeCheck TypePatternSort (Core p q) (TypePattern (Kind p) p) where
  typeCheck (CoreTypePattern p pm) = typeCheckImpl p $ projectTypePattern pm

instance (FromError p q) => TypeCheck Sort (Core p q) (Kind p) where
  typeCheck (CoreKind p κ) = typeCheckImpl p $ projectKind κ

instance TypeCheckImpl (Core p q) p Representation Sort where
  typeCheckImpl _ _ = pure $ Representation

instance (FromError p q) => TypeCheckInstantiate KindInternal TypeInternal (Core p q) (Type p) where
  typeCheckInstantiate σ = do
    κ <- typeCheck σ
    pure (κ, reduce $ Internal <$ σ)

instance (FromError p q) => TypeCheckInstantiate Sort KindInternal (Core p q) (Kind p) where
  typeCheckInstantiate κ = do
    μ <- typeCheck κ
    pure (μ, Internal <$ κ)

instance (FromError p q) => TypeCheckInstantiate PatternSort (Pattern TypeInternal p) (Core p q) (Pattern (Type p) p) where
  typeCheckInstantiate pm = do
    Pattern <- typeCheck pm
    pure (Pattern, first (reduce . (Internal <$)) pm)

instance (FromError p q) => TypeCheckInstantiate TypePatternSort (TypePattern KindInternal p) (Core p q) (TypePattern (Kind p) p) where
  typeCheckInstantiate pm = do
    TypePattern <- typeCheck pm
    pure (TypePattern, first (reduce . (Internal <$)) pm)

instance (FromError p q) => Instantiate (Pattern TypeInternal p) (Core p q) (Pattern (Type p) p) where
  instantiate = fmap snd . typeCheckInstantiate @PatternSort

instance (FromError p q) => Instantiate (TypePattern KindInternal p) (Core p q) (TypePattern (Kind p) p) where
  instantiate = fmap snd . typeCheckInstantiate @TypePatternSort

instance Instantiate (KindPattern p) (Core p q) (KindPattern p) where
  instantiate = pure

instance (FromError p q) => Instantiate KindInternal (Core p q) (Kind p) where
  instantiate = fmap snd . typeCheckInstantiate @Sort

instance (FromError p q) => SameType (Core p q) p TypeInternal where
  sameType p σ σ' = matchType p σ σ'

instance (FromError p q) => SameType (Core p' q) p KindInternal where
  sameType p κ κ' = matchKind p κ κ'

instance FromError p q => SameType (Core p' q) p Sort where
  sameType p μ μ' = matchSort p μ μ'

instance (FromError p' q) => TypeSystem.CheckFunction (Core p q) p' TypeInternal where
  checkFunction _ (CoreType Internal (Macro σ τ)) = pure (TypeSystem.Function σ τ)
  checkFunction p σ = quit $ ExpectedMacro p σ

instance (FromError p' q) => TypeSystem.CheckForall' (Core p q) p' KindInternal TypeInternal where
  checkForall' _ (CoreType Internal (Forall pm σ)) = pure (internalType pm, \τ -> reducePattern pm τ σ)
  checkForall' p σ = quit $ ExpectedForall p σ

instance (FromError p' q) => TypeSystem.CheckStageForall' Sort KindInternal (Core p q) p' TypeInternal where
  checkStageForall' _ (CoreType Internal (KindForall pm σ)) = pure $ (internalType pm, \s -> reducePattern pm s σ)
  checkStageForall' p σ = quit $ ExpectedKindForall p σ

instance (FromError p' q) => TypeSystem.CheckOfCourse (Core p q) p' TypeInternal where
  checkOfCourse _ (CoreType Internal (OfCourse σ)) = pure (TypeSystem.OfCourse σ)
  checkOfCourse p σ = quit $ ExpectedOfCourse p σ

instance (FromError p' q) => TypeSystem.CheckType KindInternal KindInternal (Core p q) p' where
  checkType _ (CoreKind Internal (Type s)) = pure (TypeSystem.Type s)
  checkType p κ = quit $ ExpectedType p κ

instance FromError p' q => TypeSystem.CheckType () Sort (Core p q) p' where
  checkType _ Kind = pure (TypeSystem.Type ())
  checkType p μ = quit $ ExpectedKind p μ

instance (FromError p' q) => TypeSystem.CheckFunction (Core p q) p' KindInternal where
  checkFunction _ (CoreKind Internal (Higher κ κ')) = pure (TypeSystem.Function κ κ')
  checkFunction p κ = quit $ ExpectedHigher p κ

instance FromError p q => TypeSystem.CheckStage Sort p (Core p' q) where
  checkStage _ Stage = pure TypeSystem.Stage
  checkStage p μ = quit $ ExpectedStage p μ

instance FromError p q => TypeSystem.CheckRepresentation Sort p (Core p' q) where
  checkRepresentation _ Representation = pure TypeSystem.Representation
  checkRepresentation p μ = quit $ ExpectedRepresentation p μ

instance (FromError p q) => ReadEnvironmentLinear (Core p q) p TypeInternal Use where
  readEnvironmentLinear p x = do
    env <- Core get
    case typeEnvironment env !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, _, σ) -> pure (σ, Use x)

instance (FromError p q) => TypeSystem.AugmentVariableLinear (Core p q) p MultiplicityInternal TypeInternal Use where
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

instance (FromError p q) => AugmentLinear (Core p q) (Pattern TypeInternal p) MultiplicityInternal Use where
  augmentLinear (CorePattern p pm) l e = augmentLinearImpl p (projectPattern pm) l e

instance (FromError p q) => ReadEnvironment (Core p q) p KindInternal where
  readEnvironment p x = do
    env <- Core get
    case kindEnvironment env !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, κ) -> pure κ

instance (FromError p q) => ReadEnvironment (Core p q) p Sort where
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

instance Augment (Core p q) (TypePattern KindInternal p) where
  augment (CoreTypePattern p (TypePatternVariable x κ)) e = augmentEnvironmentKind p x κ e

augmentEnvironmentSort p x μ e = do
  env <- Core get
  let μΓ = sortEnvironment env
  Core $ put env {sortEnvironment = Map.insert x (p, μ) μΓ}
  c <- e
  Core $ put env
  pure c

instance Augment (Core p q) (KindPattern p) where
  augment (CoreKindPattern p (KindPatternVariable x μ)) e = augmentEnvironmentSort p x μ e

instance (FromError p' q) => Capture (Core p q) p' MultiplicityInternal Use where
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
