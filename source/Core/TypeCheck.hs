module Core.TypeCheck where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (Except, except, runExcept)
import Control.Monad.Trans.State (StateT, get, put, runStateT)
import Core.Ast.Common
import Core.Ast.Kind
import Core.Ast.Multiplicity
import Core.Ast.Pattern
import Core.Ast.Stage
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
import qualified TypeSystem.Type as TypeSystem

data Error p
  = UnknownIdentfier p Identifier
  | ExpectedMacro p TypeInternal
  | ExpectedForall p TypeInternal
  | ExpectedLinearForall p TypeInternal
  | ExpectedOfCourse p TypeInternal
  | ExpectedType p KindInternal
  | ExpectedHigher p KindInternal
  | IncompatibleType p TypeInternal TypeInternal
  | IncompatibleKind p KindInternal KindInternal
  | IncompatibleLinear p MultiplicityInternal MultiplicityInternal
  | IncompatibleStage p Stage Stage
  | CaptureLinear p Identifier
  | InvalidUsage p Identifier
  deriving (Show)

class FromError p a where
  fromError :: Error p -> a

instance FromError p (Error p) where
  fromError = id

instance (i ~ Internal) => FromError i Void where
  fromError q = error (show q)

data CoreState p = CoreState
  { typeEnvironment :: Map Identifier (p, MultiplicityInternal, TypeInternal),
    kindEnvironment :: Map Identifier (p, KindInternal),
    linearEnvironment :: Map Identifier (p, MultiplicitySort)
  }
  deriving (Show, Functor)

newtype Core p q a = Core {runCore' :: StateT (CoreState p) (Except q) a} deriving (Functor, Applicative, Monad)

runCore c env = runExcept (runStateT (runCore' c) env)

quit e = Core (lift $ except (Left (fromError e)))

matchLinear' _ Linear Linear = pure ()
matchLinear' _ Unrestricted Unrestricted = pure ()
matchLinear' p l l' = quit $ IncompatibleLinear p (CoreMultiplicity Internal l) (CoreMultiplicity Internal l')

matchLinear p (CoreMultiplicity Internal l) (CoreMultiplicity Internal l') = matchLinear' p l l'

matchStage _ Runtime Runtime = pure ()
matchStage p (StageMacro s1 s1') (StageMacro s2 s2') = zipWithM (matchStage p) [s1, s1'] [s2, s2'] >> pure ()
matchStage p (StageOfCourse s) (StageOfCourse s') = matchStage p s s' >> pure ()
matchStage p s s' = quit $ IncompatibleStage p s s'

matchKind' p (Type s) (Type s') = do
  matchStage p s s'
matchKind' p (Higher κ1 κ2) (Higher κ1' κ2') = do
  matchKind p κ1 κ1'
  matchKind p κ2 κ2'
matchKind' p κ κ' = quit $ IncompatibleKind p (CoreKind Internal κ) (CoreKind Internal κ')

matchKind p (CoreKind Internal κ) (CoreKind Internal κ') = matchKind' p κ κ'

matchType' :: FromError p q => p -> TypeF Internal -> TypeF Internal -> Core p q ()
matchType' _ (TypeVariable x) (TypeVariable x') | x == x' = pure ()
matchType' p (Macro σ τ) (Macro σ' τ') = zipWithM (matchType p) [σ, τ] [σ', τ'] >> pure ()
matchType' p (Forall (CoreTypePattern Internal (TypePatternVariable x κ)) σ) (Forall (CoreTypePattern Internal (TypePatternVariable x' κ')) σ') = do
  matchKind p κ κ'
  matchType p σ (substitute (CoreType Internal $ TypeVariable x) x' σ')
  pure ()
matchType' p (OfCourse σ) (OfCourse σ') = do
  matchType p σ σ'
matchType' p (TypeConstruction σ τ) (TypeConstruction σ' τ') = do
  matchType p σ σ'
  matchType p τ τ'
matchType' p σ σ' = quit $ IncompatibleType p (CoreType Internal σ) (CoreType Internal σ')

matchType :: FromError p q => p -> TypeInternal -> TypeInternal -> Core p q ()
matchType p (CoreType Internal σ) (CoreType Internal σ') = matchType' p σ σ'

instance (FromError p q, p ~ p', i ~ Internal) => TypeCheckLinear (Type i) (Core p q) (Term p') Use where
  typeCheckLinear (CoreTerm p e) = typeCheckLinearImpl p $ projectTerm e

instance (FromError p q, p ~ p', i ~ Internal, σ ~ Type p) => TypeCheck PatternSort (Core p q) (Pattern σ p') where
  typeCheck (CorePattern p pm) = typeCheckImpl p $ projectPattern pm

instance (FromError p' q, p ~ p', i ~ Internal) => TypeCheck (Kind i) (Core p q) (Type p') where
  typeCheck (CoreType p σ) = typeCheckImpl p $ projectType σ

instance (FromError p q, p ~ p', i ~ Internal, κ ~ Kind p) => TypeCheck TypePatternSort (Core p q) (TypePattern κ p') where
  typeCheck (CoreTypePattern p pm) = typeCheckImpl p $ projectTypePattern pm

instance (p ~ p', FromError p q) => TypeCheck MultiplicitySort (Core p q) (Multiplicity p') where
  typeCheck (CoreMultiplicity p l) = typeCheckImpl p $ projectMultiplicity l

instance (p ~ p', FromError p q) => TypeCheck KindSort (Core p q) (Kind p') where
  typeCheck _ = pure $ Kind

instance (p ~ p', FromError p q, i ~ Internal, i' ~ Internal) => TypeCheckInstantiate (Kind i) (Type i') (Core p q) (Type p') where
  typeCheckInstantiate σ = do
    κ <- typeCheck σ
    pure (κ, reduce $ Internal <$ σ)

instance (p ~ p', i ~ Internal, FromError p q) => TypeCheckInstantiate MultiplicitySort (Multiplicity i) (Core p q) (Multiplicity p') where
  typeCheckInstantiate l = do
    Multiplicity <- typeCheck l
    pure (Multiplicity, Internal <$ l)

instance (p ~ p', i ~ Internal, FromError p q) => TypeCheckInstantiate KindSort (Kind i) (Core p q) (Kind p') where
  typeCheckInstantiate κ = do
    pure (Kind, Internal <$ κ)

instance
  ( p ~ p',
    p ~ p'',
    FromError p q,
    σ ~ TypeInternal,
    τ ~ Type p
  ) =>
  TypeCheckInstantiate PatternSort (Pattern σ p) (Core p' q) (Pattern τ p'')
  where
  typeCheckInstantiate pm = do
    Pattern <- typeCheck pm
    pure (Pattern, first (reduce . (Internal <$)) pm)

instance
  ( p ~ p',
    p ~ p'',
    FromError p q,
    κ ~ KindInternal,
    κ' ~ Kind p
  ) =>
  TypeCheckInstantiate TypePatternSort (TypePattern κ p) (Core p' q) (TypePattern κ' p'')
  where
  typeCheckInstantiate pm = do
    TypePattern <- typeCheck pm
    pure (TypePattern, first (reduce . (Internal <$)) pm)

instance
  ( p ~ p',
    p ~ p'',
    FromError p q,
    σ ~ TypeInternal,
    τ ~ Type p
  ) =>
  Instantiate (Pattern σ p) (Core p' q) (Pattern τ p'')
  where
  instantiate = fmap snd . typeCheckInstantiate @PatternSort

instance
  ( p ~ p',
    p ~ p'',
    FromError p q,
    κ ~ KindInternal,
    κ' ~ Kind p
  ) =>
  Instantiate (TypePattern κ p) (Core p' q) (TypePattern κ' p'')
  where
  instantiate = fmap snd . typeCheckInstantiate @TypePatternSort

instance
  ( p ~ p',
    FromError p q,
    i ~ Internal
  ) =>
  Instantiate (Kind i) (Core p q) (Kind p')
  where
  instantiate = fmap snd . typeCheckInstantiate @KindSort

instance (FromError p q, p ~ p', i ~ Internal) => SameType (Core p q) p' (Type i) where
  sameType p σ σ' = matchType p σ σ'

instance (FromError p' q, i ~ Internal) => SameType (Core p q) p' (Kind i) where
  sameType p κ κ' = matchKind p κ κ'

instance (FromError p' q, i ~ Internal) => TypeSystem.CheckFunction (Core p q) p' (Type i) where
  checkFunction _ (CoreType Internal (Macro σ τ)) = pure (TypeSystem.Function σ τ)
  checkFunction p σ = quit $ ExpectedMacro p σ

instance (FromError p' q, i ~ Internal, i' ~ Internal) => TypeSystem.CheckForall' (Core p q) p' (Kind i) (Type i') where
  checkForall' _ (CoreType Internal (Forall pm σ)) = pure (internalType pm, \τ -> reducePattern pm τ σ)
  checkForall' p σ = quit $ ExpectedForall p σ

instance (FromError p' q, i ~ Internal) => TypeSystem.CheckOfCourse (Core p q) p' (Type i) where
  checkOfCourse _ (CoreType Internal (OfCourse σ)) = pure (TypeSystem.OfCourse σ)
  checkOfCourse p σ = quit $ ExpectedOfCourse p σ

instance (FromError p' q, i ~ Internal) => TypeSystem.CheckType Stage (Kind i) (Core p q) p' where
  checkType _ (CoreKind Internal (Type s)) = pure (TypeSystem.Type s)
  checkType p κ = quit $ ExpectedType p κ

instance TypeSystem.CheckType () KindSort (Core p q) p' where
  checkType _ Kind = pure (TypeSystem.Type ())

instance (FromError p' q, i ~ Internal) => TypeSystem.CheckFunction (Core p q) p' (Kind i) where
  checkFunction _ (CoreKind Internal (Higher κ κ')) = pure (TypeSystem.Function κ κ')
  checkFunction p κ = quit $ ExpectedHigher p κ

instance (FromError p' q, i ~ Internal) => ReadEnvironmentLinear (Core p q) p' (Type i) Use where
  readEnvironmentLinear p x = do
    env <- Core get
    case typeEnvironment env !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, _, σ) -> pure (σ, Use x)

instance (FromError p' q, p ~ p', i ~ Internal, i' ~ Internal) => AugmentEnvironmentLinear (Core p q) p' (Multiplicity i') (Type i) Use where
  augmentEnvironmentLinear p x l σ e = do
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

instance
  ( FromError p q,
    p ~ p',
    p ~ p'',
    i ~ Internal,
    σ ~ TypeInternal
  ) =>
  AugmentEnvironmentPatternLinear (Core p q) (Pattern σ p') (Multiplicity i) Use
  where
  augmentEnvironmentPatternLinear (CorePattern p pm) l e = augmentEnvironmentPatternLinearImpl p (projectPattern pm) l e

instance (FromError p' q, i ~ Internal) => ReadEnvironment (Core p q) p' (Kind i) where
  readEnvironment p x = do
    env <- Core get
    case kindEnvironment env !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, σ) -> pure σ

instance (p ~ p', FromError p q) => ReadEnvironment (Core p q) p' MultiplicitySort where
  readEnvironment p x = do
    env <- Core get
    case linearEnvironment env !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, l) -> pure l

instance (p ~ p', i ~ Internal) => AugmentEnvironment (Core p q) p' (Kind i) where
  augmentEnvironment p x κ e = do
    env <- Core get
    let κΓ = kindEnvironment env
    Core $ put env {kindEnvironment = Map.insert x (p, κ) κΓ}
    c <- e
    Core $ put env
    pure c

instance
  ( p ~ p',
    p ~ p'',
    κ ~ KindInternal
  ) =>
  AugmentEnvironmentPattern (Core p q) (TypePattern κ p')
  where
  augmentEnvironmentPattern (CoreTypePattern p (TypePatternVariable x κ)) e = augmentEnvironment p x κ e

instance (p ~ p', i ~ Internal) => AugmentEnvironment (Core p q) p' MultiplicitySort where
  augmentEnvironment p x ls e = do
    env <- Core get
    let lsΓ = linearEnvironment env
    Core $ put env {linearEnvironment = Map.insert x (p, ls) lsΓ}
    c <- e
    Core $ put env
    pure c

instance (FromError p' q, i ~ Internal) => Capture (Core p q) p' (Multiplicity i) Use where
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
