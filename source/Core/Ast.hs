module Core.Ast where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (Except, except, runExcept)
import Control.Monad.Trans.State (StateT, get, put, runStateT)
import Data.Map (Map, (!), (!?))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Type.Equality ((:~:) (..))
import Data.Void (Void, absurd)
import Environment
import Misc.Identifier
import Misc.Util (Same, same, zipWithM)
import qualified TypeSystem.Forall as TypeSystem
import qualified TypeSystem.Linear as TypeSystem
import qualified TypeSystem.LinearAbstraction as TypeSystem
import qualified TypeSystem.LinearApplication as TypeSystem
import qualified TypeSystem.LinearForall as TypeSystem
import qualified TypeSystem.Multiplicity as TypeSystem
import qualified TypeSystem.Macro as TypeSystem
import qualified TypeSystem.MacroAbstraction as TypeSystem
import qualified TypeSystem.MacroApplication as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.StageMacro as TypeSystem
import qualified TypeSystem.Type as TypeSystem
import qualified TypeSystem.TypeAbstraction as TypeSystem
import qualified TypeSystem.TypeApplication as TypeSystem
import qualified TypeSystem.Unrestricted as TypeSystem
import qualified TypeSystem.Variable as TypeSystem

data Internal = Internal deriving (Show)

data TermF p
  = Variable Identifier
  | MacroAbstraction Identifier (Multiplicity p) (Type p) (Term p)
  | MacroApplication (Term p) (Term p)
  | TypeAbstraction Identifier (Kind p) (Term p)
  | TypeApplication (Term p) (Type p)
  | LinearAbstraction Identifier (Term p)
  | LinearApplication (Term p) (Multiplicity p)
  deriving (Show, Functor)

data Term p = CoreTerm p (TermF p) deriving (Show, Functor)

projectTerm ::
  TermF p ->
  Either
    (TypeSystem.Variable (Term p))
    ( Either
        (TypeSystem.MacroAbstraction MultiplicitySort MultiplicityInternal KindInternal (Multiplicity p) (Type p) (Term p))
        ( Either
            (TypeSystem.MacroApplication (Term p))
            ( Either
                (TypeSystem.TypeAbstraction KindSort KindInternal TypeInternal (Kind p) (Term p))
                ( Either
                    (TypeSystem.TypeApplication KindInternal (Type p) (Term p))
                    (Either (TypeSystem.LinearAbstraction MultiplicitySort MultiplicityInternal (Term p)) (TypeSystem.LinearApplication MultiplicitySort MultiplicityInternal (Multiplicity p) (Term p)))
                )
            )
        )
    )
projectTerm (Variable x) = Left $ TypeSystem.Variable x
projectTerm (MacroAbstraction x l σ e) = Right $ Left $ TypeSystem.MacroAbstraction x l σ e
projectTerm (MacroApplication e1 e2) = Right $ Right $ Left $ TypeSystem.MacroApplication e1 e2
projectTerm (TypeAbstraction x κ e) = Right $ Right $ Right $ Left $ TypeSystem.TypeAbstraction x κ e
projectTerm (TypeApplication e σ) = Right $ Right $ Right $ Right $ Left $ TypeSystem.TypeApplication e σ
projectTerm (LinearAbstraction x e) = Right $ Right $ Right $ Right $ Right $ Left $ TypeSystem.LinearAbstraction x e
projectTerm (LinearApplication e l) = Right $ Right $ Right $ Right $ Right $ Right $ TypeSystem.LinearApplication e l

instance i ~ Internal => TypeSystem.EmbedVariable (Term i) where
  variable' (TypeSystem.Variable x) = CoreTerm Internal $ Variable x

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal) => TypeSystem.EmbedMacroAbstraction (Multiplicity i'') (Type i) (Term i') where
  macroAbstraction' (TypeSystem.MacroAbstraction x l σ e) = CoreTerm Internal $ MacroAbstraction x l σ e

instance (i ~ Internal) => TypeSystem.EmbedMacroApplication (Term i) where
  macroApplication' (TypeSystem.MacroApplication e1 e2) = CoreTerm Internal $ MacroApplication e1 e2

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedTypeAbstraction (Kind i) (Term i') where
  typeAbstraction' (TypeSystem.TypeAbstraction x κ e) = CoreTerm Internal $ TypeAbstraction x κ e

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedTypeApplication (Type i) (Term i') where
  typeApplication' (TypeSystem.TypeApplication e σ) = CoreTerm Internal $ TypeApplication e σ

instance (i ~ Internal) => TypeSystem.EmbedLinearAbstraction (Term i) where
  linearAbstraction' (TypeSystem.LinearAbstraction x e) = CoreTerm Internal $ LinearAbstraction x e

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedLinearApplication (Multiplicity i) (Term i') where
  linearApplication' (TypeSystem.LinearApplication e l) = CoreTerm Internal $ LinearApplication e l

data TypeF p
  = TypeVariable Identifier
  | Macro (Multiplicity p) (Type p) (Type p)
  | Forall Identifier (Kind p) (Type p)
  | LinearForall Identifier (Type p)
  deriving (Show, Functor)

data Type p = CoreType p (TypeF p) deriving (Show, Functor)

type TypeInternal = Type Internal

projectType ::
  TypeF p ->
  Either
    (TypeSystem.Variable (Type p))
    ( Either
        (TypeSystem.Macro MultiplicitySort MultiplicityInternal Stage (Multiplicity p) (Type p))
        ( Either
            (TypeSystem.Forall KindSort MultiplicityInternal Stage (Kind p) (Type p))
            (TypeSystem.LinearForall MultiplicitySort MultiplicityInternal Stage (Type p))
        )
    )
projectType (TypeVariable x) = Left $ TypeSystem.Variable x
projectType (Macro l σ τ) = Right $ Left $ TypeSystem.Macro l σ τ
projectType (Forall x κ σ) = Right $ Right $ Left $ TypeSystem.Forall x κ σ
projectType (LinearForall x σ) = Right $ Right $ Right $ TypeSystem.LinearForall x σ

instance i ~ Internal => TypeSystem.EmbedVariable (Type i) where
  variable' (TypeSystem.Variable x) = CoreType Internal $ TypeVariable x

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedMacro (Multiplicity i') (Type i) where
  macro' (TypeSystem.Macro l σ τ) = CoreType Internal $ Macro l σ τ

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedForall (Kind i) (Type i') where
  forallx' (TypeSystem.Forall x κ σ) = CoreType Internal $ Forall x κ σ

instance (i ~ Internal) => TypeSystem.EmbedLinearForall (Type i) where
  linearForall' (TypeSystem.LinearForall x σ) = CoreType Internal $ LinearForall x σ

data MultiplicityF = Linear | Unrestricted | LinearVariable Identifier deriving (Show)

data Multiplicity p = CoreMultiplicity p MultiplicityF deriving (Show, Functor, Foldable, Traversable)

type MultiplicityInternal = Multiplicity Internal

projectMultiplicity ::
  MultiplicityF ->
  Either
    (TypeSystem.Variable p)
    (Either TypeSystem.Linear TypeSystem.Unrestricted)
projectMultiplicity (LinearVariable x) = Left $ TypeSystem.Variable x
projectMultiplicity Linear = Right $ Left $ TypeSystem.Linear
projectMultiplicity Unrestricted = Right $ Right $ TypeSystem.Unrestricted

instance (i ~ Internal) => TypeSystem.EmbedVariable (Multiplicity i) where
  variable' (TypeSystem.Variable x) = CoreMultiplicity Internal $ LinearVariable x

instance (i ~ Internal) => TypeSystem.EmbedLinear (Multiplicity i) where
  linear = CoreMultiplicity Internal Linear

instance (i ~ Internal) => TypeSystem.EmbedUnrestricted (Multiplicity i) where
  unrestricted = CoreMultiplicity Internal Unrestricted

data MultiplicitySort = Multiplicity deriving (Show)

instance TypeSystem.EmbedMultiplicity MultiplicitySort where
  multiplicity = Multiplicity

data Stage = Runtime | StageMacro Stage Stage deriving (Show)

instance TypeSystem.EmbedStageMacro Stage where
  stageMacro' (TypeSystem.StageMacro s s') = StageMacro s s'

data KindF p = Type (Multiplicity p) Stage deriving (Show, Functor)

data Kind p = CoreKind p (KindF p) deriving (Show, Functor)

type KindInternal = Kind Internal

data KindSort = Kind deriving (Show)

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedType (Multiplicity i') Stage (Kind i) where
  typex' (TypeSystem.Type l s) = CoreKind Internal $ Type l s

instance (i ~ Internal, i' ~ Internal) => Same (Type i) (Term i) where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => Same (Term i) (Term i) where
  same = Just Refl

instance (i ~ Internal, i' ~ Internal) => Same (Term i) (Type i) where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => Same (Type i) (Type i) where
  same = Just Refl

instance (i ~ Internal, i' ~ Internal) => Same (Multiplicity i) (Type i') where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => Same (Multiplicity i) (Term i') where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => Same (Multiplicity i) (Multiplicity i') where
  same = Just Refl

instance (i ~ Internal, i' ~ Internal) => Same (Type i) (Multiplicity i') where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => Same (Term i) (Multiplicity i') where
  same = Nothing

-- free variables of terms
instance (i ~ Internal, i' ~ Internal) => FreeVariables (Term i) (Term i') where
  freeVariables' (CoreTerm Internal e) = freeVariables @(Term Internal) $ projectTerm e

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Term i) (Type i') where
  freeVariables' (CoreTerm Internal e) = freeVariables @TypeInternal $ projectTerm e

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Term i) (Multiplicity i') where
  freeVariables' (CoreTerm Internal e) = freeVariables @MultiplicityInternal $ projectTerm e

-- free variables of types

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Type i) (Term i') where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Type i) (Type i') where
  freeVariables' (CoreType Internal σ) = freeVariables @TypeInternal $ projectType σ

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Type i) (Multiplicity i') where
  freeVariables' (CoreType Internal σ) = freeVariables @MultiplicityInternal $ projectType σ

-- free variables of multiplicity

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Multiplicity i') (Type i) where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Multiplicity i) (Term i) where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Multiplicity i) (Multiplicity i') where
  freeVariables' (CoreMultiplicity Internal l) = freeVariables @MultiplicityInternal $ projectMultiplicity @MultiplicityInternal l

-- free variables of kinds

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Kind i) (Multiplicity i') where
  freeVariables' (CoreKind Internal (Type l _)) = freeVariables @MultiplicityInternal l

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Kind i) (Term i') where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Kind i) (Type i) where
  freeVariables' _ = Set.empty

-- substitute into term

instance (i ~ Internal, i' ~ Internal) => Substitute (Term i) (Term i') where
  substitute ex x (CoreTerm Internal e) = substituteImpl ex x $ projectTerm e

instance (i ~ Internal, i' ~ Internal) => Substitute (Type i) (Term i') where
  substitute σx x (CoreTerm Internal e) = substituteImpl σx x $ projectTerm e

instance (i ~ Internal, i' ~ Internal) => Substitute (Multiplicity i) (Term i') where
  substitute lx x (CoreTerm Internal e) = substituteImpl lx x $ projectTerm e

-- substitute into type

instance (i ~ Internal, i' ~ Internal) => Substitute (Term i) (Type i) where
  substitute _ _ σ = σ

instance (i ~ Internal, i' ~ Internal) => Substitute (Type i) (Type i') where
  substitute σx x (CoreType Internal σ) = substituteImpl σx x $ projectType σ

instance (i ~ Internal) => SubstituteSame (Type i) where
  substituteSame = substitute

instance (i ~ Internal, i' ~ Internal) => Substitute (Multiplicity i) (Type i') where
  substitute l x (CoreType Internal σ) = substituteImpl l x $ projectType σ

-- substitute into kind

instance Substitute (Type i) (Kind i) where
  substitute _ _ κ = κ

instance (i ~ Internal, i' ~ Internal) => Substitute (Multiplicity i) (Kind i) where
  substitute lx x (CoreKind Internal (Type l s)) = CoreKind Internal $ Type (substitute lx x l) s

instance Substitute (Term i) (Kind i) where
  substitute _ _ κ = κ

-- substitute into multiplicity

instance (i ~ Internal, i' ~ Internal) => Substitute (Multiplicity i) (Multiplicity i') where
  substitute lx x (CoreMultiplicity Internal l) = substituteImpl lx x $ projectMultiplicity l

instance (i ~ Internal) => SubstituteSame (Multiplicity i) where
  substituteSame = substitute

instance (i ~ Internal, i' ~ Internal) => Substitute (Type i) (Multiplicity i') where
  substitute _ _ l = l

instance (i ~ Internal, i' ~ Internal) => Substitute (Term i) (Multiplicity i') where
  substitute _ _ l = l

instance (i ~ Internal) => Reduce (Term i) where
  reduce (CoreTerm Internal e) = reduceImpl $ projectTerm e

instance MatchAbstraction (Term i) where
  matchAbstraction (CoreTerm _ (MacroAbstraction x _ _ e)) = Just (x, e)
  matchAbstraction (CoreTerm _ (LinearAbstraction x e)) = Just (x, e)
  matchAbstraction (CoreTerm _ (TypeAbstraction x _ e)) = Just (x, e)
  matchAbstraction _ = Nothing

data Error p
  = UnknownIdentfier p Identifier
  | ExpectedMacro p TypeInternal
  | ExpectedForall p TypeInternal
  | ExpectedLinearForall p TypeInternal
  | ExpectedType p KindInternal
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
  { typeEnvironment :: Map Identifier (p, TypeInternal),
    kindEnvironment :: Map Identifier (p, KindInternal),
    linearEnvironment :: Map Identifier (p, MultiplicitySort)
  }
  deriving (Show, Functor)

data Core p q a = Core {runCore' :: StateT (CoreState p) (Except q) a} deriving (Functor)

instance Applicative (Core p q) where
  pure x = Core (pure x)
  Core f <*> Core x = Core (f <*> x)

instance Monad (Core p q) where
  return x = pure x
  Core m >>= f = Core (m >>= (runCore' . f))

runCore c env = runExcept (runStateT (runCore' c) env)

typeCheckInternal :: CoreState Internal -> TypeInternal -> KindInternal
typeCheckInternal env σ = case runCore (typeCheck σ) env of
  Left q -> absurd q
  Right (κ, _) -> κ

quit e = Core (lift $ except (Left (fromError e)))

matchLinear' _ Linear Linear = pure ()
matchLinear' _ Unrestricted Unrestricted = pure ()
matchLinear' _ (LinearVariable x) (LinearVariable x') | x == x' = pure ()
matchLinear' p l l' = quit $ IncompatibleLinear p (CoreMultiplicity Internal l) (CoreMultiplicity Internal l')

matchLinear p (CoreMultiplicity Internal l) (CoreMultiplicity Internal l') = matchLinear' p l l'

matchStage _ Runtime Runtime = pure ()
matchStage p (StageMacro s1 s1') (StageMacro s2 s2') = zipWithM (matchStage p) [s1, s1'] [s2, s2'] >> pure ()
matchStage p s s' = quit $ IncompatibleStage p s s'

matchKind' p (Type l s) (Type l' s') = do
  matchLinear p l l'
  matchStage p s s'

--matchKind' p κ κ' = quit $ IncompatibleKind p (CoreKind Internal κ) (CoreKind Internal κ')

matchKind p (CoreKind Internal κ) (CoreKind Internal κ') = matchKind' p κ κ'

matchType' :: FromError p q => p -> TypeF Internal -> TypeF Internal -> Core p q ()
matchType' _ (TypeVariable x) (TypeVariable x') | x == x' = pure ()
matchType' p (Macro _ σ τ) (Macro _ σ' τ') = zipWithM (matchType p) [σ, τ] [σ', τ'] >> pure ()
matchType' p (Forall x κ σ) (Forall x' κ' σ') = do
  matchKind p κ κ'
  matchType p σ (substitute (CoreType Internal $ TypeVariable x) x' σ')
  pure ()
matchType' p (LinearForall x σ) (LinearForall x' σ') = do
  matchType p σ (substitute (CoreType Internal $ TypeVariable x) x' σ')
matchType' p σ σ' = quit $ IncompatibleType p (CoreType Internal σ) (CoreType Internal σ')

matchType :: FromError p q => p -> TypeInternal -> TypeInternal -> Core p q ()
matchType p (CoreType Internal σ) (CoreType Internal σ') = matchType' p σ σ'

instance Positioned (Term p) p where
  location (CoreTerm p _) = p

instance Positioned (Type p) p where
  location (CoreType p _) = p

instance Positioned (Kind p) p where
  location (CoreKind p _) = p

instance (FromError p q, p ~ p', i ~ Internal) => TypeCheckLinear (Type i) (Core p q) (Term p') Use where
  typeCheckLinear (CoreTerm p e) = typeCheckLinearImpl p $ projectTerm e

instance (FromError p' q, p ~ p', i ~ Internal) => TypeCheck (Kind i) (Core p q) (Type p') where
  typeCheck (CoreType p σ) = typeCheckImpl p $ projectType σ

instance (p ~ p', FromError p q) => TypeCheck MultiplicitySort (Core p q) (Multiplicity p') where
  typeCheck (CoreMultiplicity p l) = typeCheckImpl p $ projectMultiplicity l

instance (p ~ p', FromError p q) => TypeCheck KindSort (Core p q) (Kind p') where
  typeCheck (CoreKind _ (Type l _)) = do
    Multiplicity <- typeCheck l
    pure $ Kind

instance (p ~ p', FromError p q, i ~ Internal, i' ~ Internal) => TypeCheckInstantiate (Kind i) (Type i') (Core p q) (Type p') where
  typeCheckInstantiate σ = do
    κ <- typeCheck σ
    pure (κ, Internal <$ σ)

instance (p ~ p', i ~ Internal, FromError p q) => TypeCheckInstantiate MultiplicitySort (Multiplicity i) (Core p q) (Multiplicity p') where
  typeCheckInstantiate l = do
    Multiplicity <- typeCheck l
    pure (Multiplicity, Internal <$ l)

instance (p ~ p', i ~ Internal, FromError p q) => TypeCheckInstantiate KindSort (Kind i) (Core p q) (Kind p') where
  typeCheckInstantiate κ = do
    Kind <- typeCheck κ
    pure (Kind, Internal <$ κ)

instance (FromError p q, p ~ p', i ~ Internal) => SameType (Core p q) p' (Type i) where
  sameType p σ σ' = matchType p σ σ'

instance (FromError p' q, i ~ Internal) => SameType (Core p q) p' (Kind i) where
  sameType p κ κ' = matchKind p κ κ'

instance (FromError p' q, i ~ Internal) => TypeSystem.CheckMacro' (Core p q) p' (Type i) where
  checkMacro' _ (CoreType Internal (Macro _ σ τ)) = pure (σ, τ)
  checkMacro' p σ = quit $ ExpectedMacro p σ

instance (FromError p' q, i ~ Internal, i' ~ Internal) => TypeSystem.CheckForall (Core p q) p' (Kind i) (Type i') where
  checkForall _ (CoreType Internal (Forall x κ σ)) = pure (TypeSystem.Forall x κ σ)
  checkForall p σ = quit $ ExpectedForall p σ

instance (FromError p' q, i ~ Internal) => TypeSystem.CheckLinearForall (Core p q) p' (Type i) where
  checkLinearForall _ (CoreType Internal (LinearForall x σ)) = pure (TypeSystem.LinearForall x σ)
  checkLinearForall p σ = quit $ ExpectedLinearForall p σ

instance (FromError p' q, i ~ Internal, i' ~ Internal) => TypeSystem.CheckType (Core p q) p' (Kind i) (Multiplicity i') Stage where
  checkType' _ (CoreKind Internal (Type l s)) = pure (TypeSystem.Type l s)

instance (FromError p' q, i ~ Internal) => ReadEnvironmentLinear (Core p q) p' (Type i) Use where
  readEnvironmentLinear p x = do
    env <- Core get
    case typeEnvironment env !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, σ) -> pure (σ, Use x)

instance (FromError p' q, p ~ p', i ~ Internal) => AugmentEnvironmentLinear (Core p q) p' (Type i) Use where
  augmentEnvironmentLinear p x σ e = do
    env <- Core get
    let σΓ = typeEnvironment env
    Core $ put env {typeEnvironment = Map.insert x (p, σ) σΓ}
    (σ', lΓ) <- e
    Core $ put env
    case count x lΓ of
      Single -> pure ()
      _ -> do
        let (CoreKind Internal (Type l _)) = typeCheckInternal (Internal <$ env) σ
        case l of
          CoreMultiplicity Internal Unrestricted -> pure ()
          _ -> quit $ InvalidUsage p x
    pure (σ', Remove x lΓ)

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
  capture p _ lΓ = do
    let captures = variables lΓ
    env <- Core get
    let lΓ = typeEnvironment env
    for (Set.toList captures) $ \x' -> do
      let (_, σ) = lΓ ! x'
      let (CoreKind Internal (Type l _)) = typeCheckInternal (Internal <$ env) σ
      case l of
        CoreMultiplicity Internal Unrestricted -> pure ()
        _ -> quit $ CaptureLinear p x'
    pure ()
