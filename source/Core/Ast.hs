module Core.Ast where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (Except, except, runExcept)
import Control.Monad.Trans.State (StateT, get, put, runStateT)
import Data.Map (Map, (!), (!?))
import qualified Data.Map as Map
import Data.Proxy (Proxy (..))
import Data.Set (Set)
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
import qualified TypeSystem.Macro as TypeSystem
import qualified TypeSystem.MacroAbstraction as TypeSystem
import qualified TypeSystem.MacroApplication as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.StageMacro as TypeSystem
import qualified TypeSystem.Type as TypeSystem
import qualified TypeSystem.TypeAbstraction as TypeSystem
import qualified TypeSystem.TypeApplication as TypeSystem
import qualified TypeSystem.Variable as TypeSystem

data Internal = Internal deriving (Show)

data TermF p
  = Variable Identifier
  | MacroAbstraction Identifier Linearity (Type p) (Term p)
  | MacroApplication (Term p) (Term p)
  | TypeAbstraction Identifier (Kind p) (Term p)
  | TypeApplication (Term p) (Type p)
  | LinearAbstraction Identifier (Term p)
  | LinearApplication (Term p) Linearity
  deriving (Show, Functor)

data Term p = CoreTerm p (TermF p) deriving (Show, Functor)

projectTerm ::
  TermF p ->
  Either
    (TypeSystem.Variable (Term p))
    ( Either
        (TypeSystem.MacroAbstraction Linearity Linearity (Type p) (Term p))
        ( Either
            (TypeSystem.MacroApplication (Term p))
            ( Either
                (TypeSystem.TypeAbstraction TypeInternal KindInternal (Kind p) (Term p))
                ( Either
                    (TypeSystem.TypeApplication KindInternal (Core.Ast.Type p) (Term p))
                    (Either (TypeSystem.LinearAbstraction Linearity (Term p)) (TypeSystem.LinearApplication Linearity (Term p)))
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

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedMacroAbstraction Linearity (Type i) (Term i') where
  macroAbstraction' (TypeSystem.MacroAbstraction x l σ e) = CoreTerm Internal $ MacroAbstraction x l σ e

instance (i ~ Internal) => TypeSystem.EmbedMacroApplication (Term i) where
  macroApplication' (TypeSystem.MacroApplication e1 e2) = CoreTerm Internal $ MacroApplication e1 e2

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedTypeAbstraction (Kind i) (Term i') where
  typeAbstraction' (TypeSystem.TypeAbstraction x κ e) = CoreTerm Internal $ TypeAbstraction x κ e

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedTypeApplication (Type i) (Term i') where
  typeApplication' (TypeSystem.TypeApplication e σ) = CoreTerm Internal $ TypeApplication e σ

instance (i ~ Internal) => TypeSystem.EmbedLinearAbstraction (Term i) where
  linearAbstraction' (TypeSystem.LinearAbstraction x e) = CoreTerm Internal $ LinearAbstraction x e

instance (i ~ Internal) => TypeSystem.EmbedLinearApplication Linearity (Term i) where
  linearApplication' (TypeSystem.LinearApplication e l) = CoreTerm Internal $ LinearApplication e l

data TypeF p
  = TypeVariable Identifier
  | Macro Linearity (Type p) (Type p)
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
        (TypeSystem.Macro Linearity Stage Linearity (Type p))
        ( Either
            (TypeSystem.Forall Linearity Stage (Kind p) (Type p))
            (TypeSystem.LinearForall Linearity Stage (Type p))
        )
    )
projectType (TypeVariable x) = Left $ TypeSystem.Variable x
projectType (Macro l σ τ) = Right $ Left $ TypeSystem.Macro l σ τ
projectType (Forall x κ σ) = Right $ Right $ Left $ TypeSystem.Forall x κ σ
projectType (LinearForall x σ) = Right $ Right $ Right $ TypeSystem.LinearForall x σ

instance i ~ Internal => TypeSystem.EmbedVariable (Type i) where
  variable' (TypeSystem.Variable x) = CoreType Internal $ TypeVariable x

instance i ~ Internal => TypeSystem.EmbedMacro Linearity (Type i) where
  macro' (TypeSystem.Macro l σ τ) = CoreType Internal $ Macro l σ τ

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedForall (Kind i) (Type i') where
  forallx' (TypeSystem.Forall x κ σ) = CoreType Internal $ Forall x κ σ

instance (i ~ Internal) => TypeSystem.EmbedLinearForall (Type i) where
  linearForall' (TypeSystem.LinearForall x σ) = CoreType Internal $ LinearForall x σ

data Linearity = Linear | Unrestricted | LinearVariable Identifier deriving (Show)

instance TypeSystem.EmbedVariable Linearity where
  variable' (TypeSystem.Variable x) = LinearVariable x

instance TypeSystem.EmbedLinear Linearity where
  linear = Linear

data Stage = Runtime | StageMacro Stage Stage deriving (Show)

instance TypeSystem.EmbedStageMacro Stage where
  stageMacro' (TypeSystem.StageMacro s s') = StageMacro s s'

data KindF p = Type Linearity Stage deriving (Show, Functor)

data Kind p = CoreKind p (KindF p) deriving (Show, Functor)

type KindInternal = Kind Internal

instance (i ~ Internal) => TypeSystem.EmbedType Linearity Stage (Kind i) where
  typex' (TypeSystem.Type l s) = CoreKind Internal $ Type l s

instance (i ~ Internal, i' ~ Internal) => Same (Type i) (Term i) where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => Same (Term i) (Term i) where
  same = Just Refl

instance (i ~ Internal, i' ~ Internal) => Same (Term i) (Type i) where
  same = Nothing

instance (i ~ Internal, i' ~ Internal) => Same (Type i) (Type i) where
  same = Just Refl

instance (i ~ Internal) => Same Linearity (Type i) where
  same = Nothing

instance (i ~ Internal) => Same Linearity (Term i) where
  same = Nothing

instance Same Linearity Linearity where
  same = Just Refl

instance Same (Type i) Linearity where
  same = Nothing

instance Same (Term i) Linearity where
  same = Nothing

-- free variables of terms
instance (i ~ Internal, i' ~ Internal) => FreeVariables (Term i) (Term i') where
  freeVariables u (CoreTerm Internal e) = freeVariables u $ projectTerm e

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Term i) (Type i') where
  freeVariables u (CoreTerm Internal e) = freeVariables u $ projectTerm e

instance (i ~ Internal) => FreeVariables (Term i) Linearity where
  freeVariables u (CoreTerm Internal e) = freeVariables u $ projectTerm e

-- free variables of types

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Type i) (Term i') where
  freeVariables Proxy _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Type i) (Type i') where
  freeVariables u (CoreType Internal σ) = freeVariables u $ projectType σ

instance (i ~ Internal) => FreeVariables (Type i) Linearity where
  freeVariables u (CoreType Internal σ) = freeVariables u $ projectType σ

-- free variables of linearity

instance (i ~ Internal) => FreeVariables Linearity (Type i) where
  freeVariables Proxy _ = Set.empty

instance FreeVariables Linearity (Term i) where
  freeVariables Proxy _ = Set.empty

instance FreeVariables Linearity Linearity where
  freeVariables Proxy Linear = Set.empty
  freeVariables Proxy Unrestricted = Set.empty
  freeVariables Proxy (LinearVariable x) = Set.singleton x

-- free variables of kinds

instance (i ~ Internal) => FreeVariables (Kind i) Linearity where
  freeVariables u (CoreKind Internal (Type l _)) = freeVariables u l

instance FreeVariables (Kind i) (Term i) where
  freeVariables Proxy _ = Set.empty

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Kind i) (Type i) where
  freeVariables Proxy _ = Set.empty

-- substitute into term

instance (i ~ Internal, i' ~ Internal) => Substitute (Term i) (Term i') where
  substitute ex x (CoreTerm Internal e) = substituteImpl ex x $ projectTerm e

instance (i ~ Internal, i' ~ Internal) => Substitute (Type i) (Term i') where
  substitute σx x (CoreTerm Internal e) = substituteImpl σx x $ projectTerm e

instance (i ~ Internal) => Substitute Linearity (Term i) where
  substitute lx x (CoreTerm Internal e) = substituteImpl lx x $ projectTerm e

-- substitute into type

instance (i ~ Internal, i' ~ Internal) => Substitute (Term i) (Type i) where
  substitute _ _ σ = σ

instance (i ~ Internal, i' ~ Internal) => Substitute (Type i) (Type i') where
  substitute σx x (CoreType Internal σ) = substituteImpl σx x $ projectType σ

instance (i ~ Internal) => SubstituteSame (Type i) where
  substituteSame = substitute

instance (i ~ Internal) => Substitute Linearity (Type i) where
  substitute l x (CoreType Internal σ) = substituteImpl l x $ projectType σ

-- substitute into kind

instance Substitute (Type i) (Kind i) where
  substitute _ _ κ = κ

instance (i ~ Internal) => Substitute Linearity (Kind i) where
  substitute lx x (CoreKind Internal (Type l s)) = CoreKind Internal $ Type (substitute lx x l) s

instance Substitute (Term i) (Kind i) where
  substitute _ _ κ = κ

-- substitute into linearity

instance Substitute Linearity Linearity where
  substitute _ _ Linear = Linear
  substitute _ _ Unrestricted = Unrestricted
  substitute lx x (LinearVariable x') | x == x' = lx
  substitute _ _ (LinearVariable x) = LinearVariable x

instance SubstituteSame Linearity where
  substituteSame = substitute

instance Substitute (Type i) Linearity where
  substitute _ _ l = l

instance (i ~ Internal) => Substitute (Term i) Linearity where
  substitute _ _ l = l

instance (i ~ Internal) => Reduce (Term i) where
  reduce (CoreTerm Internal e) = reduceImpl $ projectTerm e

instance TypeSystem.CheckMacroAbstraction' (Term i) where
  checkMacroAbstraction' (CoreTerm _ (MacroAbstraction x _ _ e)) = Just (x, e)
  checkMacroAbstraction' _ = Nothing

instance TypeSystem.CheckLinearAbstraction' (Term i) where
  checkLinearAbstraction' (CoreTerm _ (LinearAbstraction x e)) = Just (x, e)
  checkLinearAbstraction' _ = Nothing

instance TypeSystem.CheckTypeAbstraction' (Term i) where
  checkTypeAbstraction' (CoreTerm _ (TypeAbstraction x _ e)) = Just (x, e)
  checkTypeAbstraction' _ = Nothing

data Error p
  = UnknownIdentfier p Identifier
  | ExpectedMacro p TypeInternal
  | ExpectedForall p TypeInternal
  | ExpectedLinearForall p TypeInternal
  | ExpectedType p KindInternal
  | IncompatibleType p TypeInternal TypeInternal
  | IncompatibleKind p KindInternal KindInternal
  | IncompatibleLinear p Linearity Linearity
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

data CoreState p = CoreState {typeEnvironment :: Map Identifier (p, TypeInternal), kindEnvironment :: Map Identifier (p, KindInternal), linearEnvironment :: Set Identifier} deriving (Show, Functor)

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

matchLinear _ Linear Linear = pure ()
matchLinear _ Unrestricted Unrestricted = pure ()
matchLinear _ (LinearVariable x) (LinearVariable x') | x == x' = pure ()
matchLinear p l l' = quit $ IncompatibleLinear p l l'

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

instance (FromError p q, p ~ p', i ~ Internal) => TypeCheckLinear (Core p q) (Term p') (Type i) Use where
  typeCheckLinear (CoreTerm p e) = typeCheckLinearImpl p $ projectTerm e

instance (FromError p' q, p ~ p', i ~ Internal) => TypeCheck (Core p q) (Type p') (Kind i) where
  typeCheck (CoreType p σ) = typeCheckImpl p $ projectType σ

instance Instantiate (Core p q) Linearity Linearity where
  instantiate = pure

instance (i ~ Internal) => Instantiate (Core p q) (Type p') (Type i) where
  instantiate σ = pure $ Internal <$ σ

instance (i ~ Internal) => InstantiateType (Core p q) (Type p') (Type i) where
  instantiateType = instantiate

instance (i ~ Internal) => Instantiate (Core p q) (Kind p') (Kind i) where
  instantiate κ = pure $ Internal <$ κ

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

instance (FromError p' q, i ~ Internal) => TypeSystem.CheckType (Core p q) p' (Kind i) Linearity Stage where
  checkType _ (CoreKind Internal (Type l s)) = pure (TypeSystem.Type l s)

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
          Unrestricted -> pure ()
          _ -> quit $ InvalidUsage p x
    pure (σ', Remove x lΓ)

instance (FromError p' q, i ~ Internal) => ReadEnvironment (Core p q) p' (Kind i) where
  readEnvironment p x = do
    env <- Core get
    case kindEnvironment env !? x of
      Nothing -> quit $ UnknownIdentfier p x
      Just (_, σ) -> pure σ

instance (p ~ p', i ~ Internal) => AugmentEnvironment (Core p q) p' (Kind i) where
  augmentEnvironment p x κ e = do
    env <- Core get
    let κΓ = kindEnvironment env
    Core $ put env {kindEnvironment = Map.insert x (p, κ) κΓ}
    c <- e
    Core $ put env
    pure c

instance (p ~ p') => AugmentEnvironmentWithLinear (Core p q) p' where
  augmentEnvironmentWithLinear _ x e = do
    env <- Core get
    let lΓ = linearEnvironment env
    Core $ put env {linearEnvironment = Set.insert x lΓ}
    c <- e
    Core $ put env
    pure c

instance (FromError p' q) => Capture (Core p q) p' Linearity Use where
  capture _ Linear _ = pure ()
  capture p _ lΓ = do
    let captures = variables lΓ
    env <- Core get
    let lΓ = typeEnvironment env
    for (Set.toList captures) $ \x' -> do
      let (_, σ) = lΓ ! x'
      let (CoreKind Internal (Type l _)) = typeCheckInternal (Internal <$ env) σ
      case l of
        Unrestricted -> pure ()
        _ -> quit $ CaptureLinear p x'
    pure ()
