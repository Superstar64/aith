module Core.Ast where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (Except, except, runExcept)
import Control.Monad.Trans.State (StateT, get, put, runStateT)
import Data.Bifunctor (Bifunctor, bimap, first)
import Data.Map (Map, (!), (!?))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Type.Equality ((:~:) (..))
import Data.Void (Void, absurd)
import Environment
import Misc.Identifier
import Misc.Util (Same, same, zipWithM)
import qualified TypeSystem.Bind as TypeSystem
import qualified TypeSystem.Forall as TypeSystem
import qualified TypeSystem.Linear as TypeSystem
import qualified TypeSystem.Macro as TypeSystem
import qualified TypeSystem.MacroAbstraction as TypeSystem
import qualified TypeSystem.MacroApplication as TypeSystem
import TypeSystem.Methods
import qualified TypeSystem.Multiplicity as TypeSystem
import qualified TypeSystem.OfCourse as TypeSystem
import qualified TypeSystem.OfCourseIntroduction as TypeSystem
import qualified TypeSystem.PatternOfCourse as TypeSystem
import qualified TypeSystem.PatternVariable as TypeSystem
import qualified TypeSystem.StageMacro as TypeSystem
import qualified TypeSystem.StageOfCourse as TypeSystem
import qualified TypeSystem.Type as TypeSystem
import qualified TypeSystem.TypeAbstraction as TypeSystem
import qualified TypeSystem.TypeApplication as TypeSystem
import qualified TypeSystem.Unrestricted as TypeSystem
import qualified TypeSystem.Variable as TypeSystem

data Internal = Internal deriving (Show)

data TermF p
  = Variable Identifier
  | MacroAbstraction (Pattern (Type p) p) (Term p)
  | MacroApplication (Term p) (Term p)
  | TypeAbstraction Identifier (Kind p) (Term p)
  | TypeApplication (Term p) (Type p)
  | OfCourseIntroduction (Term p)
  | Bind (Pattern (Type p) p) (Term p) (Term p)
  deriving (Show)

instance Functor TermF where
  fmap _ (Variable x) = Variable x
  fmap f (MacroAbstraction pm e) = MacroAbstraction (bimap (fmap f) f pm) (fmap f e)
  fmap f (MacroApplication e1 e2) = MacroApplication (fmap f e1) (fmap f e2)
  fmap f (TypeAbstraction x κ e) = TypeAbstraction x (fmap f κ) (fmap f e)
  fmap f (TypeApplication e σ) = TypeApplication (fmap f e) (fmap f σ)
  fmap f (OfCourseIntroduction e) = OfCourseIntroduction (fmap f e)
  fmap f (Bind pm e1 e2) = Bind (bimap (fmap f) f pm) (fmap f e1) (fmap f e2)

data Term p = CoreTerm p (TermF p) deriving (Show, Functor)

projectTerm ::
  TermF p ->
  Either
    (TypeSystem.Variable (Term p))
    ( Either
        (TypeSystem.MacroAbstraction MultiplicityInternal (Pattern TypeInternal p) (Pattern (Type p) p) (Term p))
        ( Either
            (TypeSystem.MacroApplication (Term p))
            ( Either
                (TypeSystem.TypeAbstraction KindSort KindInternal TypeInternal (Kind p) (Term p))
                ( Either
                    (TypeSystem.TypeApplication KindInternal (Type p) (Term p))
                    ( Either
                        (TypeSystem.OfCourseIntroduction MultiplicityInternal (Term p))
                        (TypeSystem.Bind MultiplicityInternal (Pattern TypeInternal p) (Pattern (Type p) p) (Term p))
                    )
                )
            )
        )
    )
projectTerm (Variable x) = Left $ TypeSystem.Variable x
projectTerm (MacroAbstraction pm e) = Right $ Left $ TypeSystem.MacroAbstraction pm e
projectTerm (MacroApplication e1 e2) = Right $ Right $ Left $ TypeSystem.MacroApplication e1 e2
projectTerm (TypeAbstraction x κ e) = Right $ Right $ Right $ Left $ TypeSystem.TypeAbstraction x κ e
projectTerm (TypeApplication e σ) = Right $ Right $ Right $ Right $ Left $ TypeSystem.TypeApplication e σ
projectTerm (OfCourseIntroduction e) = Right $ Right $ Right $ Right $ Right $ Left $ TypeSystem.OfCourseIntroduction e
projectTerm (Bind pm e1 e2) = Right $ Right $ Right $ Right $ Right $ Right $ TypeSystem.Bind pm e1 e2

instance i ~ Internal => TypeSystem.EmbedVariable (Term i) where
  variable x = CoreTerm Internal $ Variable x

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal) => TypeSystem.EmbedMacroAbstraction (Pattern (Type i') i'') (Term i') where
  macroAbstraction pm e = CoreTerm Internal $ MacroAbstraction pm e

instance (i ~ Internal) => TypeSystem.EmbedMacroApplication (Term i) where
  macroApplication e1 e2 = CoreTerm Internal $ MacroApplication e1 e2

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedTypeAbstraction (Kind i) (Term i') where
  typeAbstraction x κ e = CoreTerm Internal $ TypeAbstraction x κ e

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedTypeApplication (Type i) (Term i') where
  typeApplication e σ = CoreTerm Internal $ TypeApplication e σ

instance (i ~ Internal) => TypeSystem.EmbedOfCourseIntroduction (Term i) where
  ofCourseIntroduction e = CoreTerm Internal $ OfCourseIntroduction e

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => TypeSystem.EmbedBind (Pattern σ i) (Term i') where
  bind pm e1 e2 = CoreTerm Internal $ Bind pm e1 e2

data PatternF σ p
  = PatternVariable Identifier σ
  | PatternOfCourse (Pattern σ p)
  deriving (Show)

instance Bifunctor PatternF where
  bimap f _ (PatternVariable x σ) = PatternVariable x (f σ)
  bimap f g (PatternOfCourse pm) = PatternOfCourse (bimap f g pm)

data Pattern σ p = CorePattern p (PatternF σ p) deriving (Show)

instance Bifunctor Pattern where
  bimap f g (CorePattern p pm) = CorePattern (g p) (bimap f g pm)

type PatternInternal = Pattern Internal

projectPattern ::
  PatternF σ p ->
  Either
    (TypeSystem.PatternVariable KindInternal σ)
    (TypeSystem.PatternOfCourse (Pattern σ p))
projectPattern (PatternVariable x σ) = Left $ TypeSystem.PatternVariable x σ
projectPattern (PatternOfCourse pm) = Right $ TypeSystem.PatternOfCourse pm

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => TypeSystem.EmbedPatternVariable (Type i) (Pattern σ i') where
  patternVariable x σ = CorePattern Internal $ PatternVariable x σ

instance (i ~ Internal, σ ~ TypeInternal) => TypeSystem.EmbedPatternOfCourse (Pattern σ i) where
  patternOfCourse pm = CorePattern Internal $ PatternOfCourse pm

data TypeF p
  = TypeVariable Identifier
  | Macro (Type p) (Type p)
  | Forall Identifier (Kind p) (Type p)
  | OfCourse (Type p)
  deriving (Show, Functor)

data Type p = CoreType p (TypeF p) deriving (Show, Functor)

type TypeInternal = Type Internal

projectType ::
  TypeF p ->
  Either
    (TypeSystem.Variable (Type p))
    ( Either
        (TypeSystem.Macro Stage (Type p))
        ( Either
            (TypeSystem.Forall KindSort Stage (Kind p) (Type p))
            (TypeSystem.OfCourse Stage (Type p))
        )
    )
projectType (TypeVariable x) = Left $ TypeSystem.Variable x
projectType (Macro σ τ) = Right $ Left $ TypeSystem.Macro σ τ
projectType (Forall x κ σ) = Right $ Right $ Left $ TypeSystem.Forall x κ σ
projectType (OfCourse σ) = Right $ Right $ Right $ TypeSystem.OfCourse σ

instance i ~ Internal => TypeSystem.EmbedVariable (Type i) where
  variable x = CoreType Internal $ TypeVariable x

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedMacro (Type i) where
  macro σ τ = CoreType Internal $ Macro σ τ

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedForall (Kind i) (Type i') where
  forallx x κ σ = CoreType Internal $ Forall x κ σ

instance (i ~ Internal) => TypeSystem.EmbedOfCourse (Type i) where
  ofCourse σ = CoreType Internal $ OfCourse σ

data MultiplicityF = Linear | Unrestricted deriving (Show)

data Multiplicity p = CoreMultiplicity p MultiplicityF deriving (Show, Functor, Foldable, Traversable)

type MultiplicityInternal = Multiplicity Internal

projectMultiplicity :: MultiplicityF -> (Either TypeSystem.Linear TypeSystem.Unrestricted)
projectMultiplicity Linear = Left $ TypeSystem.Linear
projectMultiplicity Unrestricted = Right $ TypeSystem.Unrestricted

instance (i ~ Internal) => TypeSystem.EmbedLinear (Multiplicity i) where
  linear = CoreMultiplicity Internal Linear

instance (i ~ Internal) => TypeSystem.EmbedUnrestricted (Multiplicity i) where
  unrestricted = CoreMultiplicity Internal Unrestricted

data MultiplicitySort = Multiplicity deriving (Show)

instance TypeSystem.EmbedMultiplicity MultiplicitySort where
  multiplicity = Multiplicity

data Stage = Runtime | StageMacro Stage Stage | StageOfCourse Stage deriving (Show)

instance TypeSystem.EmbedStageMacro Stage where
  stageMacro s s' = StageMacro s s'

instance TypeSystem.EmbedStageOfCourse Stage where
  stageOfCourse s = StageOfCourse s

data KindF p = Type Stage deriving (Show, Functor)

data Kind p = CoreKind p (KindF p) deriving (Show, Functor)

type KindInternal = Kind Internal

data KindSort = Kind deriving (Show)

instance (i ~ Internal, i' ~ Internal) => TypeSystem.EmbedType Stage (Kind i) where
  typex' s = CoreKind Internal $ Type s

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

-- free variables of patterns

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => FreeVariables (Pattern σ i) (Term i') where
  freeVariables' _ = Set.empty

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => FreeVariables (Pattern σ i) (Type i') where
  freeVariables' (CorePattern Internal pm) = freeVariables @TypeInternal $ projectPattern pm

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => FreeVariables (Pattern σ i) (Multiplicity i') where
  freeVariables' (CorePattern Internal pm) = freeVariables @MultiplicityInternal $ projectPattern pm

-- remove binding of patterns

instance (i ~ Internal, σ ~ TypeInternal) => RemoveBindings (Pattern σ i) where
  removeBindings (CorePattern Internal pm) = removeBindings $ projectPattern pm

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
  freeVariables' (CoreMultiplicity Internal l) = freeVariables @MultiplicityInternal $ projectMultiplicity l

-- free variables of kinds

instance (i ~ Internal, i' ~ Internal) => FreeVariables (Kind i) (Multiplicity i') where
  freeVariables' _ = Set.empty

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

instance (i ~ Internal) => SubstituteSame (Term i) where
  substituteSame = substitute

-- substitute into pattern

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => Substitute (Term i) (Pattern σ i') where
  substitute ex x (CorePattern Internal pm) = substituteImpl ex x $ projectPattern pm

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => Substitute (Type i) (Pattern σ i') where
  substitute σx x (CorePattern Internal pm) = substituteImpl σx x $ projectPattern pm

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => Substitute (Multiplicity i) (Pattern σ i') where
  substitute lx x (CorePattern Internal pm) = substituteImpl lx x $ projectPattern pm

-- avoid pattern capture

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal, σ ~ TypeInternal) => AvoidCapturePattern (Term i'') (Pattern σ i) (Term i') where
  avoidCapturePattern u (CorePattern Internal pm, e) = avoidCapturePatternImpl u (projectPattern pm, e)

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal, σ ~ TypeInternal) => AvoidCapturePattern (Type i'') (Pattern σ i) (Term i') where
  avoidCapturePattern u (CorePattern Internal pm, e) = avoidCapturePatternImpl u (projectPattern pm, e)

instance (i ~ Internal, i' ~ Internal, i'' ~ Internal, σ ~ TypeInternal) => AvoidCapturePattern (Multiplicity i'') (Pattern σ i) (Term i') where
  avoidCapturePattern u (CorePattern Internal pm, e) = avoidCapturePatternImpl u (projectPattern pm, e)

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
  substitute _ _ κ = κ

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

-- reduction

instance (i ~ Internal) => Reduce (Term i) where
  reduce (CoreTerm Internal e) = reduceImpl $ projectTerm e

instance (i ~ Internal, i' ~ Internal, σ ~ TypeInternal) => ReducePattern (Pattern σ i) (Term i') where
  reducePattern (CorePattern Internal pm) e1 e2 = reducePattern (projectPattern pm) e1 e2

instance (i ~ Internal, i' ~ Internal) => ReduceMatchAbstraction (Term i') (Term i) where
  reduceMatchAbstraction (CoreTerm Internal (MacroAbstraction pm e1)) = Just $ \e2 -> reducePattern pm e2 e1
  reduceMatchAbstraction _ = Nothing

instance (i ~ Internal, i' ~ Internal) => ReduceMatchAbstraction (Type i') (Term i) where
  reduceMatchAbstraction (CoreTerm Internal (TypeAbstraction x _ e)) = Just $ \σ -> reduce $ substitute σ x e
  reduceMatchAbstraction _ = Nothing

instance (i ~ Internal) => TypeSystem.MatchOfCourseIntroduction (Term i) where
  matchOfCourseIntroduction (CoreTerm Internal (OfCourseIntroduction e)) = Just (TypeSystem.OfCourseIntroduction e)
  matchOfCourseIntroduction _ = Nothing

data Error p
  = UnknownIdentfier p Identifier
  | ExpectedMacro p TypeInternal
  | ExpectedForall p TypeInternal
  | ExpectedLinearForall p TypeInternal
  | ExpectedOfCourse p TypeInternal
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
  { typeEnvironment :: Map Identifier (p, MultiplicityInternal, TypeInternal),
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
matchLinear' p l l' = quit $ IncompatibleLinear p (CoreMultiplicity Internal l) (CoreMultiplicity Internal l')

matchLinear p (CoreMultiplicity Internal l) (CoreMultiplicity Internal l') = matchLinear' p l l'

matchStage _ Runtime Runtime = pure ()
matchStage p (StageMacro s1 s1') (StageMacro s2 s2') = zipWithM (matchStage p) [s1, s1'] [s2, s2'] >> pure ()
matchStage p (StageOfCourse s) (StageOfCourse s') = matchStage p s s' >> pure ()
matchStage p s s' = quit $ IncompatibleStage p s s'

matchKind' p (Type s) (Type s') = do
  matchStage p s s'

matchKind p (CoreKind Internal κ) (CoreKind Internal κ') = matchKind' p κ κ'

matchType' :: FromError p q => p -> TypeF Internal -> TypeF Internal -> Core p q ()
matchType' _ (TypeVariable x) (TypeVariable x') | x == x' = pure ()
matchType' p (Macro σ τ) (Macro σ' τ') = zipWithM (matchType p) [σ, τ] [σ', τ'] >> pure ()
matchType' p (Forall x κ σ) (Forall x' κ' σ') = do
  matchKind p κ κ'
  matchType p σ (substitute (CoreType Internal $ TypeVariable x) x' σ')
  pure ()
matchType' p (OfCourse σ) (OfCourse σ') = do
  matchType p σ σ'
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

instance (FromError p q, p ~ p', i ~ Internal, σ ~ Type p) => TypeCheck (Type i) (Core p q) (Pattern σ p') where
  typeCheck (CorePattern p pm) = typeCheckImpl p $ projectPattern pm

instance (FromError p' q, p ~ p', i ~ Internal) => TypeCheck (Kind i) (Core p q) (Type p') where
  typeCheck (CoreType p σ) = typeCheckImpl p $ projectType σ

instance (p ~ p', FromError p q) => TypeCheck MultiplicitySort (Core p q) (Multiplicity p') where
  typeCheck (CoreMultiplicity p l) = typeCheckImpl p $ projectMultiplicity l

instance (p ~ p', FromError p q) => TypeCheck KindSort (Core p q) (Kind p') where
  typeCheck (CoreKind _ (Type _)) = do
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
    pure (Kind, Internal <$ κ)

instance
  ( FromError p q,
    p ~ p',
    p ~ p'',
    i ~ Internal,
    σ ~ TypeInternal,
    σ' ~ Type p
  ) =>
  TypeCheckInstantiate (Type i) (Pattern σ p) (Core p' q) (Pattern σ' p'')
  where
  typeCheckInstantiate pm = do
    σ <- typeCheck pm
    pure (σ, first (Internal <$) pm)

instance (FromError p q, p ~ p', i ~ Internal) => SameType (Core p q) p' (Type i) where
  sameType p σ σ' = matchType p σ σ'

instance (FromError p' q, i ~ Internal) => SameType (Core p q) p' (Kind i) where
  sameType p κ κ' = matchKind p κ κ'

instance (FromError p' q, i ~ Internal) => TypeSystem.CheckMacro (Core p q) p' (Type i) where
  checkMacro _ (CoreType Internal (Macro σ τ)) = pure (TypeSystem.Macro σ τ)
  checkMacro p σ = quit $ ExpectedMacro p σ

instance (FromError p' q, i ~ Internal, i' ~ Internal) => TypeSystem.CheckForall (Core p q) p' (Kind i) (Type i') where
  checkForall _ (CoreType Internal (Forall x κ σ)) = pure (TypeSystem.Forall x κ σ)
  checkForall p σ = quit $ ExpectedForall p σ

instance (FromError p' q, i ~ Internal) => TypeSystem.CheckOfCourse (Core p q) p' (Type i) where
  checkOfCourse _ (CoreType Internal (OfCourse σ)) = pure (TypeSystem.OfCourse σ)
  checkOfCourse p σ = quit $ ExpectedOfCourse p σ

instance (FromError p' q, i ~ Internal) => TypeSystem.CheckType (Core p q) p' (Kind i) Stage where
  checkType' _ (CoreKind Internal (Type s)) = pure (TypeSystem.Type s)

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
    i' ~ Internal,
    σ ~ TypeInternal
  ) =>
  AugmentEnvironmentPattern (Core p q) (Pattern σ p') p'' (Multiplicity i') (Type i) Use
  where
  augmentEnvironmentPattern (CorePattern p pm) l p' e = augmentEnvironmentPatternImpl p (projectPattern pm) l p' e

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
