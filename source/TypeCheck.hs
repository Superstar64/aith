module TypeCheck where

import Ast.Common.Variable
import Ast.Module.Algebra hiding (Inline)
import qualified Ast.Module.Algebra as Module
import qualified Ast.Module.Core as Core
import qualified Ast.Module.Surface as Surface
import Ast.Term.Algebra
import Ast.Term.Core
  ( TermMetaPatternUnify,
    TermSchemeInfer,
    TermSchemeUnify,
    TermUnify,
  )
import qualified Ast.Term.Core as Core
import Ast.Term.Runtime
import Ast.Term.Surface (NoType (..))
import qualified Ast.Term.Surface as Surface
import Ast.Type.Algebra
import Ast.Type.Core
  ( Instantiation (..),
    LabelSchemeUnify,
    TypeAlgebra (..),
    TypeInfer,
    TypePatternIntermediate (..),
    TypeSchemeInfer,
    TypeSchemeUnify,
    TypeUnify,
    convertBoolean,
    convertType,
    freeLocalVariablesType,
    linear,
    none,
    relabel,
    simplify,
    substituteType,
    toTypePattern,
    unconvertBoolean,
    unrestricted,
  )
import qualified Ast.Type.Core as Core
import Ast.Type.Runtime
import qualified Ast.Type.Surface as Surface
import Control.Monad (filterM, (<=<))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT, withReaderT)
import Control.Monad.Trans.State (StateT, get, modify, runStateT)
import Data.Bifunctor (second)
import Data.Functor.Identity (Identity (..), runIdentity)
import Data.List (unzip4)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (for)
import Data.Void (Void, absurd)
import Linearity
import qualified Misc.Boolean as Boolean
import Misc.Path (Path (..), SemiPath (..))
import qualified Misc.Path as Path
import Misc.Util (firstM, secondM, sortTopological, temporaries, uppers)

flexible = fmap absurd

m ! x = case Map.lookup x m of
  Nothing -> error "bad lookup in type check"
  Just e -> e

-- levels are inspired from "How OCaml type checker works -- or what polymorphism and garbage collection have in common"
-- however, rather then using levels for let generalization, levels here are used for skolemization
-- where each level can be thought of as a ∀α ∃ βγδ... qualifier in unification under a mixed prefix
newtype Level = Level {runLevel :: Int} deriving (Eq, Ord, Show, Enum)

instance Bounded Level where
  minBound = Level 0
  maxBound = Level maxBound

data TypeError p
  = UnknownGlobalIdentifier p TermGlobalIdentifier
  | UnknownTypeGlobalIdentifier p TypeGlobalIdentifier
  | TypeMismatch p TypeUnify TypeUnify
  | ErasureMismatch p Erasure Erasure
  | TypeBooleanMismatch p [TypeUnify]
  | TypePolyMismatch p TypeSchemeUnify TypeSchemeUnify
  | TypeOccursCheck p TypeLogical TypeUnify
  | AmbiguousType p TypeInfer
  | EscapingSkolemType p TypeIdentifier
  | ExpectedTypeAnnotation p
  | MismatchedTypeLambdas p
  | ExpectedBooleanType p TypeUnify
  | IncorrectRegionBounds p
  | NotTypable p
  | NotErasable p TypeUnify
  | ExpectedNewtype p TypeUnify
  | ExpectedKind p TypeUnify
  | ExpectedRepresentation p TypeUnify
  | ExpectedMultiplicity p TypeUnify
  | ExpectedSize p TypeUnify
  | ExpectedSignedness p TypeUnify
  | ExpectedType p TypeUnify
  | ExpectedPretype p TypeUnify
  | ExpectedBoxed p TypeUnify
  | ExpectedRegion p TypeUnify
  | ExpectedPropositional p TypeUnify
  | ExpectedUnification p TypeUnify
  | ExpectedInline p TypeUnify
  | ExpectedFunctionPointer p TypeUnify
  | ExpectedFunctionLiteralType p TypeUnify
  | ExpectedUnique p TypeUnify
  | ExpectedPointer p TypeUnify
  | ExpectedArray p TypeUnify
  | ExpectedEffect p TypeUnify
  | ExpectedShared p TypeUnify
  | ExpectedNumber p TypeUnify
  | ExpectedBoolean p TypeUnify
  | ExpectedStep p TypeUnify
  | ExpectedLabel p TypeUnify
  | BadBorrowIdentifier p TermIdentifier
  | BadBorrowSyntax p
  | InstantiationLengthMismatch p
  deriving (Show)

newtype Check p a = Check {runChecker'' :: ReaderT (CheckEnvironment p) (StateT (CheckState p) (Either (TypeError p))) a} deriving (Functor, Applicative, Monad)

runChecker' c = runStateT . runReaderT (runChecker'' c)

runChecker :: Check p a -> CheckEnvironment p -> CheckState p -> Either (TypeError p) a
runChecker c = (fmap fst .) . runChecker' c

data TermBinding p = TermBinding
  { termPosition :: p,
    termMultiplicity :: TypeUnify,
    termType :: LabelSchemeUnify
  }
  deriving (Functor)

data TypeBinding p = TypeBinding
  { typePosition :: p,
    typeErasure :: Erasure,
    typeKind :: TypeUnify,
    typeLevel :: Level
  }
  deriving (Functor)

data CheckEnvironment p = CheckEnvironment
  { typeEnvironment :: Map TermIdentifier (TermBinding p),
    kindEnvironment :: Map TypeIdentifier (TypeBinding p),
    typeGlobalEnvironment :: Map TermGlobalIdentifier (TermBinding p),
    kindGlobalEnvironment :: Map TypeGlobalIdentifier (TypeBinding p),
    moduleScope :: SemiPath,
    -- local synonyms are currently only used for avoiding shadowing
    typeSynonyms :: Map TypeIdentifier TypeInfer,
    typeGlobalSynonyms :: Map TypeGlobalIdentifier TypeInfer
  }
  deriving (Functor)

data TypeLogicalState p
  = UnboundType p Erasure TypeUnify Level
  | LinkType TypeUnify
  deriving (Functor, Show)

-- todo use int maps here
data CheckState p = CheckState
  { typeLogicalMap :: Map TypeLogical (TypeLogicalState p),
    freshTypeCounter :: Int,
    levelCounter :: Level,
    usedVars :: Set String,
    booleans :: [(TypeUnify, TypeUnify)]
  }
  deriving (Functor, Show)

quit :: TypeError p -> Check p a
quit e = Check $ lift $ lift $ Left e

emptyEnvironment :: CheckEnvironment p
emptyEnvironment = CheckEnvironment Map.empty Map.empty Map.empty Map.empty Path.root Map.empty Map.empty

askEnvironment :: Check p (CheckEnvironment p)
askEnvironment = Check ask

augmentTypeEnvironment :: TermIdentifier -> p -> TypeUnify -> LabelSchemeUnify -> Check p a -> Check p a
augmentTypeEnvironment x p l σ = modifyTypeEnvironment (Map.insert x (TermBinding p l σ))
  where
    modifyTypeEnvironment f = withEnvironment (\env -> env {typeEnvironment = f (typeEnvironment env)})
    withEnvironment f (Check r) = Check $ withReaderT f r

augmentKindEnvironment :: p -> TypeIdentifier -> Erasure -> TypeUnify -> Level -> Check p a -> Check p a
augmentKindEnvironment p x π κ lev f =
  modifyKindEnvironment (Map.insert x (TypeBinding p π κ lev)) f
  where
    modifyKindEnvironment f (Check r) = Check $ withReaderT (\env -> env {kindEnvironment = f (kindEnvironment env)}) r

augmentSynonym :: TypeIdentifier -> TypeInfer -> Check p a -> Check p a
augmentSynonym x σ (Check r) = Check $ withReaderT (\env -> env {typeSynonyms = Map.insert x σ (typeSynonyms env)}) r

emptyState :: CheckState p
emptyState = CheckState Map.empty 0 (Level 0) Set.empty []

getState :: Check p (CheckState p)
getState = Check $ lift $ get

modifyState :: (CheckState p -> CheckState p) -> Check p ()
modifyState f = Check $ lift $ modify f

augmentTypePatternLevel :: TypePatternIntermediate p -> Check p b -> Check p b
augmentTypePatternLevel (TypePatternIntermediate p x π κ) f = do
  useTypeVar x
  level <- levelCounter <$> getState
  f' <- augmentKindEnvironment p x π (flexible κ) (succ level) $ leveled $ f
  -- after leveled, `booleans` in state should be pre zonked
  modifyState $ \state -> state {booleans = constantElimination $ booleans state}
  pure f'
  where
    useTypeVar (TypeIdentifier x) = do
      modifyState $ \state -> state {usedVars = Set.insert x $ usedVars state}
    constantElimination [] = []
    constantElimination ((σ, τ) : problems)
      | Set.member x $ freeLocalVariablesType σ <> freeLocalVariablesType τ =
        let σ' = substituteType (Core.Type TypeTrue) x σ
            σ'' = substituteType (Core.Type TypeFalse) x σ
            τ' = substituteType (Core.Type TypeTrue) x τ
            τ'' = substituteType (Core.Type TypeFalse) x τ
         in (σ', τ') : (σ'', τ'') : constantElimination problems
      | otherwise =
        (σ, τ) : constantElimination problems

leveled :: Check p b -> Check p b
leveled f = do
  modifyLevelCounter (+ 1)
  f' <- f
  solveBooleans
  modifyLevelCounter (subtract 1)
  pure f'
  where
    modifyLevelCounter f = do
      modifyState $ \state -> state {levelCounter = Level $ f $ runLevel $ levelCounter state}

solveBooleans = do
  logical <- typeLogicalMap <$> getState
  lev <- levelCounter <$> getState
  equations <- booleans <$> getState
  variables <- pure $ Map.unions (map (\(σ, τ) -> unsolved logical σ `Map.union` unsolved logical τ) equations)
  variables <- pure $ Map.keys $ Map.filter (\(_, _, _, lev') -> lev == lev') variables
  equations <- pure $ map (\(σ, τ) -> convertBoolean (zonk logical σ) + convertBoolean (zonk logical τ)) equations
  let (answers, equations') = Boolean.solve variables equations
  modifyState $ \state -> state {booleans = map (\σ -> (unconvertBoolean σ, Core.Type TypeFalse)) equations'}
  answers <- Boolean.renameAnswers (fresh logical) answers
  answers <- pure $ Boolean.backSubstitute answers
  for answers $ \(x, σ) ->
    modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkType $ unconvertBoolean σ) $ typeLogicalMap state}
  where
    fresh logical x = case logical ! x of
      UnboundType p π κ l -> freshTypeVariableRaw p π κ l
      LinkType _ -> error "unexpected link"

freshTypeVariableRaw :: p -> Erasure -> TypeUnify -> Level -> Check p TypeLogical
freshTypeVariableRaw p π κ lev = do
  v <- TypeLogicalRaw <$> newFreshType
  insertTypeLogicalMap v
  pure $ v
  where
    newFreshType = do
      state <- getState
      let i = freshTypeCounter state
      modifyState $ \state -> state {freshTypeCounter = i + 1}
      pure i
    insertTypeLogicalMap x = do
      modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundType p π κ lev) $ typeLogicalMap state}

-- also changes logic type variable levels and check for escaping skolem variables
occursCheck :: forall p. p -> TypeLogical -> Level -> TypeUnify -> Check p ()
occursCheck p x lev σ' = go σ'
  where
    recurse = go
    go :: TypeUnify -> Check p ()
    go (Core.Type σ) = do
      case σ of
        TypeConstant (TypeVariable x') -> do
          TypeBinding _ _ _ lev' <- (! x') <$> kindEnvironment <$> askEnvironment
          if lev' > lev
            then quit $ EscapingSkolemType p x'
            else pure ()
        TypeConstant (TypeGlobalVariable x') -> do
          TypeBinding _ _ _ lev' <- (! x') <$> kindGlobalEnvironment <$> askEnvironment
          if lev' > lev
            then error "type globals aren't supposed to be argumentable"
            else pure ()
        TypeLogical x' | x == x' -> quit $ TypeOccursCheck p x σ'
        TypeLogical x' ->
          (! x') <$> typeLogicalMap <$> getState >>= \case
            (UnboundType p' π κ lev') ->
              if lev' > lev
                then do
                  modifyState $ \state -> state {typeLogicalMap = Map.insert x' (UnboundType p' π κ lev) $ typeLogicalMap state}
                else pure ()
            (LinkType σ) -> recurse σ
        Inline σ π τ -> do
          recurse σ
          recurse π
          recurse τ
        Poly σ ς -> do
          recurse σ
          occursPoly ς
        FunctionPointer σ π τ -> do
          recurse σ
          recurse π
          recurse τ
        FunctionLiteralType σ π τ -> do
          recurse σ
          recurse π
          recurse τ
        Tuple σs -> do
          traverse recurse σs
          pure ()
        Effect σ τ -> do
          recurse σ
          recurse τ
        Unique σ -> do
          recurse σ
        Shared σ π -> do
          recurse σ
          recurse π
        Pointer σ -> recurse σ
        Array σ -> recurse σ
        Number _ _ -> pure ()
        Boolean -> pure ()
        Step σ τ -> do
          recurse σ
          recurse τ
        TypeConstant World -> pure ()
        Type -> pure ()
        Region -> pure ()
        Pretype κ τ -> do
          recurse κ
          recurse τ
        Boxed -> pure ()
        Multiplicity -> pure ()
        (KindRuntime PointerRep) -> pure ()
        (KindRuntime (StructRep κs)) -> traverse recurse κs >> pure ()
        (KindRuntime (UnionRep κs)) -> traverse recurse κs >> pure ()
        (KindRuntime (WordRep κ)) -> recurse κ
        (KindSize _) -> pure ()
        (KindSignedness _) -> pure ()
        Representation -> pure ()
        Size -> pure ()
        Signedness -> pure ()
        Kind σ -> do
          recurse σ
        Syntactic -> pure ()
        Propositional -> pure ()
        Top -> pure ()
        Unification -> pure ()
        AmbiguousLabel -> pure ()
        Label -> pure ()
        Hole v -> absurd v
        TypeBoolean (TypeNot σ) -> recurse σ
        TypeBoolean (TypeAnd σ τ) -> do
          recurse σ
          recurse τ
        TypeBoolean (TypeXor σ τ) -> do
          recurse σ
          recurse τ
        TypeBoolean (TypeOr σ τ) -> do
          recurse σ
          recurse τ
        TypeTrue -> pure ()
        TypeFalse -> pure ()
    occursPoly ς = case ς of
      Core.MonoType σ -> recurse σ
      Core.TypeForall (Core.TypePattern x π κ) ς -> do
        recurse κ
        augmentKindEnvironment p x π κ minBound $ occursPoly ς
        pure ()

kindIsMember :: forall p. p -> TypeUnify -> TypeUnify -> Check p ()
kindIsMember p (Core.Type Top) _ = quit $ NotTypable p
kindIsMember p σ κ = do
  κ' <- reconstruct p σ
  matchType p κ κ'

reconstruct :: forall p. p -> TypeUnify -> Check p TypeUnify
reconstruct p = Core.reconstruct indexEnvironment indexGlobalEnvironment indexLogicalMap poly representation multiplicities propositional
  where
    poly (Core.TypeForall _ _) = pure $ Core.Type $ Type
    poly (Core.MonoType σ) = reconstruct p σ

    indexEnvironment x = (! x) <$> kindEnvironment <$> askEnvironment >>= kind
      where
        kind (TypeBinding _ _ κ _) = pure $ κ
    indexGlobalEnvironment x = (! x) <$> kindGlobalEnvironment <$> askEnvironment >>= kind
      where
        kind (TypeBinding _ _ κ _) = pure $ κ
    indexLogicalMap x = (! x) <$> typeLogicalMap <$> getState >>= index
    index (UnboundType _ _ x _) = pure x
    index (LinkType σ) = reconstruct p σ
    representation σ = do
      κ <- reconstruct p σ
      (α, _) <- checkPretype p κ
      pure α
    multiplicities σs = do
      πs <- for σs $ \σ -> do
        κ <- reconstruct p σ
        (_, π) <- checkPretype p κ
        pure π
      pure $ foldr (\τ ρ -> Core.Type $ TypeBoolean $ TypeAnd τ ρ) unrestricted πs
    propositional [] = do
      freshTypeVariable p (Core.Type $ Kind $ Core.Type $ Propositional)
    propositional (σ : σs) = do
      π <- reconstruct p σ
      for σs $ \σ -> do
        π' <- reconstruct p σ
        matchType p π π'
      pure π

erasureEntail _ Transparent _ = pure ()
erasureEntail p Concrete τ@(Core.Type σ) = case σ of
  TypeLogical x ->
    (! x) <$> typeLogicalMap <$> getState >>= \case
      LinkType σ -> erasureEntail p Concrete σ
      UnboundType p' _ κ lev ->
        modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundType p' Concrete κ lev) $ typeLogicalMap state}
  TypeConstant (TypeVariable x) -> do
    TypeBinding {typeErasure = π} <- (! x) <$> kindEnvironment <$> askEnvironment
    matchErasure p Concrete π
  TypeConstant (TypeGlobalVariable x) -> do
    TypeBinding {typeErasure = π} <- (! x) <$> kindGlobalEnvironment <$> askEnvironment
    matchErasure p Concrete π
  KindRuntime κ -> case κ of
    PointerRep -> pure ()
    StructRep πs -> do
      traverse (erasureEntail p Concrete) πs
      pure ()
    UnionRep πs -> do
      traverse (erasureEntail p Concrete) πs
      pure ()
    WordRep π -> erasureEntail p Concrete π
  KindSignedness _ -> pure ()
  KindSize _ -> pure ()
  _ -> quit $ NotErasable p τ

unifyVariable :: p -> TypeLogical -> Erasure -> TypeUnify -> Level -> TypeUnify -> Check p ()
unifyVariable p x π κ lev σ = do
  occursCheck p x lev σ
  kindIsMember p σ κ
  erasureEntail p π σ
  modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkType σ) $ typeLogicalMap state}
  pure ()

-- If two types unify, that imply that they're kinds are exactly the same
-- The type ast has enough information to uniquely determine a type's kind

-- Big rule: Unifing a logic type variable does not avoid captures
-- Rigid type variable scopes cannot shadow other rigid type variables
matchType :: forall p. p -> TypeUnify -> TypeUnify -> Check p ()
matchType p = unify
  where
    unify :: TypeUnify -> TypeUnify -> Check p ()
    unify (Core.Type (TypeLogical x)) (Core.Type (TypeLogical x')) | x == x' = pure ()
    unify σ@(Core.Type (TypeBoolean _)) τ = unifyBoolean σ τ
    unify σ τ@(Core.Type (TypeBoolean _)) = unifyBoolean σ τ
    -- when unifying two variables, the right might not be a solved variable
    unify τ@(Core.Type (TypeLogical x)) σ@(Core.Type (TypeLogical x')) =
      (! x) <$> typeLogicalMap <$> getState >>= \case
        LinkType σ' -> unify σ' σ
        UnboundType _ π κ lev ->
          (! x') <$> typeLogicalMap <$> getState >>= \case
            LinkType σ' -> unify τ σ'
            UnboundType _ _ _ _ -> unifyVariable p x π κ lev σ
    unify (Core.Type (TypeLogical x)) σ =
      (! x) <$> typeLogicalMap <$> getState >>= \case
        LinkType σ' -> unify σ' σ
        UnboundType _ π κ lev -> unifyVariable p x π κ lev σ
    unify σ (Core.Type (TypeLogical x)) =
      (! x) <$> typeLogicalMap <$> getState >>= \case
        LinkType σ' -> unify σ σ'
        UnboundType _ π κ lev -> unifyVariable p x π κ lev σ
    unify (Core.Type (TypeConstant σ)) (Core.Type (TypeConstant σ')) | σ == σ' = pure ()
    unify (Core.Type TypeTrue) (Core.Type TypeTrue) = pure ()
    unify (Core.Type TypeFalse) (Core.Type TypeFalse) = pure ()
    unify (Core.Type (Inline σ π τ)) (Core.Type (Inline σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (Core.Type (Poly σ ς)) (Core.Type (Poly σ' ς')) = do
      unify σ σ'
      unifyPoly ς ς'
    unify (Core.Type (FunctionPointer σ π τ)) (Core.Type (FunctionPointer σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (Core.Type (FunctionLiteralType σ π τ)) (Core.Type (FunctionLiteralType σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (Core.Type (Tuple σs)) (Core.Type (Tuple σs')) | length σs == length σs' = do
      sequence $ zipWith (unify) σs σs'
      pure ()
    unify (Core.Type (Effect σ π)) (Core.Type (Effect σ' π')) = do
      unify σ σ'
      unify π π'
    unify (Core.Type (Unique σ)) (Core.Type (Unique σ')) = do
      unify σ σ'
    unify (Core.Type (Shared σ π)) (Core.Type (Shared σ' π')) = do
      unify σ σ'
      unify π π'
    unify (Core.Type (Pointer σ)) (Core.Type (Pointer σ')) = do
      unify σ σ'
    unify (Core.Type (Array σ)) (Core.Type (Array σ')) = do
      unify σ σ'
    unify (Core.Type (Number ρ1 ρ2)) (Core.Type (Number ρ1' ρ2')) = do
      unify ρ1 ρ1'
      unify ρ2 ρ2'
    unify (Core.Type Boolean) (Core.Type Boolean) = pure ()
    unify (Core.Type (Step σ τ)) (Core.Type (Step σ' τ')) = do
      unify σ σ'
      unify τ τ'
    unify (Core.Type Type) (Core.Type Type) = pure ()
    unify (Core.Type Region) (Core.Type Region) = pure ()
    unify (Core.Type (Pretype κ τ)) (Core.Type (Pretype κ' τ')) = do
      unify κ κ'
      unify τ τ'
    unify (Core.Type Boxed) (Core.Type Boxed) = pure ()
    unify (Core.Type Multiplicity) (Core.Type Multiplicity) = pure ()
    unify (Core.Type (KindRuntime PointerRep)) (Core.Type (KindRuntime PointerRep)) = pure ()
    unify (Core.Type (KindRuntime (StructRep κs))) (Core.Type (KindRuntime (StructRep κs'))) | length κs == length κs' = do
      sequence_ $ zipWith (unify) κs κs'
    unify (Core.Type (KindRuntime (UnionRep κs))) (Core.Type (KindRuntime (UnionRep κs'))) | length κs == length κs' = do
      sequence_ $ zipWith (unify) κs κs'
    unify (Core.Type (KindRuntime (WordRep κ))) (Core.Type (KindRuntime (WordRep κ'))) = unify κ κ'
    unify (Core.Type (KindSize Byte)) (Core.Type (KindSize Byte)) = pure ()
    unify (Core.Type (KindSize Short)) (Core.Type (KindSize Short)) = pure ()
    unify (Core.Type (KindSize Int)) (Core.Type (KindSize Int)) = pure ()
    unify (Core.Type (KindSize Long)) (Core.Type (KindSize Long)) = pure ()
    unify (Core.Type (KindSize Native)) (Core.Type (KindSize Native)) = pure ()
    unify (Core.Type (KindSignedness Signed)) (Core.Type (KindSignedness Signed)) = pure ()
    unify (Core.Type (KindSignedness Unsigned)) (Core.Type (KindSignedness Unsigned)) = pure ()
    unify (Core.Type Representation) (Core.Type Representation) = pure ()
    unify (Core.Type Size) (Core.Type Size) = pure ()
    unify (Core.Type Signedness) (Core.Type Signedness) = pure ()
    unify (Core.Type (Kind σ)) (Core.Type (Kind σ')) = do
      unify σ σ'
    unify (Core.Type Syntactic) (Core.Type Syntactic) = pure ()
    unify (Core.Type Propositional) (Core.Type Propositional) = pure ()
    unify (Core.Type Unification) (Core.Type Unification) = pure ()
    unify (Core.Type AmbiguousLabel) (Core.Type AmbiguousLabel) = pure ()
    unify (Core.Type Label) (Core.Type Label) = pure ()
    unify (Core.Type Top) (Core.Type Top) = pure ()
    unify σ σ' = quit $ TypeMismatch p σ σ'

    unifyBoolean σ τ = do
      κ <- reconstruct p σ
      κ' <- reconstruct p τ
      matchType p κ κ'
      modifyState $ \state -> state {booleans = (σ, τ) : booleans state}
    unifyPoly
      (Core.TypeForall (Core.TypePattern α π κ) ς)
      (Core.TypeForall (Core.TypePattern α' π' κ') ς') = do
        matchErasure p π π'
        matchType p κ κ'
        -- A logical variable inside of this forall may have been equated with a type that contains this forall's binding.
        -- To prevent a capture, this forall is alpha converted to  new rigid variable that doesn't exist in the current environment.
        -- This alpha renaming does not convert under logic variables.
        vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
        let αf = fresh vars α
        let ς2 = convertType αf α ς
        let ς'2 = convertType αf α' ς'
        augmentKindEnvironment p αf π κ maxBound $ unifyPoly ς2 ς'2
        pure ()
    unifyPoly
      (Core.MonoType σ)
      (Core.MonoType σ') =
        matchType p σ σ'
    unifyPoly ς ς' = quit $ TypePolyMismatch p ς ς'

matchErasure _ Transparent Transparent = pure ()
matchErasure _ Concrete Concrete = pure ()
matchErasure p π π' = quit $ ErasureMismatch p π π'

matchInstanciation _ InstantiateEmpty InstantiateEmpty = pure ()
matchInstanciation p (InstantiateType σ θ) (InstantiateType σ' θ') = do
  matchType p σ σ'
  matchInstanciation p θ θ'
matchInstanciation p _ _ = quit $ InstantiationLengthMismatch p

freshTypeVariable p κ = (Core.Type . TypeLogical) <$> (levelCounter <$> getState >>= freshTypeVariableRaw p Transparent κ)

freshRepresentationKindVariable p = freshTypeVariable p (Core.Type Representation)

freshSizeKindVariable p = freshTypeVariable p (Core.Type Size)

freshSignednessKindVariable p = freshTypeVariable p (Core.Type Signedness)

freshOrderabilityVariable p = freshTypeVariable p (Core.Type Unification)

freshMetaTypeVariable p = do
  freshTypeVariable p (Core.Type Type)

freshMultiplicityKindVariable p = do
  freshTypeVariable p (Core.Type Multiplicity)

freshPretypeTypeVariable p = do
  s <- freshRepresentationKindVariable p
  τ <- freshMultiplicityKindVariable p
  freshTypeVariable p (Core.Type $ Pretype s τ)

freshBoxedTypeVariable p = do
  freshTypeVariable p (Core.Type Boxed)

freshRegionTypeVariable p = do
  freshTypeVariable p $ Core.Type $ Region

freshLabelTypeVariable p = do
  freshTypeVariable p $ Core.Type $ Label

checkKind _ (Core.Type (Kind σ)) = pure (σ)
checkKind p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkKind p σ
    UnboundType _ π κ l -> do
      ρ <- freshOrderabilityVariable p
      unifyVariable p x π κ l (Core.Type (Kind ρ))
      pure ρ
checkKind p σ = quit $ ExpectedKind p σ

checkRepresentation _ (Core.Type Representation) = pure ()
checkRepresentation p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkRepresentation p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l (Core.Type Representation)
      pure ()
checkRepresentation p σ = quit $ ExpectedRepresentation p σ

checkMultiplicity _ (Core.Type Multiplicity) = pure ()
checkMultiplicity p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkMultiplicity p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l (Core.Type Multiplicity)
      pure ()
checkMultiplicity p σ = quit $ ExpectedMultiplicity p σ

checkSize _ (Core.Type Size) = pure ()
checkSize p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkSize p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l (Core.Type Size)
      pure ()
checkSize p σ = quit $ ExpectedSize p σ

checkSignedness _ (Core.Type Signedness) = pure ()
checkSignedness p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkSignedness p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l (Core.Type Signedness)
      pure ()
checkSignedness p σ = quit $ ExpectedSignedness p σ

checkType _ (Core.Type Type) = pure ()
checkType p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkType p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l (Core.Type Type)
      pure ()
checkType p σ = quit $ ExpectedType p σ

checkPretype _ (Core.Type (Pretype σ τ)) = pure (σ, τ)
checkPretype p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkPretype p σ
    UnboundType _ π κ l -> do
      σ <- freshRepresentationKindVariable p
      τ <- freshMultiplicityKindVariable p
      unifyVariable p x π κ l (Core.Type $ Pretype σ τ)
      pure (κ, τ)
checkPretype p σ = quit $ ExpectedPretype p σ

checkBoxed _ (Core.Type Boxed) = pure ()
checkBoxed p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkBoxed p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l (Core.Type Boxed)
      pure ()
checkBoxed p σ = quit $ ExpectedBoxed p σ

checkRegion _ (Core.Type Region) = pure ()
checkRegion p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkRegion p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l (Core.Type Region)
      pure ()
checkRegion p σ = quit $ ExpectedRegion p σ

checkPropoitional _ (Core.Type Propositional) = pure ()
checkPropoitional p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkPropoitional p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l (Core.Type Propositional)
      pure ()
checkPropoitional p σ = quit $ ExpectedPropositional p σ

checkUnification _ (Core.Type Unification) = pure ()
checkUnification p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkUnification p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l (Core.Type Unification)
      pure ()
checkUnification p σ = quit $ ExpectedUnification p σ

checkInline _ (Core.Type (Inline σ τ π)) = pure (σ, τ, π)
checkInline p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkInline p σ
    UnboundType _ π' κ l -> do
      σ <- freshMetaTypeVariable p
      π <- freshMultiplicityKindVariable p
      τ <- freshMetaTypeVariable p
      unifyVariable p x π' κ l (Core.Type (Inline σ π τ))
      pure (σ, π, τ)
checkInline p σ = quit $ ExpectedInline p σ

checkFunctionPointer _ (Core.Type (FunctionPointer σ τ π)) = pure (σ, τ, π)
checkFunctionPointer p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkFunctionPointer p σ
    UnboundType _ π' κ l -> do
      σ <- freshPretypeTypeVariable p
      π <- freshRegionTypeVariable p
      τ <- freshPretypeTypeVariable p
      unifyVariable p x π' κ l (Core.Type $ FunctionPointer σ π τ)
      pure (σ, π, τ)
checkFunctionPointer p σ = quit $ ExpectedFunctionPointer p σ

checkFunctionLiteralType _ (Core.Type (FunctionLiteralType σ τ π)) = pure (σ, τ, π)
checkFunctionLiteralType p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkFunctionLiteralType p σ
    UnboundType _ π' κ l -> do
      σ <- freshPretypeTypeVariable p
      π <- freshRegionTypeVariable p
      τ <- freshPretypeTypeVariable p
      unifyVariable p x π' κ l (Core.Type $ FunctionLiteralType σ π τ)
      pure (σ, π, τ)
checkFunctionLiteralType p σ = quit $ ExpectedFunctionLiteralType p σ

checkUnique _ (Core.Type (Unique σ)) = pure σ
checkUnique p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkUnique p σ
    UnboundType _ π κ l -> do
      σ <- freshBoxedTypeVariable p
      unifyVariable p x π κ l (Core.Type $ Unique σ)
      pure σ
checkUnique p σ = quit $ ExpectedUnique p σ

checkPointer _ (Core.Type (Pointer σ)) = pure σ
checkPointer p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkPointer p σ
    UnboundType _ π κ l -> do
      σ <- freshPretypeTypeVariable p
      unifyVariable p x π κ l (Core.Type $ Pointer σ)
      pure (σ)
checkPointer p σ = quit $ ExpectedPointer p σ

checkArray _ (Core.Type (Array σ)) = pure σ
checkArray p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkArray p σ
    UnboundType _ π κ l -> do
      σ <- freshPretypeTypeVariable p
      unifyVariable p x π κ l (Core.Type $ Array σ)
      pure (σ)
checkArray p σ = quit $ ExpectedArray p σ

checkEffect _ (Core.Type (Effect σ τ)) = pure (σ, τ)
checkEffect p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkEffect p σ
    UnboundType _ π' κ l -> do
      σ <- freshPretypeTypeVariable p
      π <- freshRegionTypeVariable p
      unifyVariable p x π' κ l (Core.Type $ Effect σ π)
      pure (σ, π)
checkEffect p σ = quit $ ExpectedEffect p σ

checkShared _ (Core.Type (Shared σ τ)) = pure (σ, τ)
checkShared p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkShared p σ
    UnboundType _ π' κ l -> do
      σ <- freshBoxedTypeVariable p
      π <- freshRegionTypeVariable p
      unifyVariable p x π' κ l (Core.Type $ Shared σ π)
      pure (σ, π)
checkShared p σ = quit $ ExpectedShared p σ

checkNumber _ (Core.Type (Number σ τ)) = pure (σ, τ)
checkNumber p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkNumber p σ
    UnboundType _ π κ l -> do
      ρ1 <- freshSignednessKindVariable p
      ρ2 <- freshSizeKindVariable p
      unifyVariable p x π κ l (Core.Type $ Number ρ1 ρ2)
      pure (ρ1, ρ2)
checkNumber p σ = quit $ ExpectedNumber p σ

checkBoolean _ (Core.Type Boolean) = pure ()
checkBoolean p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkBoolean p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l (Core.Type $ Boolean)
      pure ()
checkBoolean p σ = quit $ ExpectedBoolean p σ

checkStep _ (Core.Type (Step σ τ)) = pure (σ, τ)
checkStep p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkStep p σ
    UnboundType _ π κ l -> do
      σ <- freshPretypeTypeVariable p
      τ <- freshPretypeTypeVariable p
      unifyVariable p x π κ l (Core.Type $ Step σ τ)
      pure (σ, τ)
checkStep p σ = quit $ ExpectedStep p σ

checkLabel _ (Core.Type Label) = pure ()
checkLabel p (Core.Type (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkLabel p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l (Core.Type Label)
      pure ()
checkLabel p σ = quit $ ExpectedLabel p σ

data Mode = InlineMode | SymbolMode

augmentVariableLinear p x l ς check = do
  Checked e σ lΓ <- augmentTypeEnvironment x p l ς check
  case count x lΓ of
    Single -> pure ()
    _ -> matchType p l unrestricted
  pure $ Checked e σ (Remove x lΓ)

capture p base lΓ = do
  let captures = variablesUsed lΓ
  for (Set.toList captures) $ \x -> do
    (TermBinding _ l _) <- fromJust <$> Map.lookup x <$> typeEnvironment <$> askEnvironment
    matchType p l (Core.Type $ TypeBoolean $ TypeOr base l)
    pure ()
  pure ()

requireUnrestricted p σ = do
  κ <- reconstruct p σ
  (_, l) <- checkPretype p κ
  matchType p l unrestricted
  pure ()

-- todo relabel seems somewhat fragile here
-- this depends on `KindChecked σ _ _ <- kindCheck τ`, never having unification variables in σ
-- because relabel ignores unification variables
augmentTermMetaPattern (Core.TermMetaPattern p (PatternVariable x π σ)) =
  augmentVariableLinear p x π (relabel (Core.MonoType σ))

nullEffect σ = Core.MonoType $ Core.Type $ Effect σ none

augmentTermPattern pm = go pm
  where
    go (Core.TermPattern p (RuntimePatternVariable x σ)) = \e -> do
      κ <- reconstruct p σ
      (_, l) <- checkPretype p κ
      augmentVariableLinear p x l (Core.MonoLabel (nullEffect σ)) e
    go (Core.TermPattern _ (RuntimePatternTuple pms)) = foldr (.) id (map go pms)
    go (Core.TermPattern _ (RuntimePatternBoolean _)) = id

checkSolid p σ = do
  (ρ, _) <- checkPretype p =<< reconstruct p σ
  erasureEntail p Concrete ρ

typeCheckMetaPattern :: Surface.TermMetaPattern p -> Check p (TermMetaPatternUnify p, TypeUnify, TypeUnify)
typeCheckMetaPattern = \case
  (Surface.TermMetaPattern p (PatternVariable x π σ)) -> do
    π <- case π of
      Surface.Type p (Hole ()) -> freshMultiplicityKindVariable p
      π -> do
        (π, ()) <- secondM (checkMultiplicity p) =<< kindCheck π
        pure (flexible π)
    σ <- case σ of
      Surface.Type p (Hole ()) -> freshMetaTypeVariable p
      σ -> do
        (σ, ()) <- secondM (checkType p) =<< kindCheck σ
        pure (flexible σ)
    pure (Core.TermMetaPattern p (PatternVariable x π σ), π, σ)

typeCheckRuntimePattern = \case
  (Surface.TermPattern p (RuntimePatternVariable x σ)) -> do
    σ' <- case σ of
      Surface.Type p (Hole ()) -> freshPretypeTypeVariable p
      σ -> do
        (σ', _) <- traverse (checkPretype p) =<< kindCheck σ
        pure (flexible σ')
    checkSolid p σ'
    pure (Core.TermPattern p $ RuntimePatternVariable x σ', σ')
  (Surface.TermPattern p (RuntimePatternTuple pms)) -> do
    (pms, σs) <- unzip <$> traverse typeCheckRuntimePattern pms
    pure (Core.TermPattern p $ RuntimePatternTuple pms, Core.Type (Tuple σs))
  (Surface.TermPattern p (RuntimePatternBoolean b)) -> do
    pure (Core.TermPattern p $ RuntimePatternBoolean b, Core.Type $ Boolean)

kindCheckScheme :: Mode -> Surface.TypeScheme p -> Check p (TypeSchemeInfer, TypeUnify)
kindCheckScheme mode =
  \case
    Surface.TypeScheme p (Surface.MonoType σ) -> do
      (σ', _) <- secondM (checkType p) =<< kindCheck σ
      pure (Core.MonoType σ', Core.Type Type)
    Surface.TypeScheme _ (Surface.TypeForall pm σ) -> do
      pm' <- kindCheckPattern mode pm
      augmentTypePatternLevel pm' $ do
        (σ', _) <- kindCheckScheme mode σ
        pure $ (Core.TypeForall (toTypePattern pm') σ', Core.Type $ Type)

kindCheckPattern :: Mode -> Surface.TypePattern p -> Check p (TypePatternIntermediate p)
kindCheckPattern mode (Surface.TypePattern p x π κ) = do
  (κ, _) <- secondM (checkKind p) =<< kindCheck κ
  case mode of
    SymbolMode -> matchErasure p π Transparent
    InlineMode -> pure ()
  pure (TypePatternIntermediate p x π κ)

kindCheck :: Surface.Type p -> Check p (TypeInfer, TypeUnify)
kindCheck (Surface.Type p σ) = case σ of
  TypeConstant (TypeVariable x) -> do
    Map.lookup x <$> kindEnvironment <$> askEnvironment >>= \case
      Just (TypeBinding _ _ κ _) -> pure (Core.Type $ TypeConstant $ TypeVariable x, κ)
      Nothing -> do
        heading <- moduleScope <$> askEnvironment
        kindCheck (Surface.Type p $ TypeConstant $ TypeGlobalVariable $ globalType heading x)
  TypeConstant (TypeGlobalVariable x) -> do
    Map.lookup x <$> kindGlobalEnvironment <$> askEnvironment >>= \case
      Just (TypeBinding _ _ κ _) -> pure (Core.Type $ TypeConstant $ TypeGlobalVariable x, κ)
      Nothing ->
        Map.lookup x <$> typeGlobalSynonyms <$> askEnvironment >>= \case
          Just σ -> do
            κ <- reconstruct p (flexible σ)
            pure (flexible σ, κ)
          Nothing -> quit $ UnknownTypeGlobalIdentifier p x
  Inline σ π τ -> do
    (σ', _) <- secondM (checkType p) =<< kindCheck σ
    (π', _) <- secondM (checkMultiplicity p) =<< kindCheck π
    (τ', _) <- secondM (checkType p) =<< kindCheck τ
    pure (Core.Type $ Inline σ' π' τ', Core.Type $ Type)
  Poly σ λ -> do
    (σ, _) <- secondM (checkLabel p) =<< kindCheck σ
    (ς, κ) <- kindCheckScheme InlineMode λ
    pure (Core.Type $ Poly σ ς, κ)
  FunctionPointer σ π τ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (Core.Type $ FunctionPointer σ' π' τ', Core.Type $ Pretype (Core.Type $ KindRuntime $ PointerRep) unrestricted)
  FunctionLiteralType σ π τ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (Core.Type $ FunctionLiteralType σ' π' τ', Core.Type $ Type)
  Tuple σs -> do
    (σs, (ρs, τs)) <- second unzip <$> unzip <$> traverse (secondM (checkPretype p) <=< kindCheck) σs
    let τ = foldr (\σ τ -> Core.Type $ TypeBoolean $ TypeAnd σ τ) unrestricted τs
    pure (Core.Type $ Tuple σs, Core.Type $ Pretype (Core.Type $ KindRuntime $ StructRep ρs) τ)
  Step σ τ -> do
    (σ, (κ, _)) <- secondM (checkPretype p) =<< kindCheck σ
    (τ, (ρ, _)) <- secondM (checkPretype p) =<< kindCheck τ
    let union = Core.Type $ KindRuntime $ UnionRep $ [κ, ρ]
    let wrap = Core.Type $ KindRuntime $ StructRep $ [Core.Type $ KindRuntime $ WordRep $ Core.Type $ KindSize $ Byte, union]
    pure (Core.Type $ Step σ τ, Core.Type $ Pretype wrap $ linear)
  Effect σ π -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    pure (Core.Type $ Effect σ' π', Core.Type $ Type)
  Unique σ -> do
    (σ', _) <- secondM (checkBoxed p) =<< kindCheck σ
    pure (Core.Type $ Unique σ', Core.Type $ Pretype (Core.Type $ KindRuntime $ PointerRep) linear)
  Shared σ π -> do
    (σ', _) <- secondM (checkBoxed p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    pure (Core.Type $ Shared σ' π', Core.Type $ Pretype (Core.Type $ KindRuntime $ PointerRep) unrestricted)
  Pointer σ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    pure (Core.Type $ Pointer σ', Core.Type $ Boxed)
  Array σ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    pure (Core.Type $ Array σ', Core.Type $ Boxed)
  Number ρ1 ρ2 -> do
    (ρ1', _) <- secondM (checkSignedness p) =<< kindCheck ρ1
    (ρ2', _) <- secondM (checkSize p) =<< kindCheck ρ2
    pure (Core.Type $ Number ρ1' ρ2', Core.Type $ Pretype (Core.Type $ KindRuntime $ WordRep (flexible ρ2')) unrestricted)
  Boolean -> do
    pure (Core.Type $ Boolean, Core.Type $ Pretype (Core.Type $ KindRuntime $ WordRep $ Core.Type $ KindSize $ Byte) unrestricted)
  TypeConstant World -> do
    pure (Core.Type $ TypeConstant World, Core.Type Region)
  TypeLogical v -> absurd v
  Type -> do
    pure (Core.Type Type, Core.Type $ Kind (Core.Type Syntactic))
  Region -> pure (Core.Type Region, Core.Type $ Kind (Core.Type Propositional))
  KindRuntime PointerRep -> pure (Core.Type $ KindRuntime PointerRep, Core.Type Representation)
  KindRuntime (StructRep κs) -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< kindCheck) κs
    pure (Core.Type (KindRuntime (StructRep κs')), Core.Type Representation)
  KindRuntime (UnionRep κs) -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< kindCheck) κs
    pure (Core.Type (KindRuntime (UnionRep κs')), Core.Type Representation)
  KindRuntime (WordRep κ) -> do
    (κ', _) <- secondM (checkSize p) =<< kindCheck κ
    pure (Core.Type (KindRuntime (WordRep κ')), Core.Type Representation)
  KindSize κ -> pure (Core.Type (KindSize κ), Core.Type Size)
  KindSignedness κ -> pure (Core.Type (KindSignedness κ), Core.Type Signedness)
  Pretype κ τ -> do
    (κ', _) <- secondM (checkRepresentation p) =<< kindCheck κ
    (τ', _) <- secondM (checkMultiplicity p) =<< kindCheck τ
    pure (Core.Type $ Pretype κ' τ', Core.Type $ Kind (Core.Type Syntactic))
  Boxed -> do
    pure (Core.Type $ Boxed, Core.Type $ Kind (Core.Type Syntactic))
  Multiplicity -> do
    pure (Core.Type $ Multiplicity, Core.Type $ Kind (Core.Type Propositional))
  Representation -> pure (Core.Type Representation, Core.Type $ Kind (Core.Type Syntactic))
  Size -> pure (Core.Type Size, Core.Type $ Kind (Core.Type Syntactic))
  Signedness -> pure (Core.Type Signedness, Core.Type $ Kind (Core.Type Syntactic))
  Kind ρ -> do
    (ρ, _) <- secondM (checkUnification p) =<< kindCheck ρ
    pure (Core.Type (Kind ρ), Core.Type Top)
  Syntactic -> do
    pure (Core.Type Syntactic, Core.Type Unification)
  Propositional -> do
    pure (Core.Type Propositional, Core.Type Unification)
  Unification -> do
    pure (Core.Type Unification, Core.Type Top)
  AmbiguousLabel -> do
    pure (Core.Type AmbiguousLabel, Core.Type Label)
  Label -> do
    pure (Core.Type Label, Core.Type $ Top)
  TypeTrue -> do
    π <- freshTypeVariable p (Core.Type $ Kind (Core.Type $ Propositional))
    pure (Core.Type $ TypeTrue, π)
  TypeFalse -> do
    π <- freshTypeVariable p (Core.Type $ Kind (Core.Type $ Propositional))
    pure (Core.Type $ TypeFalse, π)
  TypeBoolean (TypeXor σ τ) -> do
    (σ', κ) <- kindCheck σ
    (τ', κ') <- kindCheck τ
    matchType p κ κ'
    ρ <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (Core.Type $ TypeBoolean $ TypeXor σ' τ', κ)
  TypeBoolean (TypeOr σ τ) -> do
    (σ', κ) <- kindCheck σ
    (τ', κ') <- kindCheck τ
    matchType p κ κ'
    ρ <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (Core.Type $ TypeBoolean $ TypeOr σ' τ', κ)
  TypeBoolean (TypeAnd σ τ) -> do
    (σ', κ) <- kindCheck σ
    (τ', κ') <- kindCheck τ
    matchType p κ κ'
    ρ <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (Core.Type $ TypeBoolean $ TypeAnd σ' τ', κ)
  TypeBoolean (TypeNot σ) -> do
    (σ', κ) <- kindCheck σ
    ρ <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (Core.Type $ TypeBoolean $ TypeNot σ', κ)
  Top -> quit $ NotTypable p
  Hole () -> quit $ NotTypable p

instantiate p ς = case ς of
  Core.MonoType σ -> pure (σ, Core.InstantiateEmpty)
  Core.TypeForall (Core.TypePattern x π κ) σ -> do
    τ <- freshTypeVariable p κ
    erasureEntail p π τ
    (ς, θ) <- instantiate p $ substituteType τ x σ
    pure (ς, Core.InstantiateType τ θ)

instantiateLabel instantiate p (Core.MonoLabel ς) = instantiate p ς
instantiateLabel instantiate p (Core.LabelForall x ς) = do
  τ <- freshLabelTypeVariable p
  instantiateLabel instantiate p $ substituteType τ x ς

expectTypeAnnotation p Nothing = quit $ ExpectedTypeAnnotation p
expectTypeAnnotation _ (Just σ) = pure σ

validateType σ = fst <$> kindCheck σ

data Checked p σ = Checked (TermUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

data CheckedScheme p σ = CheckedScheme (TermSchemeUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

regions [] = none
regions σs = foldl1 (\π1 π2 -> Core.Type $ TypeBoolean $ TypeOr π1 π2) σs

validateInstantation p θ θ' = do
  θ' <- for θ' $ \σ -> do
    (τ, _) <- kindCheck σ
    let ς = relabel $ Core.MonoType $ flexible τ
    (σ, _) <- instantiateLabel instantiate p ς
    pure σ
  matchInstanciation p θ (Core.instanciation θ')

typeCheck :: forall p. Surface.Term p -> Check p (Checked p TypeUnify)
typeCheck (Surface.Term p e) = case e of
  TermRuntime (Variable x θ') -> do
    mσ <- Map.lookup x <$> typeEnvironment <$> askEnvironment
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiateLabel instantiate p σ
        case θ' of
          Surface.InstantiationInfer -> pure ()
          Surface.Instantiation θ' -> validateInstantation p θ θ'
        pure $ Checked (Core.Term p $ TermRuntime $ Variable x θ) τ (Use x)
      Nothing -> do
        heading <- moduleScope <$> askEnvironment
        typeCheck (Surface.Term p $ GlobalVariable (globalTerm heading x) θ')
  GlobalVariable x θ' -> do
    mσ <- Map.lookup x <$> typeGlobalEnvironment <$> askEnvironment
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiateLabel instantiate p σ
        case θ' of
          Surface.InstantiationInfer -> pure ()
          Surface.Instantiation θ' -> validateInstantation p θ θ'
        -- todo useNothing here is kinda of a hack
        pure $ Checked (Core.Term p $ GlobalVariable x θ) τ useNothing
      Nothing -> quit $ UnknownGlobalIdentifier p x
  InlineAbstraction (Surface.TermMetaBound pm e) -> do
    (pm', π, σ) <- typeCheckMetaPattern pm
    Checked e' τ lΓ <- augmentTermMetaPattern pm' (typeCheck e)
    pure $ Checked (Core.Term p $ InlineAbstraction $ Core.TermMetaBound pm' e') (Core.Type $ Inline σ π τ) lΓ
  InlineApplication e1 e2 -> do
    Checked e1' (σ, π, τ) lΓ1 <- traverse (checkInline p) =<< typeCheck e1
    Checked e2' σ' lΓ2 <- typeCheck e2
    matchType p σ σ'
    capture p π lΓ2
    pure $ Checked (Core.Term p $ InlineApplication e1' e2') τ (lΓ1 `combine` lΓ2)
  Bind e1 (Surface.TermMetaBound pm e2) -> do
    Checked e1' τ lΓ1 <- typeCheck e1
    (pm', π, τ') <- typeCheckMetaPattern pm
    matchType p τ τ'
    Checked e2' σ lΓ2 <- augmentTermMetaPattern pm' $ typeCheck e2
    capture p π lΓ1
    pure $ Checked (Core.Term p $ Bind e1' $ Core.TermMetaBound pm' e2') σ (lΓ1 `combine` lΓ2)
  PolyIntroduction λ -> do
    CheckedScheme eς σ lΓ <- typeCheckScheme InlineMode λ
    τ <- freshLabelTypeVariable p
    vars <- typeLogicalMap <$> getState
    let σ' = zonk vars σ
    pure $ Checked (Core.Term p $ PolyIntroduction $ eς) (Core.Type $ Poly τ σ') lΓ
  PolyElimination e θ' -> do
    Checked e ς lΓ <- leveled $ typeCheck e
    elimatePoly e ς lΓ
    where
      elimatePoly e (Core.Type (Poly l ς)) lΓ = do
        validateLevel l
        (σ, θ) <- instantiate p ς
        case θ' of
          Surface.InstantiationInfer -> pure ()
          Surface.Instantiation θ' -> validateInstantation p θ θ'
        pure $ Checked (Core.Term p $ PolyElimination e θ) σ lΓ
      elimatePoly e (Core.Type (TypeLogical v)) lΓ =
        (! v) <$> typeLogicalMap <$> getState >>= \case
          LinkType σ -> elimatePoly e σ lΓ
          _ -> quit $ ExpectedTypeAnnotation p
      elimatePoly _ _ _ = quit $ ExpectedTypeAnnotation p
      validateLevel (Core.Type (TypeLogical v)) =
        (! v) <$> typeLogicalMap <$> getState >>= \case
          LinkType σ -> validateLevel σ
          UnboundType p _ _ level' -> do
            level <- levelCounter <$> getState
            if level >= level'
              then quit $ ExpectedTypeAnnotation p
              else pure ()
      validateLevel _ = quit $ ExpectedTypeAnnotation p
  TermRuntime (Alias e1 (Surface.TermBound pm e2)) -> do
    (pm', τ) <- typeCheckRuntimePattern pm
    Checked e1' (τ', π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p τ τ'
    Checked e2' (σ, π2) lΓ2 <- traverse (checkEffect p) =<< augmentTermPattern pm' (typeCheck e2)
    let π = regions [π1, π2]
    pure $ Checked (Core.Term p $ TermRuntime $ Alias e1' $ Core.TermBound pm' e2') (Core.Type $ Effect σ π) (lΓ1 `combine` lΓ2)
  TermRuntime (Case e NoType λs NoType) -> do
    Checked e (τ, π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e
    σ <- freshPretypeTypeVariable p
    checkSolid p σ
    (e2, pm, πs, lΓ2) <- fmap unzip4 $
      for λs $ \(Surface.TermBound pm e2) -> do
        (pm, τ') <- typeCheckRuntimePattern pm
        matchType p τ τ'
        Checked e2 (σ', π) lΓ2 <- traverse (checkEffect p) =<< augmentTermPattern pm (typeCheck e2)
        matchType p σ σ'
        pure (e2, pm, π, lΓ2)
    let π = regions $ π1 : πs
    pure $
      Checked
        (Core.Term p $ TermRuntime $ Case e τ (zipWith Core.TermBound pm e2) σ)
        (Core.Type $ Effect σ π)
        (lΓ1 `combine` branchAll lΓ2)
  TermRuntime (Extern sym NoType NoType NoType) -> do
    σ <- freshPretypeTypeVariable p
    checkSolid p σ
    π <- freshRegionTypeVariable p
    τ <- freshPretypeTypeVariable p
    checkSolid p τ
    pure $
      Checked
        (Core.Term p $ TermRuntime $ Extern sym σ π τ)
        (Core.Type $ Effect (Core.Type $ FunctionPointer σ π τ) none)
        useNothing
  TermRuntime (FunctionApplication e1 e2 NoType) -> do
    Checked e1' ((σ, π2, τ), π1) lΓ1 <- traverse (firstM (checkFunctionPointer p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' (σ', π3) lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
    matchType p σ σ'
    checkSolid p τ
    let π = regions [π1, π2, π3]
    pure $
      Checked
        (Core.Term p $ TermRuntime $ FunctionApplication e1' e2' σ)
        (Core.Type $ Effect τ π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (TupleIntroduction es) -> do
    checked <- traverse (traverse (checkEffect p) <=< typeCheck) es
    let (es, σs, πs, lΓs) = unzip4 $ map (\(Checked es (σ, π) lΓ) -> (es, σ, π, lΓ)) checked
    let π = regions πs
    pure $
      Checked
        (Core.Term p $ TermRuntime $ TupleIntroduction es)
        (Core.Type $ Effect (Core.Type (Tuple σs)) π)
        (combineAll lΓs)
  TermRuntime (ReadReference e) -> do
    Checked e' ((σ, π2), π1) lΓ <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck e
    let π = regions [π1, π2]
    requireUnrestricted p σ
    checkSolid p σ
    pure $ Checked (Core.Term p $ TermRuntime $ ReadReference e') (Core.Type $ Effect σ π) lΓ
  TermRuntime (WriteReference ep ev NoType) -> do
    Checked ep ((σ, π2), π1) lΓ1 <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
    Checked ev (σ', π3) lΓ2 <- traverse (checkEffect p) =<< typeCheck ev
    matchType p σ σ'
    checkSolid p σ
    let π = regions [π1, π2, π3]
    requireUnrestricted p σ
    pure $
      Checked
        (Core.Term p $ TermRuntime $ WriteReference ep ev σ)
        (Core.Type $ Effect (Core.Type $ Tuple []) π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (NumberLiteral v NoType) -> do
    ρ1 <- freshSignednessKindVariable p
    ρ2 <- freshSizeKindVariable p
    erasureEntail p Concrete ρ2
    pure $
      Checked
        (Core.Term p $ TermRuntime (NumberLiteral v (Core.Type $ Number ρ1 ρ2)))
        (Core.Type $ Effect (Core.Type $ Number ρ1 ρ2) none)
        useNothing
  TermRuntime (Arithmatic o e1 e2 NoType) -> do
    Checked e1' ((ρ1, ρ2), π1) lΓ1 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' ((ρ1', ρ2'), π2) lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e2
    matchType p ρ1 ρ1'
    matchType p ρ2 ρ2'
    erasureEntail p Concrete ρ1
    erasureEntail p Concrete ρ2
    let π = regions [π1, π2]
    pure $
      Checked
        (Core.Term p $ TermRuntime $ Arithmatic o e1' e2' ρ1)
        (Core.Type $ Effect (Core.Type $ Number ρ1 ρ2) π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (Relational o e1 e2 NoType NoType) -> do
    Checked e1' ((ρ1, ρ2), π1) lΓ1 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' ((ρ1', ρ2'), π2) lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e2
    matchType p ρ1 ρ1'
    matchType p ρ2 ρ2'
    erasureEntail p Concrete ρ1
    erasureEntail p Concrete ρ2
    let π = regions [π1, π2]
    pure $
      Checked
        (Core.Term p $ TermRuntime $ Relational o e1' e2' (Core.Type $ Number ρ1 ρ2) ρ1)
        (Core.Type $ Effect (Core.Type $ Boolean) π)
        (lΓ1 `combine` lΓ2)
  FunctionLiteral (Surface.TermBound pm e) τ' π' -> do
    (pm', σ) <- typeCheckRuntimePattern pm
    Checked e' (τ, π) lΓ <- traverse (checkEffect p) =<< augmentTermPattern pm' (typeCheck e)
    case τ' of
      Surface.Type _ (Hole ()) -> pure ()
      τ' -> do
        (τ', _) <- kindCheck τ'
        matchType p τ (flexible τ')
    case π' of
      Surface.Type _ (Hole ()) -> pure ()
      π' -> do
        (π', _) <- kindCheck π'
        matchType p π (flexible π')
    pure $ Checked (Core.Term p $ FunctionLiteral (Core.TermBound pm' e') τ π) (Core.Type $ FunctionLiteralType σ π τ) lΓ
  Annotation (Surface.TypeAnnotation e τ) -> do
    Checked e σ lΓ <- typeCheck e
    (τ, _) <- kindCheck τ
    let ς = relabel $ Core.MonoType $ flexible τ
    (σ', _) <- instantiateLabel instantiate p ς
    (σ'', _) <- instantiateLabel instantiate p ς
    matchType p σ σ'
    pure $ Checked e σ'' lΓ
  Annotation (Surface.PretypeAnnotation e σ') -> do
    Checked e τ lΓ <- typeCheck e
    (σ, _) <- checkEffect p τ
    σ' <- flexible <$> fst <$> kindCheck σ'
    matchType p σ σ'
    pure $ Checked e τ lΓ
  TermRuntime (BooleanLiteral b) -> do
    pure $ Checked (Core.Term p $ TermRuntime $ BooleanLiteral b) (Core.Type $ Effect (Core.Type Boolean) none) useNothing
  TermSugar (If eb et ef NoType) -> do
    Checked eb' ((), π1) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck eb
    Checked et' (σ, π2) lΓ2 <- traverse (checkEffect p) =<< typeCheck et
    Checked ef' (σ', π3) lΓ3 <- traverse (checkEffect p) =<< typeCheck ef
    matchType p σ σ'
    let π = regions [π1, π2, π3]
    pure $
      Checked
        (Core.Term p $ TermSugar $ If eb' et' ef' $ Core.Type Boolean)
        (Core.Type $ Effect σ π)
        (lΓ1 `combine` (lΓ2 `branch` lΓ3))
  TermRuntime (PointerIncrement ep ei NoType) -> do
    Checked ep' ((σ, π2), π1) lΓ1 <- traverse (firstM (firstM (checkArray p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
    Checked ei' ((κ1, κ2), π3) lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck ei
    matchType p κ1 (Core.Type $ KindSignedness Unsigned)
    matchType p κ2 (Core.Type $ KindSize Native)
    checkSolid p σ
    let π = regions [π1, π3]
    pure $
      Checked
        (Core.Term p $ TermRuntime $ PointerIncrement ep' ei' σ)
        (Core.Type $ Effect (Core.Type $ Shared (Core.Type $ Array σ) π2) π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (Continue e NoType) -> do
    Checked e (σ, π) lΓ <- traverse (checkEffect p) =<< typeCheck e
    τ <- freshPretypeTypeVariable p
    checkSolid p τ
    let ρ = Core.Type $ Step τ σ
    pure $ Checked (Core.Term p $ TermRuntime $ Continue e ρ) (Core.Type $ Effect ρ π) lΓ
  TermRuntime (Break e NoType) -> do
    Checked e (τ, π) lΓ <- traverse (checkEffect p) =<< typeCheck e
    σ <- freshPretypeTypeVariable p
    checkSolid p σ
    let ρ = Core.Type $ Step τ σ
    pure $ Checked (Core.Term p $ TermRuntime $ Break e ρ) (Core.Type $ Effect ρ π) lΓ
  TermRuntime (Loop e1 (Surface.TermBound pm e2)) -> do
    (pm, σ) <- typeCheckRuntimePattern pm
    Checked e1 (σ', π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p σ σ'
    Checked e2 ((τ, σ''), π2) lΓ2 <- traverse (firstM (checkStep p) <=< checkEffect p) =<< augmentTermPattern pm (typeCheck e2)
    matchType p σ σ''
    capture p unrestricted lΓ2
    let π = regions [π1, π2]
    pure $ Checked (Core.Term p $ TermRuntime $ Loop e1 (Core.TermBound pm e2)) (Core.Type $ Effect τ π) (combine lΓ1 lΓ2)
  TermErasure (IsolatePointer e) -> do
    Checked e ((σ, π2), π) lΓ <- traverse (firstM (firstM (checkArray p) <=< checkShared p) <=< checkEffect p) =<< typeCheck e
    pure $
      Checked
        (Core.Term p $ TermErasure $ IsolatePointer e)
        (Core.Type $ Effect (Core.Type $ Shared (Core.Type $ Pointer σ) π2) π)
        lΓ
  TermSugar (Not e) -> do
    Checked e' ((), π) lΓ <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    pure $ Checked (Core.Term p $ TermSugar $ Not e') (Core.Type $ Effect (Core.Type Boolean) π) lΓ
  TermSugar (And e ey) -> do
    Checked e' ((), π1) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked ey' ((), π2) lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck ey
    let π = regions [π1, π2]
    pure $ Checked (Core.Term p $ TermSugar $ And e' ey') (Core.Type $ Effect (Core.Type Boolean) π) (lΓ1 `combine` (lΓ2 `branch` useNothing))
  TermSugar (Or e en) -> do
    Checked e' ((), π1) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked en' ((), π2) lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck en
    let π = regions [π1, π2]
    pure $ Checked (Core.Term p $ TermSugar $ Or e' en') (Core.Type $ Effect (Core.Type Boolean) π) (lΓ1 `combine` (useNothing `branch` lΓ2))
  TermSugar (Do e1 e2) -> do
    Checked e1' (τ, π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p τ (Core.Type $ Tuple [])
    Checked e2' (σ, π2) lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
    let π = regions [π1, π2]
    pure $ Checked (Core.Term p $ TermSugar $ Do e1' e2') (Core.Type $ Effect σ π) (lΓ1 `combine` lΓ2)
  TermErasure (Cast e NoType) -> do
    Checked e (σ, _) lΓ <- traverse (checkEffect p) =<< typeCheck e
    κ <- reconstruct p σ
    (ρ, _) <- checkPretype p κ
    m <- freshMultiplicityKindVariable p
    σ' <- freshTypeVariable p (Core.Type $ Pretype ρ m)
    checkSolid p σ'
    π' <- freshRegionTypeVariable p
    let τ = Core.Type $ Effect σ' π'
    pure $ Checked (Core.Term p $ TermErasure $ Cast e τ) τ lΓ

typeCheckScheme :: Mode -> Surface.TermScheme p -> Check p (CheckedScheme p TypeSchemeUnify)
typeCheckScheme mode (Surface.TermScheme p (Surface.TypeAbstraction pm e)) = do
  pm <- kindCheckPattern mode pm

  -- Shadowing type variables is prohibited
  vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
  let αo = intermediateBinder pm
      αn = fresh vars αo
      pm' = pm {intermediateBinder = αn}
      α = Core.Type $ TypeConstant $ TypeVariable $ αn

  augmentTypePatternLevel pm' $
    augmentSynonym αo α $ do
      CheckedScheme e' σ' lΓ <- typeCheckScheme mode e
      pure $
        CheckedScheme
          (Core.TermScheme p $ Core.TypeAbstraction (flexible $ toTypePattern pm') e')
          (Core.TypeForall (flexible $ toTypePattern pm') σ')
          lΓ
typeCheckScheme _ (Surface.TermScheme p (Surface.MonoTerm e)) = do
  Checked e σ lΓ <- typeCheck e
  pure $ CheckedScheme (Core.TermScheme p $ Core.MonoTerm e) (Core.MonoType σ) lΓ

defaultType p ρ = do
  ρ'@(Core.Type ρ) <- finish ρ
  case ρ of
    Representation -> pure $ Core.Type $ KindRuntime $ PointerRep
    Size -> pure $ Core.Type $ KindSize $ Int
    Signedness -> pure $ Core.Type $ KindSignedness $ Signed
    Region -> pure $ Core.Type $ TypeConstant World
    Multiplicity -> pure unrestricted
    Label -> pure $ Core.Type $ AmbiguousLabel
    (TypeLogical v) -> absurd v
    _ -> quit $ AmbiguousType p ρ'

unsolved ::
  Map TypeLogical (TypeLogicalState a) ->
  TypeUnify ->
  Map TypeLogical (a, Erasure, TypeUnify, Level)
unsolved vars σ = foldMap lookup σ
  where
    lookup x | LinkType σ <- vars ! x = unsolved vars σ
    lookup x | UnboundType p π κ l <- vars ! x = Map.singleton x (p, π, κ, l)
    lookup _ = Map.empty

unsolvedVariables vars σ = Map.keys (unsolved vars σ)

zonk :: TypeAlgebra u => Map TypeLogical (TypeLogicalState p) -> u TypeLogical -> u TypeLogical
zonk vars σ = runIdentity $ zonkType (Identity . get) σ
  where
    get x = case vars ! x of
      UnboundType _ _ _ _ -> Core.Type (TypeLogical x)
      LinkType σ -> zonk vars σ

finish :: TypeAlgebra u => u TypeLogical -> Check p (u Void)
finish σ = zonkType go σ
  where
    go x =
      (! x) <$> typeLogicalMap <$> getState >>= \case
        LinkType σ -> finish σ
        UnboundType p _ κ _ -> do
          σ <- defaultType p κ
          modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkType (flexible σ)) $ typeLogicalMap state}
          pure (flexible σ)

finishBooleans p = do
  solveBooleans
  sat <- booleans <$> getState
  case sat of
    [] -> pure ()
    σs -> quit $ TypeBooleanMismatch p $ map (\(σ, τ) -> Core.Type $ TypeBoolean $ TypeXor σ τ) σs

topologicalBoundsSort :: Map TypeLogical (TypeLogicalState p) -> [TypeLogical] -> [TypeLogical]
topologicalBoundsSort vars = runIdentity . sortTopological id quit (Identity . children)
  where
    quit x = error $ "unexpected cycle: " ++ show x
    children x = case vars ! x of
      LinkType σ -> unsolvedVariables vars σ
      UnboundType _ _ κ _ -> unsolvedVariables vars κ

generalizable mode x = do
  level <- levelCounter <$> getState
  (! x) <$> typeLogicalMap <$> getState >>= \case
    UnboundType p π κ level' -> do
      Core.Type ρ <- reconstruct p κ
      case ρ of
        _ | level >= level' -> pure False
        Top -> pure False
        Kind _ | InlineMode <- mode -> pure True
        Kind _ | Transparent <- π -> pure True
        Kind _ -> pure False
        σ -> error $ "generalization error " ++ show σ
    LinkType _ -> error "generalization error"

generalizeExact _ [] e = pure e
generalizeExact scope ((n, x) : remaining) e = do
  e <- generalizeExact scope remaining e
  (! x) <$> typeLogicalMap <$> getState >>= \case
    UnboundType p π κ _ -> do
      ( \f -> do
          modifyState $ \state ->
            state
              { typeLogicalMap = f $ typeLogicalMap state
              }
        )
        $ \σΓ -> Map.insert x (LinkType $ Core.Type $ TypeConstant $ TypeVariable $ TypeIdentifier n) σΓ
      pure (scope p n π κ e)
    _ -> error "generalization error"

-- todo refactor this
generalize :: Mode -> (TermUnify p, TypeUnify) -> Check p (TermSchemeUnify p, TypeSchemeUnify)
generalize mode (e@(Core.Term p _), σ) = do
  logical <- typeLogicalMap <$> getState
  vars <- filterM (generalizable mode) $ topologicalBoundsSort logical (unsolvedVariables logical σ)
  used <- usedVars <$> getState
  let names = filter (\x -> x `Set.notMember` used) $ temporaries uppers
  generalizeExact scope (zip names vars) (Core.TermScheme p $ Core.MonoTerm e, Core.MonoType σ)
  where
    scope p n π κ (e, σ) =
      ( Core.TermScheme p $ Core.TypeAbstraction (Core.TypePattern (TypeIdentifier n) π κ) e,
        Core.TypeForall (Core.TypePattern (TypeIdentifier n) π κ) σ
      )

typeCheckGlobalAuto ::
  Mode ->
  Surface.Term p ->
  Check p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalAuto mode e@(Surface.Term p _) = do
  Checked e σ _ <- leveled $ typeCheck e
  finishBooleans p
  (e, ς) <- generalize mode (e, σ)
  e <- simplify <$> finish e
  ς <- simplify <$> finish ς
  pure (e, ς)

typeCheckGlobalSchemed ::
  Mode ->
  Surface.TermScheme p ->
  Check p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalSchemed mode e@(Surface.TermScheme p _) = do
  CheckedScheme e ς _ <- leveled $ typeCheckScheme mode e
  finishBooleans p
  ς <- simplify <$> finish ς
  e <- simplify <$> finish e
  pure (e, ς)

typeCheckGlobalSyn :: Surface.Type p -> Check p TypeInfer
typeCheckGlobalSyn σ = do
  (σ, _) <- kindCheck σ
  pure σ

typeCheckGlobalNew :: Surface.Type p -> Check p (TypeInfer, TypeInfer)
typeCheckGlobalNew σ@(Surface.Type p _) = do
  (σ, κ) <- kindCheck σ
  checkPretype p κ
  κ <- finish κ
  pure (σ, κ)

typeCheckGlobalForward :: Surface.TypeScheme p -> Check p TypeSchemeInfer
typeCheckGlobalForward ς = do
  (ς, _) <- kindCheckScheme SymbolMode ς
  pure ς

typeCheckGlobalNewForward :: Surface.Type p -> Check p TypeInfer
typeCheckGlobalNewForward κ@(Surface.Type p _) = do
  (κ, _) <- kindCheck κ
  checkPretype p (flexible κ)
  pure κ

convertFunctionLiteral ς = case ς of
  Core.MonoType (Core.Type (FunctionLiteralType σ π τ)) -> nullEffect (Core.Type $ FunctionPointer σ π τ)
  Core.TypeForall pm ς -> Core.TypeForall pm $ convertFunctionLiteral ς
  _ -> error "not function literal"

typeCheckModule ::
  [(Path, Surface.Global p)] ->
  StateT
    (CheckEnvironment p)
    (Either (TypeError p))
    [(Path, Core.Global p)]
typeCheckModule [] = pure []
typeCheckModule ((path, item) : nodes) | heading <- Path.directory path = do
  environment <- get
  let run f = lift $ runChecker f environment {moduleScope = heading} emptyState
  item <- case item of
    Surface.Global e -> case e of
      Module.Inline (Surface.TermAuto e) -> do
        (e, σ) <- run (typeCheckGlobalAuto InlineMode e)
        updateTerm (flexible σ)
        pure $ Core.Global $ Module.Inline e
      Module.Inline (Surface.TermManual e) -> do
        (e, σ) <- run (typeCheckGlobalSchemed InlineMode e)
        updateTerm (flexible σ)
        pure $ Core.Global $ Module.Inline e
      Text (Surface.TermAuto e) -> do
        (e, σ) <- run (typeCheckGlobalAuto SymbolMode e)
        updateTerm (convertFunctionLiteral $ flexible σ)
        pure $ Core.Global $ Text e
      Text (Surface.TermManual e) -> do
        (e, σ) <- run (typeCheckGlobalSchemed SymbolMode e)
        updateTerm (convertFunctionLiteral $ flexible σ)
        pure $ Core.Global $ Text e
      Synonym σ -> do
        σ <- run $ typeCheckGlobalSyn σ
        updateSym σ
        pure $ Core.Global $ Synonym σ
      ForwardText ς -> do
        ς <- run $ typeCheckGlobalForward ς
        updateTerm (convertFunctionLiteral $ flexible ς)
        pure $ Core.Global $ ForwardText ς
      ForwardNewType κ -> do
        κ <- run $ typeCheckGlobalNewForward κ
        updateNewType' (flexible κ)
        pure $ Core.Global $ ForwardNewType κ
      where
        p = Surface.positionGlobal item
        updateTerm ς = modify $ \environment ->
          environment
            { typeGlobalEnvironment =
                Map.insert
                  (TermGlobalIdentifier path)
                  (TermBinding p unrestricted (relabel ς))
                  $ typeGlobalEnvironment environment
            }
        updateSym σ = modify $ \environment ->
          environment
            { typeGlobalSynonyms =
                Map.insert
                  (TypeGlobalIdentifier path)
                  σ
                  $ typeGlobalSynonyms environment
            }
        updateNewType' κ = modify $ \environment ->
          environment
            { kindGlobalEnvironment =
                Map.insertWith
                  (\_ x -> x)
                  (TypeGlobalIdentifier path)
                  (TypeBinding p Transparent κ minBound)
                  $ kindGlobalEnvironment environment
            }

  ((path, item) :) <$> typeCheckModule nodes
