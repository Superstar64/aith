module TypeCheck where

import Ast.Core
  ( Erasure (..),
    LabelSchemeUnify,
    TermMetaPatternUnify,
    TermSchemeInfer,
    TermSchemeUnify,
    TermUnify,
    TypeAlgebra,
    TypeInfer,
    TypeLogical (..),
    TypeSchemeInfer,
    TypeSchemeUnify,
    TypeUnify,
    convertBoolean,
    convertType,
    freeLocalVariablesType,
    relabel,
    simplify,
    substituteType,
    unconvertBoolean,
    zonkType,
  )
import qualified Ast.Core as Core
import qualified Ast.Surface as Surface
import Ast.Symbol hiding (combine)
import Control.Monad (filterM, replicateM, zipWithM, (<=<))
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
  | ExpectedFunctionPointer p Int TypeUnify
  | ExpectedFunctionLiteralType p Int TypeUnify
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
emptyEnvironment = CheckEnvironment Map.empty Map.empty Map.empty Map.empty root Map.empty Map.empty

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

data TypePatternIntermediate p = TypePatternIntermediate
  { intermediatePosition :: p,
    intermediateBinder :: TypeIdentifier,
    intermediateErasure :: Erasure,
    intermediateKind :: TypeInfer
  }

booleanConstantElimination x = do
  modifyState $ \state -> state {booleans = constantElimination $ booleans state}
  where
    constantElimination [] = []
    constantElimination ((σ, τ) : problems)
      | Set.member x $ freeLocalVariablesType σ <> freeLocalVariablesType τ =
        let σ' = substituteType Core.TypeTrue x σ
            σ'' = substituteType Core.TypeFalse x σ
            τ' = substituteType Core.TypeTrue x τ
            τ'' = substituteType Core.TypeFalse x τ
         in (σ', τ') : (σ'', τ'') : constantElimination problems
      | otherwise =
        (σ, τ) : constantElimination problems

augmentTypePatternLevel :: TypePatternIntermediate p -> Check p b -> Check p b
augmentTypePatternLevel (TypePatternIntermediate p x π κ) f = do
  useTypeVar x
  level <- levelCounter <$> getState
  f' <- augmentKindEnvironment p x π (flexible κ) (succ level) $ leveled $ f
  -- after leveled, `booleans` in state should be pre zonked
  booleanConstantElimination x
  pure f'
  where
    useTypeVar (TypeIdentifier x) = do
      modifyState $ \state -> state {usedVars = Set.insert x $ usedVars state}

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
  modifyState $ \state -> state {booleans = map (\σ -> (unconvertBoolean σ, Core.TypeFalse)) equations'}
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
    go σ = case σ of
      Core.TypeLogical x'
        | x == x' -> quit $ TypeOccursCheck p x σ'
        | otherwise ->
          (! x') <$> typeLogicalMap <$> getState >>= \case
            (UnboundType p' π κ lev') ->
              if lev' > lev
                then do
                  modifyState $ \state -> state {typeLogicalMap = Map.insert x' (UnboundType p' π κ lev) $ typeLogicalMap state}
                else pure ()
            (LinkType σ) -> recurse σ
      Core.TypeScheme σ ς -> do
        recurse σ
        occursPoly ς
      Core.TypeVariable x' -> do
        TypeBinding _ _ _ lev' <- (! x') <$> kindEnvironment <$> askEnvironment
        if lev' > lev
          then quit $ EscapingSkolemType p x'
          else pure ()
      Core.TypeGlobalVariable x' -> do
        TypeBinding _ _ _ lev' <- (! x') <$> kindGlobalEnvironment <$> askEnvironment
        if lev' > lev
          then error "type globals aren't supposed to be argumentable"
          else pure ()
      Core.Inline σ π τ -> do
        recurse σ
        recurse π
        recurse τ
      Core.FunctionPointer σ π τ -> do
        traverse recurse σ
        recurse π
        recurse τ
      Core.FunctionLiteralType σ π τ -> do
        traverse recurse σ
        recurse π
        recurse τ
      Core.Tuple σs -> do
        traverse recurse σs
        pure ()
      Core.Effect σ τ -> do
        recurse σ
        recurse τ
      Core.Unique σ -> do
        recurse σ
      Core.Shared σ π -> do
        recurse σ
        recurse π
      Core.Pointer σ -> recurse σ
      Core.Array σ -> recurse σ
      Core.Number _ _ -> pure ()
      Core.Boolean -> pure ()
      Core.Step σ τ -> do
        recurse σ
        recurse τ
      Core.World -> pure ()
      Core.Type -> pure ()
      Core.Region -> pure ()
      Core.Pretype κ τ -> do
        recurse κ
        recurse τ
      Core.Boxed -> pure ()
      Core.Multiplicity -> pure ()
      Core.PointerRepresentation -> pure ()
      Core.StructRepresentation κs -> traverse recurse κs >> pure ()
      Core.UnionRepresentation κs -> traverse recurse κs >> pure ()
      Core.WordRepresentation κ -> recurse κ
      Core.Signed -> pure ()
      Core.Unsigned -> pure ()
      Core.Byte -> pure ()
      Core.Short -> pure ()
      Core.Int -> pure ()
      Core.Long -> pure ()
      Core.Native -> pure ()
      Core.Representation -> pure ()
      Core.Size -> pure ()
      Core.Signedness -> pure ()
      Core.Kind σ -> do
        recurse σ
      Core.Syntactic -> pure ()
      Core.Propositional -> pure ()
      Core.Top -> pure ()
      Core.Unification -> pure ()
      Core.AmbiguousLabel -> pure ()
      Core.Label -> pure ()
      Core.TypeNot σ -> recurse σ
      Core.TypeAnd σ τ -> do
        recurse σ
        recurse τ
      Core.TypeXor σ τ -> do
        recurse σ
        recurse τ
      Core.TypeOr σ τ -> do
        recurse σ
        recurse τ
      Core.TypeTrue -> pure ()
      Core.TypeFalse -> pure ()
    occursPoly ς = case ς of
      Core.MonoType σ -> recurse σ
      Core.TypeForall x π κ ς -> do
        recurse κ
        augmentKindEnvironment p x π κ minBound $ occursPoly ς
        pure ()

kindIsMember :: forall p. p -> TypeUnify -> TypeUnify -> Check p ()
kindIsMember p Core.Top _ = quit $ NotTypable p
kindIsMember p σ κ = do
  κ' <- reconstruct p σ
  matchType p κ κ'

reconstruct :: forall p. p -> TypeUnify -> Check p TypeUnify
reconstruct p = Core.reconstruct indexEnvironment indexGlobalEnvironment indexLogicalMap poly representation multiplicities propositional
  where
    poly (Core.TypeForall {}) = pure $ Core.Type
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
      pure $ foldr (\τ ρ -> Core.TypeAnd τ ρ) Core.TypeTrue πs
    propositional [] = do
      freshTypeVariable p (Core.Kind Core.Propositional)
    propositional (σ : σs) = do
      π <- reconstruct p σ
      for σs $ \σ -> do
        π' <- reconstruct p σ
        matchType p π π'
      pure π

erasureEntail _ Core.Transparent _ = pure ()
erasureEntail p Core.Concrete τ = case τ of
  Core.TypeLogical x ->
    (! x) <$> typeLogicalMap <$> getState >>= \case
      LinkType σ -> erasureEntail p Concrete σ
      UnboundType p' _ κ lev ->
        modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundType p' Concrete κ lev) $ typeLogicalMap state}
  Core.TypeVariable x -> do
    TypeBinding {typeErasure = π} <- (! x) <$> kindEnvironment <$> askEnvironment
    matchErasure p Concrete π
  Core.TypeGlobalVariable x -> do
    TypeBinding {typeErasure = π} <- (! x) <$> kindGlobalEnvironment <$> askEnvironment
    matchErasure p Concrete π
  Core.PointerRepresentation -> pure ()
  Core.StructRepresentation πs -> do
    traverse (erasureEntail p Concrete) πs
    pure ()
  Core.UnionRepresentation πs -> do
    traverse (erasureEntail p Concrete) πs
    pure ()
  Core.WordRepresentation π -> erasureEntail p Concrete π
  Core.Signed -> pure ()
  Core.Unsigned -> pure ()
  Core.Byte -> pure ()
  Core.Short -> pure ()
  Core.Int -> pure ()
  Core.Long -> pure ()
  Core.Native -> pure ()
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
    boolean σ = case σ of
      Core.TypeNot {} -> True
      Core.TypeAnd {} -> True
      Core.TypeOr {} -> True
      Core.TypeXor {} -> True
      _ -> False

    unify :: TypeUnify -> TypeUnify -> Check p ()
    unify (Core.TypeLogical x) (Core.TypeLogical x') | x == x' = pure ()
    unify σ τ | boolean σ || boolean τ = unifyBoolean σ τ
    -- when unifying two variables, the right might not be a solved variable
    -- due to the occurance check
    unify τ@(Core.TypeLogical x) σ@(Core.TypeLogical x') =
      (! x) <$> typeLogicalMap <$> getState >>= \case
        LinkType σ' -> unify σ' σ
        UnboundType _ π κ lev ->
          (! x') <$> typeLogicalMap <$> getState >>= \case
            LinkType σ' -> unify τ σ'
            UnboundType _ _ _ _ -> unifyVariable p x π κ lev σ
    unify (Core.TypeLogical x) σ =
      (! x) <$> typeLogicalMap <$> getState >>= \case
        LinkType σ' -> unify σ' σ
        UnboundType _ π κ lev -> unifyVariable p x π κ lev σ
    unify σ (Core.TypeLogical x) =
      (! x) <$> typeLogicalMap <$> getState >>= \case
        LinkType σ' -> unify σ σ'
        UnboundType _ π κ lev -> unifyVariable p x π κ lev σ
    unify (Core.TypeVariable x) (Core.TypeVariable x') | x == x' = pure ()
    unify (Core.TypeGlobalVariable x) (Core.TypeGlobalVariable x') | x == x' = pure ()
    unify Core.World Core.World = pure ()
    unify Core.TypeTrue Core.TypeTrue = pure ()
    unify Core.TypeFalse Core.TypeFalse = pure ()
    unify (Core.Inline σ π τ) (Core.Inline σ' π' τ') = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (Core.TypeScheme σ ς) (Core.TypeScheme σ' ς') = do
      unify σ σ'
      unifyPoly ς ς'
    unify (Core.FunctionPointer σ π τ) (Core.FunctionPointer σ' π' τ') = do
      zipWithM unify σ σ'
      unify π π'
      unify τ τ'
    unify (Core.FunctionLiteralType σ π τ) (Core.FunctionLiteralType σ' π' τ') = do
      zipWithM unify σ σ'
      unify π π'
      unify τ τ'
    unify (Core.Tuple σs) (Core.Tuple σs') | length σs == length σs' = do
      zipWithM unify σs σs'
      pure ()
    unify (Core.Effect σ π) (Core.Effect σ' π') = do
      unify σ σ'
      unify π π'
    unify (Core.Unique σ) (Core.Unique σ') = do
      unify σ σ'
    unify (Core.Shared σ π) (Core.Shared σ' π') = do
      unify σ σ'
      unify π π'
    unify (Core.Pointer σ) (Core.Pointer σ') = do
      unify σ σ'
    unify (Core.Array σ) (Core.Array σ') = do
      unify σ σ'
    unify (Core.Number ρ1 ρ2) (Core.Number ρ1' ρ2') = do
      unify ρ1 ρ1'
      unify ρ2 ρ2'
    unify Core.Boolean Core.Boolean = pure ()
    unify (Core.Step σ τ) (Core.Step σ' τ') = do
      unify σ σ'
      unify τ τ'
    unify Core.Type Core.Type = pure ()
    unify Core.Region Core.Region = pure ()
    unify (Core.Pretype κ τ) (Core.Pretype κ' τ') = do
      unify κ κ'
      unify τ τ'
    unify (Core.Boxed) (Core.Boxed) = pure ()
    unify (Core.Multiplicity) (Core.Multiplicity) = pure ()
    unify (Core.PointerRepresentation) (Core.PointerRepresentation) = pure ()
    unify (Core.StructRepresentation κs) (Core.StructRepresentation κs') | length κs == length κs' = do
      zipWithM unify κs κs'
      pure ()
    unify (Core.UnionRepresentation κs) (Core.UnionRepresentation κs') | length κs == length κs' = do
      zipWithM unify κs κs'
      pure ()
    unify (Core.WordRepresentation κ) (Core.WordRepresentation κ') = unify κ κ'
    unify Core.Byte Core.Byte = pure ()
    unify Core.Short Core.Short = pure ()
    unify Core.Int Core.Int = pure ()
    unify Core.Long Core.Long = pure ()
    unify Core.Native Core.Native = pure ()
    unify Core.Signed Core.Signed = pure ()
    unify Core.Unsigned Core.Unsigned = pure ()
    unify Core.Representation Core.Representation = pure ()
    unify Core.Size Core.Size = pure ()
    unify Core.Signedness Core.Signedness = pure ()
    unify (Core.Kind σ) (Core.Kind σ') = do
      unify σ σ'
    unify Core.Syntactic Core.Syntactic = pure ()
    unify Core.Propositional Core.Propositional = pure ()
    unify Core.Unification Core.Unification = pure ()
    unify Core.AmbiguousLabel Core.AmbiguousLabel = pure ()
    unify Core.Label Core.Label = pure ()
    unify Core.Top Core.Top = pure ()
    unify σ σ' = quit $ TypeMismatch p σ σ'

    unifyBoolean σ τ = do
      κ <- reconstruct p σ
      κ' <- reconstruct p τ
      matchType p κ κ'
      modifyState $ \state -> state {booleans = (σ, τ) : booleans state}
    unifyPoly
      (Core.TypeForall α π κ ς)
      (Core.TypeForall α' π' κ' ς') = do
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
        booleanConstantElimination αf
        pure ()
    unifyPoly
      (Core.MonoType σ)
      (Core.MonoType σ') =
        matchType p σ σ'
    unifyPoly ς ς' = quit $ TypePolyMismatch p ς ς'

matchErasure _ Core.Transparent Core.Transparent = pure ()
matchErasure _ Core.Concrete Core.Concrete = pure ()
matchErasure p π π' = quit $ ErasureMismatch p π π'

matchInstanciation _ [] [] = pure ()
matchInstanciation p (σ : θ) (σ' : θ') = do
  matchType p σ σ'
  matchInstanciation p θ θ'
matchInstanciation p _ _ = quit $ InstantiationLengthMismatch p

freshTypeVariable p κ = Core.TypeLogical <$> (levelCounter <$> getState >>= freshTypeVariableRaw p Transparent κ)

freshRepresentationKindVariable p = freshTypeVariable p Core.Representation

freshSizeKindVariable p = freshTypeVariable p Core.Size

freshSignednessKindVariable p = freshTypeVariable p Core.Signedness

freshOrderabilityVariable p = freshTypeVariable p Core.Unification

freshMetaTypeVariable p = do
  freshTypeVariable p Core.Type

freshMultiplicityKindVariable p = do
  freshTypeVariable p Core.Multiplicity

freshPretypeTypeVariable p = do
  s <- freshRepresentationKindVariable p
  τ <- freshMultiplicityKindVariable p
  freshTypeVariable p (Core.Pretype s τ)

freshBoxedTypeVariable p = do
  freshTypeVariable p Core.Boxed

freshRegionTypeVariable p = do
  freshTypeVariable p Core.Region

freshLabelTypeVariable p = do
  freshTypeVariable p Core.Label

checkKind _ (Core.Kind σ) = pure (σ)
checkKind p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkKind p σ
    UnboundType _ π κ l -> do
      ρ <- freshOrderabilityVariable p
      unifyVariable p x π κ l (Core.Kind ρ)
      pure ρ
checkKind p σ = quit $ ExpectedKind p σ

checkRepresentation _ Core.Representation = pure ()
checkRepresentation p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkRepresentation p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l Core.Representation
      pure ()
checkRepresentation p σ = quit $ ExpectedRepresentation p σ

checkMultiplicity _ Core.Multiplicity = pure ()
checkMultiplicity p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkMultiplicity p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l Core.Multiplicity
      pure ()
checkMultiplicity p σ = quit $ ExpectedMultiplicity p σ

checkSize _ Core.Size = pure ()
checkSize p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkSize p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l Core.Size
      pure ()
checkSize p σ = quit $ ExpectedSize p σ

checkSignedness _ Core.Signedness = pure ()
checkSignedness p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkSignedness p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l Core.Signedness
      pure ()
checkSignedness p σ = quit $ ExpectedSignedness p σ

checkType _ Core.Type = pure ()
checkType p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkType p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l Core.Type
      pure ()
checkType p σ = quit $ ExpectedType p σ

checkPretype _ (Core.Pretype σ τ) = pure (σ, τ)
checkPretype p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkPretype p σ
    UnboundType _ π κ l -> do
      σ <- freshRepresentationKindVariable p
      τ <- freshMultiplicityKindVariable p
      unifyVariable p x π κ l (Core.Pretype σ τ)
      pure (κ, τ)
checkPretype p σ = quit $ ExpectedPretype p σ

checkBoxed _ Core.Boxed = pure ()
checkBoxed p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkBoxed p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l Core.Boxed
      pure ()
checkBoxed p σ = quit $ ExpectedBoxed p σ

checkRegion _ Core.Region = pure ()
checkRegion p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkRegion p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l Core.Region
      pure ()
checkRegion p σ = quit $ ExpectedRegion p σ

checkPropoitional _ Core.Propositional = pure ()
checkPropoitional p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkPropoitional p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l Core.Propositional
      pure ()
checkPropoitional p σ = quit $ ExpectedPropositional p σ

checkUnification _ Core.Unification = pure ()
checkUnification p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkUnification p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l Core.Unification
      pure ()
checkUnification p σ = quit $ ExpectedUnification p σ

checkInline _ (Core.Inline σ τ π) = pure (σ, τ, π)
checkInline p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkInline p σ
    UnboundType _ π' κ l -> do
      σ <- freshMetaTypeVariable p
      π <- freshMultiplicityKindVariable p
      τ <- freshMetaTypeVariable p
      unifyVariable p x π' κ l (Core.Inline σ π τ)
      pure (σ, π, τ)
checkInline p σ = quit $ ExpectedInline p σ

checkFunctionPointer _ n (Core.FunctionPointer σ τ π) | length σ == n = pure (σ, τ, π)
checkFunctionPointer p n (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkFunctionPointer p n σ
    UnboundType _ π' κ l -> do
      σs <- replicateM n (freshPretypeTypeVariable p)
      π <- freshRegionTypeVariable p
      τ <- freshPretypeTypeVariable p
      unifyVariable p x π' κ l (Core.FunctionPointer σs π τ)
      pure (σs, π, τ)
checkFunctionPointer p n σ = quit $ ExpectedFunctionPointer p n σ

checkFunctionLiteralType _ n (Core.FunctionLiteralType σ τ π) | length σ == n = pure (σ, τ, π)
checkFunctionLiteralType p n (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkFunctionLiteralType p n σ
    UnboundType _ π' κ l -> do
      σs <- replicateM n (freshPretypeTypeVariable p)
      π <- freshRegionTypeVariable p
      τ <- freshPretypeTypeVariable p
      unifyVariable p x π' κ l (Core.FunctionLiteralType σs π τ)
      pure (σs, π, τ)
checkFunctionLiteralType p n σ = quit $ ExpectedFunctionLiteralType p n σ

checkUnique _ (Core.Unique σ) = pure σ
checkUnique p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkUnique p σ
    UnboundType _ π κ l -> do
      σ <- freshBoxedTypeVariable p
      unifyVariable p x π κ l (Core.Unique σ)
      pure σ
checkUnique p σ = quit $ ExpectedUnique p σ

checkPointer _ (Core.Pointer σ) = pure σ
checkPointer p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkPointer p σ
    UnboundType _ π κ l -> do
      σ <- freshPretypeTypeVariable p
      unifyVariable p x π κ l (Core.Pointer σ)
      pure (σ)
checkPointer p σ = quit $ ExpectedPointer p σ

checkArray _ (Core.Array σ) = pure σ
checkArray p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkArray p σ
    UnboundType _ π κ l -> do
      σ <- freshPretypeTypeVariable p
      unifyVariable p x π κ l (Core.Array σ)
      pure (σ)
checkArray p σ = quit $ ExpectedArray p σ

checkEffect _ (Core.Effect σ τ) = pure (σ, τ)
checkEffect p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkEffect p σ
    UnboundType _ π' κ l -> do
      σ <- freshPretypeTypeVariable p
      π <- freshRegionTypeVariable p
      unifyVariable p x π' κ l (Core.Effect σ π)
      pure (σ, π)
checkEffect p σ = quit $ ExpectedEffect p σ

checkShared _ (Core.Shared σ τ) = pure (σ, τ)
checkShared p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkShared p σ
    UnboundType _ π' κ l -> do
      σ <- freshBoxedTypeVariable p
      π <- freshRegionTypeVariable p
      unifyVariable p x π' κ l (Core.Shared σ π)
      pure (σ, π)
checkShared p σ = quit $ ExpectedShared p σ

checkNumber _ (Core.Number σ τ) = pure (σ, τ)
checkNumber p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkNumber p σ
    UnboundType _ π κ l -> do
      ρ1 <- freshSignednessKindVariable p
      ρ2 <- freshSizeKindVariable p
      unifyVariable p x π κ l (Core.Number ρ1 ρ2)
      pure (ρ1, ρ2)
checkNumber p σ = quit $ ExpectedNumber p σ

checkBoolean _ Core.Boolean = pure ()
checkBoolean p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkBoolean p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l Core.Boolean
      pure ()
checkBoolean p σ = quit $ ExpectedBoolean p σ

checkStep _ (Core.Step σ τ) = pure (σ, τ)
checkStep p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkStep p σ
    UnboundType _ π κ l -> do
      σ <- freshPretypeTypeVariable p
      τ <- freshPretypeTypeVariable p
      unifyVariable p x π κ l (Core.Step σ τ)
      pure (σ, τ)
checkStep p σ = quit $ ExpectedStep p σ

checkLabel _ Core.Label = pure ()
checkLabel p (Core.TypeLogical x) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkLabel p σ
    UnboundType _ π κ l -> do
      unifyVariable p x π κ l Core.Label
      pure ()
checkLabel p σ = quit $ ExpectedLabel p σ

data Mode = InlineMode | SymbolMode

augmentVariableLinear p x l ς check = do
  Checked e σ lΓ <- augmentTypeEnvironment x p l ς check
  case count x lΓ of
    Single -> pure ()
    _ -> matchType p l Core.TypeTrue
  pure $ Checked e σ (Remove x lΓ)

capture p base lΓ = do
  let captures = variablesUsed lΓ
  for (Set.toList captures) $ \x -> do
    (TermBinding _ l _) <- fromJust <$> Map.lookup x <$> typeEnvironment <$> askEnvironment
    matchType p l (Core.TypeOr base l)
    pure ()
  pure ()

requireUnrestricted p σ = do
  κ <- reconstruct p σ
  (_, l) <- checkPretype p κ
  matchType p l Core.TypeTrue
  pure ()

-- todo relabel seems somewhat fragile here
-- this depends on `KindChecked σ _ _ <- kindCheck τ`, never having unification variables in σ
-- because relabel ignores unification variables
augmentTermMetaPattern (Core.InlineMatchVariable p x π σ) =
  augmentVariableLinear p x π (relabel (Core.MonoType σ))

nullEffect σ = Core.MonoType $ Core.Effect σ Core.TypeFalse

augmentTermPattern = \case
  Core.MatchVariable p x σ -> \e -> do
    κ <- reconstruct p σ
    (_, l) <- checkPretype p κ
    augmentVariableLinear p x l (Core.MonoLabel (nullEffect σ)) e
  Core.MatchTuple _ pms -> augmentTermPatterns pms
  Core.MatchBoolean _ _ -> id

augmentTermPatterns pms = foldr (.) id (map augmentTermPattern pms)

checkSolid p σ = do
  (ρ, _) <- checkPretype p =<< reconstruct p σ
  erasureEntail p Concrete ρ

typeCheckMetaPattern :: Surface.TermMetaPattern p -> Check p (TermMetaPatternUnify p, TypeUnify, TypeUnify)
typeCheckMetaPattern = \case
  (Surface.InlineMatchVariable p x π σ) -> do
    π <- case π of
      Surface.Hole p -> freshMultiplicityKindVariable p
      π -> do
        (π, ()) <- secondM (checkMultiplicity p) =<< kindCheck π
        pure (flexible π)
    σ <- case σ of
      Surface.Hole p -> freshMetaTypeVariable p
      σ -> do
        (σ, ()) <- secondM (checkType p) =<< kindCheck σ
        pure (flexible σ)
    pure (Core.InlineMatchVariable p x π σ, π, σ)

typeCheckRuntimePattern = \case
  (Surface.MatchVariable p x σ) -> do
    σ' <- case σ of
      Surface.Hole p -> freshPretypeTypeVariable p
      σ -> do
        (σ', _) <- traverse (checkPretype p) =<< kindCheck σ
        pure (flexible σ')
    checkSolid p σ'
    pure (Core.MatchVariable p x σ', σ')
  (Surface.MatchTuple p pms) -> do
    (pms, σs) <- unzip <$> traverse typeCheckRuntimePattern pms
    pure (Core.MatchTuple p pms, Core.Tuple σs)
  (Surface.MatchBoolean p b) -> do
    pure (Core.MatchBoolean p b, Core.Boolean)

kindCheckScheme :: Mode -> Surface.TypeScheme p -> Check p (TypeSchemeInfer, TypeUnify)
kindCheckScheme mode =
  \case
    Surface.MonoType σ -> do
      (σ', _) <- secondM (checkType (Surface.position σ)) =<< kindCheck σ
      pure (Core.MonoType σ', Core.Type)
    Surface.TypeForall pm σ -> do
      pm'@(TypePatternIntermediate _ x er κ) <- kindCheckPattern mode pm
      augmentTypePatternLevel pm' $ do
        (σ', _) <- kindCheckScheme mode σ
        pure $ (Core.TypeForall x er κ σ', Core.Type)

kindCheckPattern :: Mode -> Surface.TypePattern p -> Check p (TypePatternIntermediate p)
kindCheckPattern mode (Surface.TypePattern p x π κ) = do
  (κ, _) <- secondM (checkKind p) =<< kindCheck κ
  case mode of
    SymbolMode -> matchErasure p π Transparent
    InlineMode -> pure ()
  pure (TypePatternIntermediate p x π κ)

kindCheck :: Surface.Type p -> Check p (TypeInfer, TypeUnify)
kindCheck = \case
  Surface.Hole p -> quit $ NotTypable p
  Surface.TypeScheme _ λ -> do
    (ς, κ) <- kindCheckScheme InlineMode λ
    pure (Core.TypeScheme (Core.AmbiguousLabel) ς, κ)
  Surface.TypeVariable p x -> do
    Map.lookup x <$> kindEnvironment <$> askEnvironment >>= \case
      Just (TypeBinding _ _ κ _) -> pure (Core.TypeVariable x, κ)
      Nothing -> do
        heading <- moduleScope <$> askEnvironment
        kindCheck (Surface.TypeGlobalVariable p $ globalType heading x)
  Surface.TypeGlobalVariable p x -> do
    Map.lookup x <$> kindGlobalEnvironment <$> askEnvironment >>= \case
      Just (TypeBinding _ _ κ _) -> pure (Core.TypeGlobalVariable x, κ)
      Nothing ->
        Map.lookup x <$> typeGlobalSynonyms <$> askEnvironment >>= \case
          Just σ -> do
            κ <- reconstruct p (flexible σ)
            pure (flexible σ, κ)
          Nothing -> quit $ UnknownTypeGlobalIdentifier p x
  Surface.Inline p σ π τ -> do
    (σ', _) <- secondM (checkType p) =<< kindCheck σ
    (π', _) <- secondM (checkMultiplicity p) =<< kindCheck π
    (τ', _) <- secondM (checkType p) =<< kindCheck τ
    pure (Core.Inline σ' π' τ', Core.Type)
  Surface.FunctionPointer p σ π τ -> do
    (σ', _) <- unzip <$> traverse (secondM (checkPretype p) <=< kindCheck) σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (Core.FunctionPointer σ' π' τ', Core.Pretype Core.PointerRepresentation Core.TypeTrue)
  Surface.FunctionLiteralType p σ π τ -> do
    (σ', _) <- unzip <$> traverse (secondM (checkPretype p) <=< kindCheck) σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (Core.FunctionLiteralType σ' π' τ', Core.Type)
  Surface.Tuple p σs -> do
    (σs, (ρs, τs)) <- second unzip <$> unzip <$> traverse (secondM (checkPretype p) <=< kindCheck) σs
    let τ = foldr Core.TypeAnd Core.TypeTrue τs
    pure (Core.Tuple σs, Core.Pretype (Core.StructRepresentation ρs) τ)
  Surface.Step p σ τ -> do
    (σ, (κ, _)) <- secondM (checkPretype p) =<< kindCheck σ
    (τ, (ρ, _)) <- secondM (checkPretype p) =<< kindCheck τ
    let union = Core.UnionRepresentation $ [κ, ρ]
    let wrap = Core.StructRepresentation [Core.WordRepresentation Core.Byte, union]
    pure (Core.Step σ τ, Core.Pretype wrap Core.TypeFalse)
  Surface.Effect p σ π -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    pure (Core.Effect σ' π', Core.Type)
  Surface.Unique p σ -> do
    (σ', _) <- secondM (checkBoxed p) =<< kindCheck σ
    pure (Core.Unique σ', Core.Pretype Core.PointerRepresentation Core.TypeFalse)
  Surface.Shared p σ π -> do
    (σ', _) <- secondM (checkBoxed p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    pure (Core.Shared σ' π', Core.Pretype Core.PointerRepresentation Core.TypeTrue)
  Surface.Pointer p σ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    pure (Core.Pointer σ', Core.Boxed)
  Surface.Array p σ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    pure (Core.Array σ', Core.Boxed)
  Surface.Number p ρ1 ρ2 -> do
    (ρ1', _) <- secondM (checkSignedness p) =<< kindCheck ρ1
    (ρ2', _) <- secondM (checkSize p) =<< kindCheck ρ2
    pure (Core.Number ρ1' ρ2', Core.Pretype (Core.WordRepresentation (flexible ρ2')) Core.TypeTrue)
  Surface.Boolean _ -> do
    pure (Core.Boolean, Core.Pretype (Core.WordRepresentation Core.Byte) Core.TypeTrue)
  Surface.World _ -> do
    pure (Core.World, Core.Region)
  Surface.Type _ -> do
    pure (Core.Type, Core.Kind Core.Syntactic)
  Surface.Region _ -> pure (Core.Region, Core.Kind Core.Propositional)
  Surface.PointerRepresentation _ -> pure (Core.PointerRepresentation, Core.Representation)
  Surface.StructRepresentation p κs -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< kindCheck) κs
    pure (Core.StructRepresentation κs', Core.Representation)
  Surface.UnionRepresentation p κs -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< kindCheck) κs
    pure (Core.UnionRepresentation κs', Core.Representation)
  Surface.WordRepresentation p κ -> do
    (κ', _) <- secondM (checkSize p) =<< kindCheck κ
    pure (Core.WordRepresentation κ', Core.Representation)
  Surface.Byte _ -> pure (Core.Byte, Core.Size)
  Surface.Short _ -> pure (Core.Short, Core.Size)
  Surface.Int _ -> pure (Core.Int, Core.Size)
  Surface.Long _ -> pure (Core.Long, Core.Size)
  Surface.Native _ -> pure (Core.Native, Core.Size)
  Surface.Signed _ -> pure (Core.Signed, Core.Signedness)
  Surface.Unsigned _ -> pure (Core.Unsigned, Core.Signedness)
  Surface.Pretype p κ τ -> do
    (κ', _) <- secondM (checkRepresentation p) =<< kindCheck κ
    (τ', _) <- secondM (checkMultiplicity p) =<< kindCheck τ
    pure (Core.Pretype κ' τ', Core.Kind Core.Syntactic)
  Surface.Boxed _ -> do
    pure (Core.Boxed, Core.Kind Core.Syntactic)
  Surface.Multiplicity _ -> do
    pure (Core.Multiplicity, Core.Kind Core.Propositional)
  Surface.Representation _ -> pure (Core.Representation, Core.Kind Core.Syntactic)
  Surface.Size _ -> pure (Core.Size, Core.Kind Core.Syntactic)
  Surface.Signedness _ -> pure (Core.Signedness, Core.Kind Core.Syntactic)
  Surface.Kind p ρ -> do
    (ρ, _) <- secondM (checkUnification p) =<< kindCheck ρ
    pure (Core.Kind ρ, Core.Top)
  Surface.Syntactic _ -> do
    pure (Core.Syntactic, Core.Unification)
  Surface.Propositional _ -> do
    pure (Core.Propositional, Core.Unification)
  Surface.Unification _ -> do
    pure (Core.Unification, Core.Top)
  Surface.AmbiguousLabel _ -> do
    pure (Core.AmbiguousLabel, Core.Label)
  Surface.Label _ -> do
    pure (Core.Label, Core.Top)
  Surface.TypeTrue p -> do
    π <- freshTypeVariable p (Core.Kind Core.Propositional)
    pure (Core.TypeTrue, π)
  Surface.TypeFalse p -> do
    π <- freshTypeVariable p (Core.Kind Core.Propositional)
    pure (Core.TypeFalse, π)
  Surface.TypeXor p σ τ -> do
    (σ', κ) <- kindCheck σ
    (τ', κ') <- kindCheck τ
    matchType p κ κ'
    ρ <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (Core.TypeXor σ' τ', κ)
  Surface.TypeOr p σ τ -> do
    (σ', κ) <- kindCheck σ
    (τ', κ') <- kindCheck τ
    matchType p κ κ'
    ρ <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (Core.TypeOr σ' τ', κ)
  Surface.TypeAnd p σ τ -> do
    (σ', κ) <- kindCheck σ
    (τ', κ') <- kindCheck τ
    matchType p κ κ'
    ρ <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (Core.TypeAnd σ' τ', κ)
  Surface.TypeNot p σ -> do
    (σ', κ) <- kindCheck σ
    ρ <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (Core.TypeNot σ', κ)
  Surface.Top p -> quit $ NotTypable p

instantiate p ς = case ς of
  Core.MonoType σ -> pure (σ, [])
  Core.TypeForall x π κ σ -> do
    τ <- freshTypeVariable p κ
    erasureEntail p π τ
    (ς, θ) <- instantiate p $ substituteType τ x σ
    pure (ς, τ : θ)

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

regions [] = Core.TypeFalse
regions σs = foldl1 Core.TypeOr σs

validateInstantation p θ θ' = do
  θ' <- for θ' $ \σ -> do
    (τ, _) <- kindCheck σ
    let ς = relabel $ Core.MonoType $ flexible τ
    (σ, _) <- instantiateLabel instantiate p ς
    pure σ
  matchInstanciation p θ θ'

typeCheck :: forall p. Surface.Term p -> Check p (Checked p TypeUnify)
typeCheck = \case
  Surface.Variable p x θ' -> do
    mσ <- Map.lookup x <$> typeEnvironment <$> askEnvironment
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiateLabel instantiate p σ
        case θ' of
          Surface.InstantiationInfer -> pure ()
          Surface.Instantiation θ' -> validateInstantation p θ θ'
        pure $ Checked (Core.Variable p x θ) τ (Use x)
      Nothing -> do
        heading <- moduleScope <$> askEnvironment
        typeCheck (Surface.GlobalVariable p (globalTerm heading x) θ')
  Surface.GlobalVariable p x θ' -> do
    mσ <- Map.lookup x <$> typeGlobalEnvironment <$> askEnvironment
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiateLabel instantiate p σ
        case θ' of
          Surface.InstantiationInfer -> pure ()
          Surface.Instantiation θ' -> validateInstantation p θ θ'
        -- todo useNothing here is kinda of a hack
        pure $ Checked (Core.GlobalVariable p x θ) τ useNothing
      Nothing -> quit $ UnknownGlobalIdentifier p x
  Surface.InlineAbstraction p pm e -> do
    (pm', π, σ) <- typeCheckMetaPattern pm
    Checked e' τ lΓ <- augmentTermMetaPattern pm' (typeCheck e)
    pure $ Checked (Core.InlineAbstraction p pm' e') (Core.Inline σ π τ) lΓ
  Surface.InlineApplication p e1 e2 -> do
    Checked e1' (σ, π, τ) lΓ1 <- traverse (checkInline p) =<< typeCheck e1
    Checked e2' σ' lΓ2 <- typeCheck e2
    matchType p σ σ'
    capture p π lΓ2
    pure $ Checked (Core.InlineApplication p e1' e2') τ (lΓ1 `combine` lΓ2)
  Surface.InlineLet p pm e1 e2 -> do
    Checked e1' τ lΓ1 <- typeCheck e1
    (pm', π, τ') <- typeCheckMetaPattern pm
    matchType p τ τ'
    Checked e2' σ lΓ2 <- augmentTermMetaPattern pm' $ typeCheck e2
    capture p π lΓ1
    pure $ Checked (Core.InlineLet p pm' e1' e2') σ (lΓ1 `combine` lΓ2)
  Surface.PolyIntroduction p λ -> do
    CheckedScheme eς σ lΓ <- typeCheckScheme InlineMode λ
    τ <- freshLabelTypeVariable p
    vars <- typeLogicalMap <$> getState
    let σ' = zonk vars σ
    pure $ Checked (Core.PolyIntroduction p eς) (Core.TypeScheme τ σ') lΓ
  Surface.PolyElimination p e θ' -> do
    Checked e ς lΓ <- leveled $ typeCheck e
    elimatePoly e ς lΓ
    where
      elimatePoly e (Core.TypeScheme l ς) lΓ = do
        validateLevel l
        (σ, θ) <- instantiate p ς
        case θ' of
          Surface.InstantiationInfer -> pure ()
          Surface.Instantiation θ' -> validateInstantation p θ θ'
        pure $ Checked (Core.PolyElimination p e θ) σ lΓ
      elimatePoly e (Core.TypeLogical v) lΓ =
        (! v) <$> typeLogicalMap <$> getState >>= \case
          LinkType σ -> elimatePoly e σ lΓ
          _ -> quit $ ExpectedTypeAnnotation p
      elimatePoly _ _ _ = quit $ ExpectedTypeAnnotation p
      validateLevel (Core.TypeLogical v) =
        (! v) <$> typeLogicalMap <$> getState >>= \case
          LinkType σ -> validateLevel σ
          UnboundType p _ _ level' -> do
            level <- levelCounter <$> getState
            if level >= level'
              then quit $ ExpectedTypeAnnotation p
              else pure ()
      validateLevel _ = quit $ ExpectedTypeAnnotation p
  Surface.Let p pm e1 e2 -> do
    (pm', τ) <- typeCheckRuntimePattern pm
    Checked e1' (τ', π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p τ τ'
    Checked e2' (σ, π2) lΓ2 <- traverse (checkEffect p) =<< augmentTermPattern pm' (typeCheck e2)
    let π = regions [π1, π2]
    pure $ Checked (Core.Let p pm' e1' e2') (Core.Effect σ π) (lΓ1 `combine` lΓ2)
  Surface.Case p e λs -> do
    Checked e (τ, π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e
    σ <- freshPretypeTypeVariable p
    checkSolid p σ
    (e2, pm, πs, lΓ2) <- fmap unzip4 $
      for λs $ \(pm, e2) -> do
        (pm, τ') <- typeCheckRuntimePattern pm
        matchType p τ τ'
        Checked e2 (σ', π) lΓ2 <- traverse (checkEffect p) =<< augmentTermPattern pm (typeCheck e2)
        matchType p σ σ'
        pure (e2, pm, π, lΓ2)
    let π = regions $ π1 : πs
    pure $
      Checked
        (Core.Case p e τ (zip pm e2) σ)
        (Core.Effect σ π)
        (lΓ1 `combine` branchAll lΓ2)
  Surface.Extern p n sym -> do
    σs <- replicateM n $ do
      σ <- freshPretypeTypeVariable p
      checkSolid p σ
      pure σ
    π <- freshRegionTypeVariable p
    τ <- freshPretypeTypeVariable p
    checkSolid p τ
    pure $
      Checked
        (Core.Extern p sym σs π τ)
        (Core.Effect (Core.FunctionPointer σs π τ) Core.TypeFalse)
        useNothing
  Surface.Application p e1 e2s -> do
    Checked e1' ((σs, π2, τ), π1) lΓ1 <- traverse (firstM (checkFunctionPointer p (length e2s)) <=< checkEffect p) =<< typeCheck e1
    (e2s', σs', π3s, lΓ2s) <- fmap unzip4 $
      for e2s $ \e2 -> do
        Checked e2' (σ', π3) lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
        pure (e2', σ', π3, lΓ2)
    zipWithM (matchType p) σs σs'
    checkSolid p τ
    let π = regions $ [π1, π2] ++ π3s
    pure $
      Checked
        (Core.Application p e1' (zip e2s' σs'))
        (Core.Effect τ π)
        (lΓ1 `combine` combineAll lΓ2s)
  Surface.TupleLiteral p es -> do
    checked <- traverse (traverse (checkEffect p) <=< typeCheck) es
    let (es, σs, πs, lΓs) = unzip4 $ map (\(Checked es (σ, π) lΓ) -> (es, σ, π, lΓ)) checked
    let π = regions πs
    pure $
      Checked
        (Core.TupleLiteral p es)
        (Core.Effect (Core.Tuple σs) π)
        (combineAll lΓs)
  Surface.Read p e -> do
    Checked e' ((σ, π2), π1) lΓ <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck e
    let π = regions [π1, π2]
    requireUnrestricted p σ
    checkSolid p σ
    pure $ Checked (Core.Read p e') (Core.Effect σ π) lΓ
  Surface.Write p ep ev -> do
    Checked ep ((σ, π2), π1) lΓ1 <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
    Checked ev (σ', π3) lΓ2 <- traverse (checkEffect p) =<< typeCheck ev
    matchType p σ σ'
    checkSolid p σ
    let π = regions [π1, π2, π3]
    requireUnrestricted p σ
    pure $
      Checked
        (Core.Write p ep ev σ)
        (Core.Effect (Core.Tuple []) π)
        (lΓ1 `combine` lΓ2)
  Surface.NumberLiteral p v -> do
    ρ1 <- freshSignednessKindVariable p
    ρ2 <- freshSizeKindVariable p
    erasureEntail p Concrete ρ2
    pure $
      Checked
        (Core.NumberLiteral p v (Core.Number ρ1 ρ2))
        (Core.Effect (Core.Number ρ1 ρ2) Core.TypeFalse)
        useNothing
  Surface.Arithmatic p o e1 e2 -> do
    Checked e1' ((ρ1, ρ2), π1) lΓ1 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' ((ρ1', ρ2'), π2) lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e2
    matchType p ρ1 ρ1'
    matchType p ρ2 ρ2'
    erasureEntail p Concrete ρ1
    erasureEntail p Concrete ρ2
    let π = regions [π1, π2]
    pure $
      Checked
        (Core.Arithmatic p o e1' e2' ρ1)
        (Core.Effect (Core.Number ρ1 ρ2) π)
        (lΓ1 `combine` lΓ2)
  Surface.Relational p o e1 e2 -> do
    Checked e1' ((ρ1, ρ2), π1) lΓ1 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' ((ρ1', ρ2'), π2) lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e2
    matchType p ρ1 ρ1'
    matchType p ρ2 ρ2'
    erasureEntail p Concrete ρ1
    erasureEntail p Concrete ρ2
    let π = regions [π1, π2]
    pure $
      Checked
        (Core.Relational p o e1' e2' (Core.Number ρ1 ρ2) ρ1)
        (Core.Effect (Core.Boolean) π)
        (lΓ1 `combine` lΓ2)
  Surface.Resize p e -> do
    ρ1 <- freshSignednessKindVariable p
    ρ2 <- freshSizeKindVariable p
    Checked e ((ρ1', ρ2'), π) lΓ <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e
    matchType p ρ1 ρ1'
    matchType p ρ2 ρ2'

    ρ3 <- freshSignednessKindVariable p
    ρ4 <- freshSizeKindVariable p
    erasureEntail p Concrete ρ4

    pure $ Checked (Core.Resize p e (Core.Number ρ1 ρ2) (Core.Number ρ3 ρ4)) (Core.Effect (Core.Number ρ3 ρ4) π) lΓ
  Surface.FunctionLiteral p pms τ' π' e -> do
    (pms', σs) <- unzip <$> traverse typeCheckRuntimePattern pms
    Checked e' (τ, π) lΓ <- traverse (checkEffect p) =<< augmentTermPatterns pms' (typeCheck e)
    case τ' of
      Surface.Hole _ -> pure ()
      τ' -> do
        (τ', _) <- kindCheck τ'
        matchType p τ (flexible τ')
    case π' of
      Surface.Hole _ -> pure ()
      π' -> do
        (π', _) <- kindCheck π'
        matchType p π (flexible π')
    pure $ Checked (Core.FunctionLiteral p pms' τ π e') (Core.FunctionLiteralType σs π τ) lΓ
  Surface.TypeAnnotation p e τ -> do
    Checked e σ lΓ <- typeCheck e
    (τ, _) <- kindCheck τ
    let ς = relabel $ Core.MonoType $ flexible τ
    (σ', _) <- instantiateLabel instantiate p ς
    (σ'', _) <- instantiateLabel instantiate p ς
    matchType p σ σ'
    pure $ Checked e σ'' lΓ
  Surface.PretypeAnnotation p e σ' -> do
    Checked e τ lΓ <- typeCheck e
    (σ, _) <- checkEffect p τ
    σ' <- flexible <$> fst <$> kindCheck σ'
    matchType p σ σ'
    pure $ Checked e τ lΓ
  Surface.BooleanLiteral p b -> do
    pure $ Checked (Core.BooleanLiteral p b) (Core.Effect Core.Boolean Core.TypeFalse) useNothing
  Surface.If p eb et ef -> do
    Checked eb' ((), π1) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck eb
    Checked et' (σ, π2) lΓ2 <- traverse (checkEffect p) =<< typeCheck et
    Checked ef' (σ', π3) lΓ3 <- traverse (checkEffect p) =<< typeCheck ef
    matchType p σ σ'
    let π = regions [π1, π2, π3]
    pure $
      Checked
        (Core.If p eb' et' ef')
        (Core.Effect σ π)
        (lΓ1 `combine` (lΓ2 `branch` lΓ3))
  Surface.PointerAddition p ep ei -> do
    Checked ep' ((σ, π2), π1) lΓ1 <- traverse (firstM (firstM (checkArray p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
    Checked ei' ((κ1, κ2), π3) lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck ei
    matchType p κ1 (Core.Unsigned)
    matchType p κ2 (Core.Native)
    checkSolid p σ
    let π = regions [π1, π3]
    pure $
      Checked
        (Core.PointerAddition p ep' ei' σ)
        (Core.Effect (Core.Shared (Core.Array σ) π2) π)
        (lΓ1 `combine` lΓ2)
  Surface.Continue p e -> do
    Checked e (σ, π) lΓ <- traverse (checkEffect p) =<< typeCheck e
    τ <- freshPretypeTypeVariable p
    checkSolid p τ
    let ρ = Core.Step τ σ
    pure $ Checked (Core.Continue p e ρ) (Core.Effect ρ π) lΓ
  Surface.Break p e -> do
    Checked e (τ, π) lΓ <- traverse (checkEffect p) =<< typeCheck e
    σ <- freshPretypeTypeVariable p
    checkSolid p σ
    let ρ = Core.Step τ σ
    pure $ Checked (Core.Break p e ρ) (Core.Effect ρ π) lΓ
  Surface.Loop p pm e1 e2 -> do
    (pm, σ) <- typeCheckRuntimePattern pm
    Checked e1 (σ', π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p σ σ'
    Checked e2 ((τ, σ''), π2) lΓ2 <- traverse (firstM (checkStep p) <=< checkEffect p) =<< augmentTermPattern pm (typeCheck e2)
    matchType p σ σ''
    capture p Core.TypeTrue lΓ2
    let π = regions [π1, π2]
    pure $ Checked (Core.Loop p pm e1 e2) (Core.Effect τ π) (combine lΓ1 lΓ2)
  Surface.Isolate p e -> do
    Checked e ((σ, π2), π) lΓ <- traverse (firstM (firstM (checkArray p) <=< checkShared p) <=< checkEffect p) =<< typeCheck e
    pure $
      Checked
        (Core.Isolate p e)
        (Core.Effect (Core.Shared (Core.Pointer σ) π2) π)
        lΓ
  Surface.Not p e -> do
    Checked e' ((), π) lΓ <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    pure $ Checked (Core.Not p e') (Core.Effect Core.Boolean π) lΓ
  Surface.And p e ey -> do
    Checked e' ((), π1) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked ey' ((), π2) lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck ey
    let π = regions [π1, π2]
    pure $ Checked (Core.And p e' ey') (Core.Effect Core.Boolean π) (lΓ1 `combine` (lΓ2 `branch` useNothing))
  Surface.Or p e en -> do
    Checked e' ((), π1) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked en' ((), π2) lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck en
    let π = regions [π1, π2]
    pure $ Checked (Core.Or p e' en') (Core.Effect Core.Boolean π) (lΓ1 `combine` (useNothing `branch` lΓ2))
  Surface.Do p e1 e2 -> do
    Checked e1' (τ, π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p τ (Core.Tuple [])
    Checked e2' (σ, π2) lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
    let π = regions [π1, π2]
    pure $ Checked (Core.Do p e1' e2') (Core.Effect σ π) (lΓ1 `combine` lΓ2)
  Surface.Cast p e -> do
    Checked e (σ, _) lΓ <- traverse (checkEffect p) =<< typeCheck e
    κ <- reconstruct p σ
    (ρ, _) <- checkPretype p κ
    m <- freshMultiplicityKindVariable p
    σ' <- freshTypeVariable p (Core.Pretype ρ m)
    checkSolid p σ'
    π' <- freshRegionTypeVariable p
    let τ = Core.Effect σ' π'
    pure $ Checked (Core.Cast p e τ) τ lΓ

typeCheckScheme :: Mode -> Surface.TermScheme p -> Check p (CheckedScheme p TypeSchemeUnify)
typeCheckScheme mode (Surface.TypeAbstraction pm e) = do
  pm <- kindCheckPattern mode pm

  -- Shadowing type variables is prohibited
  vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
  let αo = intermediateBinder pm
      αn = fresh vars αo
      pm'@(TypePatternIntermediate _ x er κ) = pm {intermediateBinder = αn}
      α = Core.TypeVariable αn

  augmentTypePatternLevel pm' $
    augmentSynonym αo α $ do
      CheckedScheme e' σ' lΓ <- typeCheckScheme mode e
      pure $
        CheckedScheme
          (Core.TypeAbstraction x er (flexible κ) e')
          (Core.TypeForall x er (flexible κ) σ')
          lΓ
typeCheckScheme _ (Surface.MonoTerm e) = do
  Checked e σ lΓ <- typeCheck e
  pure $ CheckedScheme (Core.MonoTerm e) (Core.MonoType σ) lΓ

defaultType p ρ = do
  ρ' <- finish ρ
  case ρ' of
    Core.TypeLogical v -> absurd v
    Core.Representation -> pure $ Core.PointerRepresentation
    Core.Size -> pure $ Core.Int
    Core.Signedness -> pure $ Core.Signed
    Core.Region -> pure $ Core.World
    Core.Multiplicity -> pure Core.TypeTrue
    Core.Label -> pure $ Core.AmbiguousLabel
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
      UnboundType _ _ _ _ -> Core.TypeLogical x
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
    σs -> quit $ TypeBooleanMismatch p $ map (uncurry Core.TypeXor) σs

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
      ρ <- reconstruct p κ
      case ρ of
        _ | level >= level' -> pure False
        Core.Top -> pure False
        Core.Kind _ | InlineMode <- mode -> pure True
        Core.Kind _ | Core.Transparent <- π -> pure True
        Core.Kind _ -> pure False
        σ -> error $ "generalization error " ++ show σ
    LinkType _ -> error "generalization error"

generalizeExact _ [] e = pure e
generalizeExact scope ((n, x) : remaining) e = do
  e <- generalizeExact scope remaining e
  (! x) <$> typeLogicalMap <$> getState >>= \case
    UnboundType _ π κ _ -> do
      ( \f -> do
          modifyState $ \state ->
            state
              { typeLogicalMap = f $ typeLogicalMap state
              }
        )
        $ \σΓ -> Map.insert x (LinkType $ Core.TypeVariable $ TypeIdentifier n) σΓ
      pure (scope n π κ e)
    _ -> error "generalization error"

-- todo refactor this
generalize :: Mode -> (TermUnify p, TypeUnify) -> Check p (TermSchemeUnify p, TypeSchemeUnify)
generalize mode (e, σ) = do
  logical <- typeLogicalMap <$> getState
  vars <- filterM (generalizable mode) $ topologicalBoundsSort logical (unsolvedVariables logical σ)
  used <- usedVars <$> getState
  let names = filter (\x -> x `Set.notMember` used) $ temporaries uppers
  generalizeExact scope (zip names vars) (Core.MonoTerm e, Core.MonoType σ)
  where
    scope n π κ (e, σ) =
      ( Core.TypeAbstraction (TypeIdentifier n) π κ e,
        Core.TypeForall (TypeIdentifier n) π κ σ
      )

typeCheckGlobalAuto ::
  Mode ->
  Surface.Term p ->
  Check p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalAuto mode e = do
  let p = Surface.position e
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
typeCheckGlobalSchemed mode e = do
  let p = Surface.position e
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
typeCheckGlobalNew σ = do
  let p = Surface.position σ
  (σ, κ) <- kindCheck σ
  checkPretype p κ
  κ <- finish κ
  pure (σ, κ)

typeCheckGlobalForward :: Surface.TypeScheme p -> Check p TypeSchemeInfer
typeCheckGlobalForward ς = do
  (ς, _) <- kindCheckScheme SymbolMode ς
  pure ς

typeCheckGlobalNewForward :: Surface.Type p -> Check p TypeInfer
typeCheckGlobalNewForward κ = do
  let p = Surface.position κ
  (κ, _) <- kindCheck κ
  checkPretype p (flexible κ)
  pure κ

convertFunctionLiteral ς = case ς of
  Core.MonoType (Core.FunctionLiteralType σ π τ) -> nullEffect (Core.FunctionPointer σ π τ)
  Core.TypeForall x er κ ς -> Core.TypeForall x er κ $ convertFunctionLiteral ς
  _ -> error "not function literal"

typeCheckModule ::
  [(Path, Surface.Global p)] ->
  StateT
    (CheckEnvironment p)
    (Either (TypeError p))
    [(Path, Core.Global p)]
typeCheckModule [] = pure []
typeCheckModule ((path, item) : nodes) | heading <- directory path = do
  environment <- get
  let run f = lift $ runChecker f environment {moduleScope = heading} emptyState
      p = Surface.position item
      updateTerm ς = modify $ \environment ->
        environment
          { typeGlobalEnvironment =
              Map.insert
                (TermGlobalIdentifier path)
                (TermBinding p Core.TypeTrue (relabel ς))
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
  item <- case item of
    Surface.Macro (Surface.TermAuto e) -> do
      (e, σ) <- run (typeCheckGlobalAuto InlineMode e)
      updateTerm (flexible σ)
      pure $ Core.Macro e
    Surface.Macro (Surface.TermManual e) -> do
      (e, σ) <- run (typeCheckGlobalSchemed InlineMode e)
      updateTerm (flexible σ)
      pure $ Core.Macro e
    Surface.Text (Surface.TermAuto e) -> do
      (e, σ) <- run (typeCheckGlobalAuto SymbolMode e)
      updateTerm (convertFunctionLiteral $ flexible σ)
      pure $ Core.Text e
    Surface.Text (Surface.TermManual e) -> do
      (e, σ) <- run (typeCheckGlobalSchemed SymbolMode e)
      updateTerm (convertFunctionLiteral $ flexible σ)
      pure $ Core.Text e
    Surface.Synonym σ -> do
      σ <- run $ typeCheckGlobalSyn σ
      updateSym σ
      pure $ Core.Synonym σ
    Surface.ForwardText ς -> do
      ς <- run $ typeCheckGlobalForward ς
      updateTerm (convertFunctionLiteral $ flexible ς)
      pure $ Core.ForwardText ς
    Surface.ForwardNewType κ -> do
      κ <- run $ typeCheckGlobalNewForward κ
      updateNewType' (flexible κ)
      pure $ Core.ForwardNewType κ

  ((path, item) :) <$> typeCheckModule nodes
