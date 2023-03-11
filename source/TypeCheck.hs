module TypeCheck where

import Ast.Common
import Ast.Term
import Ast.Type
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
import Data.Void
import Linearity
import qualified Misc.Boolean as Boolean
import Misc.Util (firstM, secondM, sortTopological, temporaries, uppers)

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
  | ExpectedTransparency p TypeUnify
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

data NominalBinding
  = Unnamed
  | Named TypeInfer

data TypeBinding p
  = TypeBinding p TypeUnify Level NominalBinding
  deriving (Functor)

data CheckEnvironment p = CheckEnvironment
  { typeEnvironment :: Map TermIdentifier (TermBinding p),
    kindEnvironment :: Map TypeIdentifier (TypeBinding p),
    typeGlobalEnvironment :: Map TermGlobalIdentifier (TermBinding p),
    kindGlobalEnvironment :: Map TypeGlobalIdentifier (TypeBinding p),
    moduleScope :: [String],
    typeSynonyms :: Map TypeGlobalIdentifier TypeInfer
  }
  deriving (Functor)

data TypeLogicalState p
  = UnboundType p TypeUnify Level
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
emptyEnvironment = CheckEnvironment Map.empty Map.empty Map.empty Map.empty [] Map.empty

askEnvironment :: Check p (CheckEnvironment p)
askEnvironment = Check ask

augmentTypeEnvironment :: TermIdentifier -> p -> TypeUnify -> LabelSchemeUnify -> Check p a -> Check p a
augmentTypeEnvironment x p l σ = modifyTypeEnvironment (Map.insert x (TermBinding p l σ))
  where
    modifyTypeEnvironment f = withEnvironment (\env -> env {typeEnvironment = f (typeEnvironment env)})
    withEnvironment f (Check r) = Check $ withReaderT f r

augmentKindEnvironment :: p -> TypeIdentifier -> TypeUnify -> Level -> Check p a -> Check p a
augmentKindEnvironment p x κ lev f =
  modifyKindEnvironment (Map.insert x (TypeBinding p κ lev Unnamed)) f
  where
    modifyKindEnvironment f (Check r) = Check $ withReaderT (\env -> env {kindEnvironment = f (kindEnvironment env)}) r

augmentKindUnify :: Bool -> p -> TypeIdentifier -> Check p a -> Check p a
augmentKindUnify occurs p x = modifyKindEnvironment (Map.insert x (TypeBinding p κ (if occurs then minBound else maxBound) Unnamed))
  where
    κ = error "kind used during unification"
    modifyKindEnvironment f (Check r) = Check $ withReaderT (\env -> env {kindEnvironment = f (kindEnvironment env)}) r

emptyState :: CheckState p
emptyState = CheckState Map.empty 0 (Level 0) Set.empty []

getState :: Check p (CheckState p)
getState = Check $ lift $ get

modifyState :: (CheckState p -> CheckState p) -> Check p ()
modifyState f = Check $ lift $ modify f

augmentTypePatternLevel :: TypePatternIntermediate p -> Check p b -> Check p b
augmentTypePatternLevel (TypePatternIntermediate p x κ) f = do
  useTypeVar x
  level <- levelCounter <$> getState
  f' <- augmentKindEnvironment p x (flexible κ) (succ level) $ leveled $ f
  logical <- typeLogicalMap <$> getState
  sat <- booleans <$> getState
  for sat $ \(σ, τ) -> do
    check logical x σ
    check logical x τ
  pure f'
  where
    useTypeVar (TypeIdentifier x) = do
      modifyState $ \state -> state {usedVars = Set.insert x $ usedVars state}
    check _ x (TypeAst () (TypeConstant (TypeVariable x'))) | x == x' = quit $ EscapingSkolemType p x
    check logical x (TypeAst () (TypeLogical v)) = case logical ! v of
      UnboundType _ _ _ -> pure ()
      LinkType σ -> check logical x σ
    check logical x (TypeAst () σ) = do
      traverseTypeF
        (absurd . runCore)
        (error "handled manually")
        (error "scheme in boolean")
        (check logical x)
        σ
      pure ()

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
  variables <- pure $ Map.keys $ Map.filter (\(_, _, lev') -> lev == lev') variables
  equations <- pure $ map (\(σ, τ) -> convertBoolean (zonk logical σ) + convertBoolean (zonk logical τ)) equations
  let (answers, equations') = Boolean.solve variables equations
  modifyState $ \state -> state {booleans = map (\σ -> (unconvertBoolean σ, TypeAst () TypeFalse)) equations'}
  answers <- Boolean.renameAnswers (fresh logical) answers
  answers <- pure $ Boolean.backSubstitute answers
  for answers $ \(x, σ) ->
    modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkType $ unconvertBoolean σ) $ typeLogicalMap state}
  where
    fresh logical x = case logical ! x of
      UnboundType p κ l -> freshTypeVariableRaw p κ l
      LinkType _ -> error "unexpected link"

freshTypeVariableRaw :: p -> TypeUnify -> Level -> Check p TypeLogical
freshTypeVariableRaw p κ lev = do
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
      modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundType p κ lev) $ typeLogicalMap state}

-- also changes logic type variable levels and check for escaping skolem variables
occursCheck :: forall p. p -> TypeLogical -> Level -> TypeUnify -> Check p ()
occursCheck p x lev σ' = go σ'
  where
    recurse = go
    go :: TypeUnify -> Check p ()
    go (TypeAst () σ) = do
      case σ of
        TypeConstant (TypeVariable x') -> do
          TypeBinding _ _ lev' _ <- (! x') <$> kindEnvironment <$> askEnvironment
          if lev' > lev
            then quit $ EscapingSkolemType p x'
            else pure ()
        TypeConstant (TypeGlobalVariable x') -> do
          TypeBinding _ _ lev' _ <- (! x') <$> kindGlobalEnvironment <$> askEnvironment
          if lev' > lev
            then error "type globals aren't supposed to be argumentable"
            else pure ()
        TypeLogical x' | x == x' -> quit $ TypeOccursCheck p x σ'
        TypeLogical x' ->
          (! x') <$> typeLogicalMap <$> getState >>= \case
            (UnboundType p' κ lev') ->
              if lev' > lev
                then do
                  modifyState $ \state -> state {typeLogicalMap = Map.insert x' (UnboundType p' κ lev) $ typeLogicalMap state}
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
        Kind σ τ -> do
          recurse σ
          recurse τ
        Syntactic -> pure ()
        Propositional -> pure ()
        Transparent -> pure ()
        Opaque -> pure ()
        Top -> pure ()
        Unification -> pure ()
        Transparency -> pure ()
        AmbiguousLabel -> pure ()
        Label -> pure ()
        Hole (Core v) -> absurd v
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
    occursPoly (TypeScheme () ς) = case ς of
      MonoType σ -> recurse σ
      TypeForall (Bound (TypePattern () x κ) ς) -> do
        augmentKindUnify True p x $ occursPoly ς
        recurse κ
        pure ()

kindIsMember :: forall p. p -> TypeUnify -> TypeUnify -> Check p ()
kindIsMember p (TypeAst () Top) _ = quit $ NotTypable p
kindIsMember p σ κ = do
  κ' <- reconstruct p σ
  matchType p κ κ'

reconstruct :: forall p. p -> TypeUnify -> Check p TypeUnify
reconstruct p = reconstructF indexEnvironment indexGlobalEnvironment indexLogicalMap poly representation multiplicities propositional
  where
    poly (TypeScheme () (TypeForall _)) = pure $ TypeAst () $ Type
    poly (TypeScheme () (MonoType σ)) = reconstruct p σ

    indexEnvironment x = (! x) <$> kindEnvironment <$> askEnvironment >>= kind
      where
        kind (TypeBinding _ κ _ _) = pure $ κ
    indexGlobalEnvironment x = (! x) <$> kindGlobalEnvironment <$> askEnvironment >>= kind
      where
        kind (TypeBinding _ κ _ _) = pure $ κ
    indexLogicalMap x = (! x) <$> typeLogicalMap <$> getState >>= index
    index (UnboundType _ x _) = pure x
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
      pure $ foldr (\τ ρ -> TypeAst () $ TypeBoolean $ TypeAnd τ ρ) unrestricted πs
    propositional [] = do
      κ <- freshTransparencyVariable p
      freshTypeVariable p (TypeAst () $ Kind (TypeAst () $ Propositional) κ)
    propositional (σ : σs) = do
      π <- reconstruct p σ
      for σs $ \σ -> do
        π' <- reconstruct p σ
        matchType p π π'
      pure π

unifyVariable :: p -> TypeLogical -> TypeUnify -> Level -> TypeUnify -> Check p ()
unifyVariable p x κ lev σ = do
  occursCheck p x lev σ
  kindIsMember p σ κ
  modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkType σ) $ typeLogicalMap state}
  pure ()

-- If two types unify, that imply that they're kinds are exactly the same
-- The type ast has enough information to uniquely determine a type's kind

-- Big rule: Unifing a logic type variable does not avoid captures
-- Rigid type variable scopes cannot shadow other rigid type variables
matchType :: p -> TypeUnify -> TypeUnify -> Check p ()
matchType p σ σ' = unify σ σ'
  where
    unify (TypeAst () (TypeLogical x)) (TypeAst () (TypeLogical x')) | x == x' = pure ()
    unify σ@(TypeAst () (TypeBoolean _)) τ = unifyBoolean σ τ
    unify σ τ@(TypeAst () (TypeBoolean _)) = unifyBoolean σ τ
    -- when unifying two variables, the right might not be a solved variable
    unify τ@(TypeAst () (TypeLogical x)) σ@(TypeAst () (TypeLogical x')) =
      (! x) <$> typeLogicalMap <$> getState >>= \case
        LinkType σ' -> unify σ' σ
        UnboundType _ κ lev ->
          (! x') <$> typeLogicalMap <$> getState >>= \case
            LinkType σ' -> unify τ σ'
            UnboundType _ _ _ -> unifyVariable p x κ lev σ
    unify (TypeAst () (TypeLogical x)) σ =
      (! x) <$> typeLogicalMap <$> getState >>= \case
        LinkType σ' -> unify σ' σ
        UnboundType _ κ lev -> unifyVariable p x κ lev σ
    unify σ (TypeAst () (TypeLogical x)) =
      (! x) <$> typeLogicalMap <$> getState >>= \case
        LinkType σ' -> unify σ σ'
        UnboundType _ κ lev -> unifyVariable p x κ lev σ
    unify (TypeAst () (TypeConstant σ)) (TypeAst () (TypeConstant σ')) | σ == σ' = pure ()
    unify (TypeAst () TypeTrue) (TypeAst () TypeTrue) = pure ()
    unify (TypeAst () TypeFalse) (TypeAst () TypeFalse) = pure ()
    unify (TypeAst () (Inline σ π τ)) (TypeAst () (Inline σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (TypeAst () (Poly σ ς)) (TypeAst () (Poly σ' ς')) = do
      unify σ σ'
      unifyPoly ς ς'
    unify (TypeAst () (FunctionPointer σ π τ)) (TypeAst () (FunctionPointer σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (TypeAst () (FunctionLiteralType σ π τ)) (TypeAst () (FunctionLiteralType σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (TypeAst () (Tuple σs)) (TypeAst () (Tuple σs')) | length σs == length σs' = do
      sequence $ zipWith (unify) σs σs'
      pure ()
    unify (TypeAst () (Effect σ π)) (TypeAst () (Effect σ' π')) = do
      unify σ σ'
      unify π π'
    unify (TypeAst () (Unique σ)) (TypeAst () (Unique σ')) = do
      unify σ σ'
    unify (TypeAst () (Shared σ π)) (TypeAst () (Shared σ' π')) = do
      unify σ σ'
      unify π π'
    unify (TypeAst () (Pointer σ)) (TypeAst () (Pointer σ')) = do
      unify σ σ'
    unify (TypeAst () (Array σ)) (TypeAst () (Array σ')) = do
      unify σ σ'
    unify (TypeAst () (Number ρ1 ρ2)) (TypeAst () (Number ρ1' ρ2')) = do
      unify ρ1 ρ1'
      unify ρ2 ρ2'
    unify (TypeAst () Boolean) (TypeAst () Boolean) = pure ()
    unify (TypeAst () (Step σ τ)) (TypeAst () (Step σ' τ')) = do
      unify σ σ'
      unify τ τ'
    unify (TypeAst () Type) (TypeAst () Type) = pure ()
    unify (TypeAst () Region) (TypeAst () Region) = pure ()
    unify (TypeAst () (Pretype κ τ)) (TypeAst () (Pretype κ' τ')) = do
      unify κ κ'
      unify τ τ'
    unify (TypeAst () Boxed) (TypeAst () Boxed) = pure ()
    unify (TypeAst () Multiplicity) (TypeAst () Multiplicity) = pure ()
    unify (TypeAst () (KindRuntime PointerRep)) (TypeAst () (KindRuntime PointerRep)) = pure ()
    unify (TypeAst () (KindRuntime (StructRep κs))) (TypeAst () (KindRuntime (StructRep κs'))) | length κs == length κs' = do
      sequence_ $ zipWith (unify) κs κs'
    unify (TypeAst () (KindRuntime (UnionRep κs))) (TypeAst () (KindRuntime (UnionRep κs'))) | length κs == length κs' = do
      sequence_ $ zipWith (unify) κs κs'
    unify (TypeAst () (KindRuntime (WordRep κ))) (TypeAst () (KindRuntime (WordRep κ'))) = unify κ κ'
    unify (TypeAst () (KindSize Byte)) (TypeAst () (KindSize Byte)) = pure ()
    unify (TypeAst () (KindSize Short)) (TypeAst () (KindSize Short)) = pure ()
    unify (TypeAst () (KindSize Int)) (TypeAst () (KindSize Int)) = pure ()
    unify (TypeAst () (KindSize Long)) (TypeAst () (KindSize Long)) = pure ()
    unify (TypeAst () (KindSize Native)) (TypeAst () (KindSize Native)) = pure ()
    unify (TypeAst () (KindSignedness Signed)) (TypeAst () (KindSignedness Signed)) = pure ()
    unify (TypeAst () (KindSignedness Unsigned)) (TypeAst () (KindSignedness Unsigned)) = pure ()
    unify (TypeAst () Representation) (TypeAst () Representation) = pure ()
    unify (TypeAst () Size) (TypeAst () Size) = pure ()
    unify (TypeAst () Signedness) (TypeAst () Signedness) = pure ()
    unify (TypeAst () (Kind σ τ)) (TypeAst () (Kind σ' τ')) = do
      unify σ σ'
      unify τ τ'
    unify (TypeAst () Syntactic) (TypeAst () Syntactic) = pure ()
    unify (TypeAst () Propositional) (TypeAst () Propositional) = pure ()
    unify (TypeAst () Transparent) (TypeAst () Transparent) = pure ()
    unify (TypeAst () Opaque) (TypeAst () Opaque) = pure ()
    unify (TypeAst () Transparency) (TypeAst () Transparency) = pure ()
    unify (TypeAst () Unification) (TypeAst () Unification) = pure ()
    unify (TypeAst () AmbiguousLabel) (TypeAst () AmbiguousLabel) = pure ()
    unify (TypeAst () Label) (TypeAst () Label) = pure ()
    unify (TypeAst () Top) (TypeAst () Top) = pure ()
    unify σ σ' = quit $ TypeMismatch p σ σ'

    unifyPoly
      (TypeScheme () (TypeForall (Bound (TypePattern () α κ) ς)))
      (TypeScheme () (TypeForall (Bound (TypePattern () α' κ') ς'))) = do
        unify κ κ'
        -- A logical variable inside of this forall may have been equated with a type that contains this forall's binding.
        -- To prevent a capture, this forall is alpha converted to  new rigid variable that doesn't exist in the current environment.
        -- This alpha renaming does not convert under logic variables.
        vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
        let αf = fresh vars α
        let ς2 = convertType αf α ς
        let ς'2 = convertType αf α' ς'
        augmentKindUnify False p αf $ unifyPoly ς2 ς'2
        pure ()
    unifyPoly
      (TypeScheme () (MonoType σ))
      (TypeScheme () (MonoType σ')) =
        unify σ σ'
    unifyPoly ς ς' = quit $ TypePolyMismatch p ς ς'

    unifyBoolean σ τ = do
      κ <- reconstruct p σ
      κ' <- reconstruct p τ
      matchType p κ κ'
      modifyState $ \state -> state {booleans = (σ, τ) : booleans state}

freshTypeVariable p κ = (TypeAst () . TypeLogical) <$> (levelCounter <$> getState >>= freshTypeVariableRaw p κ)

freshRepresentationKindVariable p = freshTypeVariable p (TypeAst () Representation)

freshSizeKindVariable p = freshTypeVariable p (TypeAst () Size)

freshSignednessKindVariable p = freshTypeVariable p (TypeAst () Signedness)

freshOrderabilityVariable p = freshTypeVariable p (TypeAst () Unification)

freshTransparencyVariable p = freshTypeVariable p (TypeAst () Transparency)

freshMetaTypeVariable p = do
  freshTypeVariable p (TypeAst () Type)

freshMultiplicityKindVariable p = do
  freshTypeVariable p (TypeAst () Multiplicity)

freshPretypeTypeVariable p = do
  s <- freshRepresentationKindVariable p
  τ <- freshMultiplicityKindVariable p
  freshTypeVariable p (TypeAst () $ Pretype s τ)

freshBoxedTypeVariable p = do
  freshTypeVariable p (TypeAst () Boxed)

freshRegionTypeVariable p = do
  freshTypeVariable p $ TypeAst () $ Region

freshLabelTypeVariable p = do
  freshTypeVariable p $ TypeAst () $ Label

checkKind _ (TypeAst () (Kind σ τ)) = pure (σ, τ)
checkKind p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkKind p σ
    UnboundType _ κ l -> do
      μ <- freshOrderabilityVariable p
      π <- freshTransparencyVariable p
      unifyVariable p x κ l (TypeAst () (Kind μ π))
      pure (μ, κ)
checkKind p σ = quit $ ExpectedKind p σ

checkRepresentation _ (TypeAst () Representation) = pure ()
checkRepresentation p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkRepresentation p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () Representation)
      pure ()
checkRepresentation p σ = quit $ ExpectedRepresentation p σ

checkMultiplicity _ (TypeAst () Multiplicity) = pure ()
checkMultiplicity p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkMultiplicity p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () Multiplicity)
      pure ()
checkMultiplicity p σ = quit $ ExpectedMultiplicity p σ

checkSize _ (TypeAst () Size) = pure ()
checkSize p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkSize p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () Size)
      pure ()
checkSize p σ = quit $ ExpectedSize p σ

checkSignedness _ (TypeAst () Signedness) = pure ()
checkSignedness p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkSignedness p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () Signedness)
      pure ()
checkSignedness p σ = quit $ ExpectedSignedness p σ

checkType _ (TypeAst () Type) = pure ()
checkType p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkType p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () Type)
      pure ()
checkType p σ = quit $ ExpectedType p σ

checkPretype _ (TypeAst () (Pretype σ τ)) = pure (σ, τ)
checkPretype p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkPretype p σ
    UnboundType _ κ l -> do
      σ <- freshRepresentationKindVariable p
      τ <- freshMultiplicityKindVariable p
      unifyVariable p x κ l (TypeAst () $ Pretype σ τ)
      pure (κ, τ)
checkPretype p σ = quit $ ExpectedPretype p σ

checkBoxed _ (TypeAst () Boxed) = pure ()
checkBoxed p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkBoxed p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () Boxed)
      pure ()
checkBoxed p σ = quit $ ExpectedBoxed p σ

checkRegion _ (TypeAst () Region) = pure ()
checkRegion p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkRegion p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () Region)
      pure ()
checkRegion p σ = quit $ ExpectedRegion p σ

checkPropoitional _ (TypeAst () Propositional) = pure ()
checkPropoitional p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkPropoitional p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () Propositional)
      pure ()
checkPropoitional p σ = quit $ ExpectedPropositional p σ

checkUnification _ (TypeAst () Unification) = pure ()
checkUnification p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkUnification p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () Unification)
      pure ()
checkUnification p σ = quit $ ExpectedUnification p σ

checkTransparency _ (TypeAst () Transparency) = pure ()
checkTransparency p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkTransparency p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () Transparency)
      pure ()
checkTransparency p σ = quit $ ExpectedTransparency p σ

checkInline _ (TypeAst () (Inline σ τ π)) = pure (σ, τ, π)
checkInline p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkInline p σ
    UnboundType _ κ l -> do
      σ <- freshMetaTypeVariable p
      π <- freshMultiplicityKindVariable p
      τ <- freshMetaTypeVariable p
      unifyVariable p x κ l (TypeAst () (Inline σ π τ))
      pure (σ, π, τ)
checkInline p σ = quit $ ExpectedInline p σ

checkFunctionPointer _ (TypeAst () (FunctionPointer σ τ π)) = pure (σ, τ, π)
checkFunctionPointer p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkFunctionPointer p σ
    UnboundType _ κ l -> do
      σ <- freshPretypeTypeVariable p
      π <- freshRegionTypeVariable p
      τ <- freshPretypeTypeVariable p
      unifyVariable p x κ l (TypeAst () $ FunctionPointer σ π τ)
      pure (σ, π, τ)
checkFunctionPointer p σ = quit $ ExpectedFunctionPointer p σ

checkFunctionLiteralType _ (TypeAst () (FunctionLiteralType σ τ π)) = pure (σ, τ, π)
checkFunctionLiteralType p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkFunctionLiteralType p σ
    UnboundType _ κ l -> do
      σ <- freshPretypeTypeVariable p
      π <- freshRegionTypeVariable p
      τ <- freshPretypeTypeVariable p
      unifyVariable p x κ l (TypeAst () $ FunctionLiteralType σ π τ)
      pure (σ, π, τ)
checkFunctionLiteralType p σ = quit $ ExpectedFunctionLiteralType p σ

checkUnique _ (TypeAst () (Unique σ)) = pure σ
checkUnique p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkUnique p σ
    UnboundType _ κ l -> do
      σ <- freshBoxedTypeVariable p
      unifyVariable p x κ l (TypeAst () $ Unique σ)
      pure σ
checkUnique p σ = quit $ ExpectedUnique p σ

checkPointer _ (TypeAst () (Pointer σ)) = pure σ
checkPointer p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkPointer p σ
    UnboundType _ κ l -> do
      σ <- freshPretypeTypeVariable p
      unifyVariable p x κ l (TypeAst () $ Pointer σ)
      pure (σ)
checkPointer p σ = quit $ ExpectedPointer p σ

checkArray _ (TypeAst () (Array σ)) = pure σ
checkArray p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkArray p σ
    UnboundType _ κ l -> do
      σ <- freshPretypeTypeVariable p
      unifyVariable p x κ l (TypeAst () $ Array σ)
      pure (σ)
checkArray p σ = quit $ ExpectedArray p σ

checkEffect _ (TypeAst () (Effect σ τ)) = pure (σ, τ)
checkEffect p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkEffect p σ
    UnboundType _ κ l -> do
      σ <- freshPretypeTypeVariable p
      π <- freshRegionTypeVariable p
      unifyVariable p x κ l (TypeAst () $ Effect σ π)
      pure (σ, π)
checkEffect p σ = quit $ ExpectedEffect p σ

checkShared _ (TypeAst () (Shared σ τ)) = pure (σ, τ)
checkShared p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkShared p σ
    UnboundType _ κ l -> do
      σ <- freshBoxedTypeVariable p
      π <- freshRegionTypeVariable p
      unifyVariable p x κ l (TypeAst () $ Shared σ π)
      pure (σ, π)
checkShared p σ = quit $ ExpectedShared p σ

checkNumber _ (TypeAst () (Number σ τ)) = pure (σ, τ)
checkNumber p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkNumber p σ
    UnboundType _ κ l -> do
      ρ1 <- freshSignednessKindVariable p
      ρ2 <- freshSizeKindVariable p
      unifyVariable p x κ l (TypeAst () $ Number ρ1 ρ2)
      pure (ρ1, ρ2)
checkNumber p σ = quit $ ExpectedNumber p σ

checkBoolean _ (TypeAst () Boolean) = pure ()
checkBoolean p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkBoolean p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () $ Boolean)
      pure ()
checkBoolean p σ = quit $ ExpectedBoolean p σ

checkStep _ (TypeAst () (Step σ τ)) = pure (σ, τ)
checkStep p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkStep p σ
    UnboundType _ κ l -> do
      σ <- freshPretypeTypeVariable p
      τ <- freshPretypeTypeVariable p
      unifyVariable p x κ l (TypeAst () $ Step σ τ)
      pure (σ, τ)
checkStep p σ = quit $ ExpectedStep p σ

checkLabel _ (TypeAst () Label) = pure ()
checkLabel p (TypeAst () (TypeLogical x)) =
  (! x) <$> typeLogicalMap <$> getState >>= \case
    LinkType σ -> checkLabel p σ
    UnboundType _ κ l -> do
      unifyVariable p x κ l (TypeAst () Label)
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
    matchType p l (TypeAst () $ TypeBoolean $ TypeAnd base l)
    pure ()
  pure ()

requireUnrestricted p σ = do
  κ <- reconstruct p σ
  (_, l) <- checkPretype p κ
  matchType p l unrestricted
  pure ()

-- todo relabel seems somewhat fragile here
-- this depends on `(σ, κ) <- kindCheck σ`, never having unification variables in σ
-- because relabel ignores unification variables
augmentMetaTermPattern l (TermPattern p (PatternVariable x σ)) = augmentVariableLinear p x l (reLabel (TypeScheme () $ MonoType σ))

nullEffect σ = TypeScheme () $ MonoType $ TypeAst () $ Effect σ none

augmentRuntimeTermPattern pm = go pm
  where
    go (TermRuntimePattern p (RuntimePatternVariable x σ)) = \e -> do
      κ <- reconstruct p σ
      (_, l) <- checkPretype p κ
      augmentVariableLinear p x l (MonoLabel (nullEffect σ)) e
    go (TermRuntimePattern _ (RuntimePatternTuple pms)) = foldr (.) id (map go pms)
    go (TermRuntimePattern _ (RuntimePatternBoolean _)) = id

typeCheckMetaPattern :: TermPatternSource p -> Check p (TermPatternUnify p, TypeUnify)
typeCheckMetaPattern = \case
  (TermPattern p (PatternVariable x σ)) -> do
    σ' <- case σ of
      TypeAst _ (Hole (Source ())) -> freshMetaTypeVariable p
      σ -> do
        (σ', _) <- secondM (checkType p) =<< kindCheck σ
        pure (flexible σ')
    pure (TermPattern p (PatternVariable x σ'), σ')

typeCheckRuntimePattern = \case
  (TermRuntimePattern p (RuntimePatternVariable x σ)) -> do
    σ' <- case σ of
      TypeAst _ (Hole (Source ())) -> freshPretypeTypeVariable p
      σ -> do
        (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
        pure (flexible σ')
    pure (TermRuntimePattern p $ RuntimePatternVariable x σ', σ')
  (TermRuntimePattern p (RuntimePatternTuple pms)) -> do
    (pms, σs) <- unzip <$> traverse typeCheckRuntimePattern pms
    pure (TermRuntimePattern p $ RuntimePatternTuple pms, TypeAst () (Tuple σs))
  (TermRuntimePattern p (RuntimePatternBoolean b)) -> do
    pure (TermRuntimePattern p $ RuntimePatternBoolean b, TypeAst () $ Boolean)

kindCheckScheme :: Mode -> TypeSchemeSource p -> Check p (TypeSchemeInfer, TypeUnify)
kindCheckScheme mode =
  \case
    TypeScheme p (MonoType σ) -> do
      (σ', _) <- secondM (checkType p) =<< kindCheck σ
      pure (TypeScheme () (MonoType σ'), TypeAst () Type)
    TypeScheme p (TypeForall (Bound pm σ)) -> do
      (pm', _) <- kindCheckPattern mode pm
      augmentTypePatternLevel pm' $ do
        (σ', _) <- secondM (checkType p) =<< kindCheckScheme mode σ
        pure (TypeScheme () $ TypeForall (Bound (toTypePattern pm') σ'), TypeAst () $ Type)

kindCheckPattern :: Mode -> TypePatternSource p -> Check p (TypePatternIntermediate p, TypeUnify)
kindCheckPattern mode (TypePattern p x κ) = do
  (κ, (_, σ)) <- secondM (checkKind p) =<< kindCheck κ
  case mode of
    SymbolMode -> matchType p σ (TypeAst () Transparent)
    InlineMode -> pure ()
  pure (TypePatternIntermediate p x κ, flexible κ)

kindCheck :: TypeSource p -> Check p (TypeInfer, TypeUnify)
kindCheck (TypeAst p σ) = case σ of
  TypeConstant (TypeVariable x) -> do
    Map.lookup x <$> kindEnvironment <$> askEnvironment >>= \case
      Just (TypeBinding _ κ _ _) -> pure (TypeAst () $ TypeConstant $ TypeVariable x, κ)
      Nothing -> do
        heading <- moduleScope <$> askEnvironment
        kindCheck (TypeAst p $ TypeConstant $ TypeGlobalVariable $ globalType heading x)
  TypeConstant (TypeGlobalVariable x) -> do
    Map.lookup x <$> kindGlobalEnvironment <$> askEnvironment >>= \case
      Just (TypeBinding _ κ _ _) -> pure (TypeAst () $ TypeConstant $ TypeGlobalVariable x, κ)
      Nothing ->
        Map.lookup x <$> typeSynonyms <$> askEnvironment >>= \case
          Just σ -> do
            κ <- reconstruct p (flexible σ)
            pure (flexible σ, κ)
          Nothing -> quit $ UnknownTypeGlobalIdentifier p x
  Inline σ π τ -> do
    (σ', _) <- secondM (checkType p) =<< kindCheck σ
    (π', _) <- secondM (checkMultiplicity p) =<< kindCheck π
    (τ', _) <- secondM (checkType p) =<< kindCheck τ
    pure (TypeAst () $ Inline σ' π' τ', TypeAst () $ Type)
  Poly σ λ -> do
    (σ, _) <- secondM (checkLabel p) =<< kindCheck σ
    (ς, κ) <- kindCheckScheme InlineMode λ
    pure (TypeAst () $ Poly σ ς, κ)
  FunctionPointer σ π τ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (TypeAst () $ FunctionPointer σ' π' τ', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) unrestricted)
  FunctionLiteralType σ π τ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    (τ', _) <- secondM (checkPretype p) =<< kindCheck τ
    pure (TypeAst () $ FunctionLiteralType σ' π' τ', TypeAst () $ Type)
  Tuple σs -> do
    (σs, (ρs, τs)) <- second unzip <$> unzip <$> traverse (secondM (checkPretype p) <=< kindCheck) σs
    let τ = foldr (\σ τ -> TypeAst () $ TypeBoolean $ TypeAnd σ τ) unrestricted τs
    pure (TypeAst () $ Tuple σs, TypeAst () $ Pretype (TypeAst () $ KindRuntime $ StructRep ρs) τ)
  Step σ τ -> do
    (σ, (κ, _)) <- secondM (checkPretype p) =<< kindCheck σ
    (τ, (μ, _)) <- secondM (checkPretype p) =<< kindCheck τ
    let union = TypeAst () $ KindRuntime $ UnionRep $ [κ, μ]
    let wrap = TypeAst () $ KindRuntime $ StructRep $ [TypeAst () $ KindRuntime $ WordRep $ TypeAst () $ KindSize $ Byte, union]
    pure (TypeAst () $ Step σ τ, TypeAst () $ Pretype wrap $ linear)
  Effect σ π -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    pure (TypeAst () $ Effect σ' π', TypeAst () $ Type)
  Unique σ -> do
    (σ', _) <- secondM (checkBoxed p) =<< kindCheck σ
    pure (TypeAst () $ Unique σ', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) linear)
  Shared σ π -> do
    (σ', _) <- secondM (checkBoxed p) =<< kindCheck σ
    (π', _) <- secondM (checkRegion p) =<< kindCheck π
    pure (TypeAst () $ Shared σ' π', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) unrestricted)
  Pointer σ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    pure (TypeAst () $ Pointer σ', TypeAst () $ Boxed)
  Array σ -> do
    (σ', _) <- secondM (checkPretype p) =<< kindCheck σ
    pure (TypeAst () $ Array σ', TypeAst () $ Boxed)
  Number ρ1 ρ2 -> do
    (ρ1', _) <- secondM (checkSignedness p) =<< kindCheck ρ1
    (ρ2', _) <- secondM (checkSize p) =<< kindCheck ρ2
    pure (TypeAst () $ Number ρ1' ρ2', TypeAst () $ Pretype (TypeAst () $ KindRuntime $ WordRep (flexible ρ2')) unrestricted)
  Boolean -> do
    pure (TypeAst () $ Boolean, TypeAst () $ Pretype (TypeAst () $ KindRuntime $ WordRep $ TypeAst () $ KindSize $ Byte) unrestricted)
  TypeConstant World -> do
    pure (TypeAst () $ TypeConstant World, TypeAst () Region)
  TypeLogical v -> absurd v
  Type -> do
    pure (TypeAst () Type, TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Transparent))
  Region -> pure (TypeAst () Region, TypeAst () $ Kind (TypeAst () Propositional) (TypeAst () Transparent))
  KindRuntime PointerRep -> pure (TypeAst () $ KindRuntime PointerRep, TypeAst () Representation)
  KindRuntime (StructRep κs) -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< kindCheck) κs
    pure (TypeAst () (KindRuntime (StructRep κs')), TypeAst () Representation)
  KindRuntime (UnionRep κs) -> do
    (κs', _) <- unzip <$> traverse (secondM (checkRepresentation p) <=< kindCheck) κs
    pure (TypeAst () (KindRuntime (UnionRep κs')), TypeAst () Representation)
  KindRuntime (WordRep κ) -> do
    (κ', _) <- secondM (checkSize p) =<< kindCheck κ
    pure (TypeAst () (KindRuntime (WordRep κ')), TypeAst () Representation)
  KindSize κ -> pure (TypeAst () (KindSize κ), TypeAst () Size)
  KindSignedness κ -> pure (TypeAst () (KindSignedness κ), TypeAst () Signedness)
  Pretype κ τ -> do
    (κ', _) <- secondM (checkRepresentation p) =<< kindCheck κ
    (τ', _) <- secondM (checkMultiplicity p) =<< kindCheck τ
    pure (TypeAst () $ Pretype κ' τ', TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Transparent))
  Boxed -> do
    pure (TypeAst () $ Boxed, TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Transparent))
  Multiplicity -> do
    pure (TypeAst () $ Multiplicity, TypeAst () $ Kind (TypeAst () Propositional) (TypeAst () Transparent))
  Representation -> pure (TypeAst () Representation, TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Opaque))
  Size -> pure (TypeAst () Size, TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Opaque))
  Signedness -> pure (TypeAst () Signedness, TypeAst () $ Kind (TypeAst () Syntactic) (TypeAst () Opaque))
  Kind μ κ -> do
    (μ, _) <- secondM (checkUnification p) =<< kindCheck μ
    (κ, _) <- secondM (checkTransparency p) =<< kindCheck κ
    pure (TypeAst () (Kind μ κ), TypeAst () Top)
  Syntactic -> do
    pure (TypeAst () Syntactic, TypeAst () Unification)
  Propositional -> do
    pure (TypeAst () Propositional, TypeAst () Unification)
  Transparent -> do
    pure (TypeAst () Transparent, TypeAst () Transparency)
  Opaque -> do
    pure (TypeAst () Opaque, TypeAst () Transparency)
  Unification -> do
    pure (TypeAst () Unification, TypeAst () Top)
  Transparency -> do
    pure (TypeAst () Transparency, TypeAst () Top)
  AmbiguousLabel -> do
    pure (TypeAst () AmbiguousLabel, TypeAst () Label)
  Label -> do
    pure (TypeAst () Label, TypeAst () $ Top)
  TypeTrue -> do
    κ <- freshTransparencyVariable p
    π <- freshTypeVariable p (TypeAst () $ Kind (TypeAst () $ Propositional) κ)
    pure (TypeAst () $ TypeTrue, π)
  TypeFalse -> do
    κ <- freshTransparencyVariable p
    π <- freshTypeVariable p (TypeAst () $ Kind (TypeAst () $ Propositional) κ)
    pure (TypeAst () $ TypeFalse, π)
  TypeBoolean (TypeXor σ τ) -> do
    (σ', κ) <- kindCheck σ
    (τ', κ') <- kindCheck τ
    matchType p κ κ'
    (ρ, _) <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (TypeAst () $ TypeBoolean $ TypeXor σ' τ', κ)
  TypeBoolean (TypeOr σ τ) -> do
    (σ', κ) <- kindCheck σ
    (τ', κ') <- kindCheck τ
    matchType p κ κ'
    (ρ, _) <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (TypeAst () $ TypeBoolean $ TypeOr σ' τ', κ)
  TypeBoolean (TypeAnd σ τ) -> do
    (σ', κ) <- kindCheck σ
    (τ', κ') <- kindCheck τ
    matchType p κ κ'
    (ρ, _) <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (TypeAst () $ TypeBoolean $ TypeAnd σ' τ', κ)
  TypeBoolean (TypeNot σ) -> do
    (σ', κ) <- kindCheck σ
    (ρ, _) <- checkKind p =<< reconstruct p κ
    checkPropoitional p ρ
    pure (TypeAst () $ TypeBoolean $ TypeNot σ', κ)
  Top -> quit $ NotTypable p
  Hole (Source ()) -> quit $ NotTypable p

instantiate p (TypeScheme () ς) = case ς of
  MonoType σ -> pure (σ, Instantiation InstantiateEmpty)
  TypeForall (Bound (TypePattern () x κ) σ) -> do
    τ <- freshTypeVariable p κ
    (ς, θ) <- instantiate p $ substituteType τ x σ
    pure (ς, Instantiation $ InstantiateType τ θ)

instantiateLabel :: p -> LabelSchemeUnify -> Check p (TypeUnify, InstantiationUnify)
instantiateLabel p (MonoLabel ς) = instantiate p ς
instantiateLabel p (LabelForall x ς) = do
  τ <- freshLabelTypeVariable p
  instantiateLabel p $ substituteLabel τ x ς
  where
    -- todo maybe make LabelScheme a part of TypeAlgebra
    substituteLabel σx x (MonoLabel σ) = MonoLabel $ substituteType σx x σ
    -- todo labels are assumed to not overlap here
    substituteLabel σx x (LabelForall x' ς) = LabelForall x' (substituteLabel σx x ς)

expectTypeAnnotation p Nothing = quit $ ExpectedTypeAnnotation p
expectTypeAnnotation _ (Just σ) = pure σ

validateType σ = fst <$> kindCheck σ

data Checked p σ = Checked (TermUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

data CheckedScheme p σ = CheckedScheme (TermSchemeUnify p) σ (Use TermIdentifier)
  deriving (Functor, Foldable, Traversable)

regions [] = none
regions σs = foldl1 (\π1 π2 -> TypeAst () $ TypeBoolean $ TypeOr π1 π2) σs

typeCheck :: forall p. TermSource p -> Check p (Checked p TypeUnify)
typeCheck (Term p e) = case e of
  TermRuntime (Variable x (Source ())) -> do
    mσ <- Map.lookup x <$> typeEnvironment <$> askEnvironment
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiateLabel p σ
        pure $ Checked (Term p $ TermRuntime $ Variable x (Core θ)) τ (Use x)
      Nothing -> do
        heading <- moduleScope <$> askEnvironment
        typeCheck (Term p $ GlobalVariable (globalTerm heading x) (Source ()))
  GlobalVariable x (Source ()) -> do
    mσ <- Map.lookup x <$> typeGlobalEnvironment <$> askEnvironment
    case mσ of
      Just (TermBinding _ _ σ) -> do
        (τ, θ) <- instantiateLabel p σ
        -- todo useNothing here is kinda of a hack
        pure $ Checked (Term p $ GlobalVariable x (Core θ)) τ useNothing
      Nothing -> quit $ UnknownGlobalIdentifier p x
  InlineAbstraction (Bound pm e) -> do
    (pm', σ) <- typeCheckMetaPattern pm
    π <- freshMultiplicityKindVariable p
    Checked e' τ lΓ <- augmentMetaTermPattern π pm' (typeCheck e)
    pure $ Checked (Term p $ InlineAbstraction $ Bound pm' e') (TypeAst () $ Inline σ π τ) lΓ
  InlineApplication e1 e2 (Source ()) -> do
    Checked e1' (σ, π, τ) lΓ1 <- traverse (checkInline p) =<< typeCheck e1
    Checked e2' σ' lΓ2 <- typeCheck e2
    matchType p σ σ'
    capture p π lΓ2
    pure $ Checked (Term p $ InlineApplication e1' e2' (Core σ)) τ (lΓ1 `combine` lΓ2)
  Bind e1 (Bound pm e2) -> do
    Checked e1' τ lΓ1 <- typeCheck e1
    (pm', τ') <- typeCheckMetaPattern pm
    matchType p τ τ'
    π <- freshMultiplicityKindVariable p
    Checked e2' σ lΓ2 <- augmentMetaTermPattern π pm' $ typeCheck e2
    capture p π lΓ1
    pure $ Checked (Term p $ Bind e1' $ Bound pm' e2') σ (lΓ1 `combine` lΓ2)
  PolyIntroduction λ -> do
    CheckedScheme eς σ lΓ <- typeCheckScheme InlineMode λ
    τ <- freshLabelTypeVariable p
    vars <- typeLogicalMap <$> getState
    let σ' = zonk vars σ
    pure $ Checked (Term p $ PolyIntroduction $ eς) (TypeAst () $ Poly τ σ') lΓ
  PolyElimination e (Source ()) (Source ()) -> do
    Checked e ς lΓ <- leveled $ typeCheck e
    elimatePoly e ς lΓ
    where
      elimatePoly e τ@(TypeAst () (Poly l ς)) lΓ = do
        validateLevel l
        (σ, θ) <- instantiate p ς
        pure $ Checked (Term p $ PolyElimination e (Core θ) (Core τ)) σ lΓ
      elimatePoly e (TypeAst () (TypeLogical v)) lΓ =
        (! v) <$> typeLogicalMap <$> getState >>= \case
          LinkType σ -> elimatePoly e σ lΓ
          _ -> quit $ ExpectedTypeAnnotation p
      elimatePoly _ _ _ = quit $ ExpectedTypeAnnotation p
      validateLevel (TypeAst () (TypeLogical v)) =
        (! v) <$> typeLogicalMap <$> getState >>= \case
          LinkType σ -> validateLevel σ
          UnboundType p _ level' -> do
            level <- levelCounter <$> getState
            if level >= level'
              then quit $ ExpectedTypeAnnotation p
              else pure ()
      validateLevel _ = quit $ ExpectedTypeAnnotation p
  TermRuntime (Alias e1 (Bound pm e2)) -> do
    (pm', τ) <- typeCheckRuntimePattern pm
    Checked e1' (τ', π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p τ τ'
    Checked e2' (σ, π2) lΓ2 <- traverse (checkEffect p) =<< augmentRuntimeTermPattern pm' (typeCheck e2)
    let π = regions [π1, π2]
    pure $ Checked (Term p $ TermRuntime $ Alias e1' $ Bound pm' e2') (TypeAst () $ Effect σ π) (lΓ1 `combine` lΓ2)
  TermRuntime (Case e (Source ()) λs) -> do
    Checked e (τ, π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e
    σ <- freshPretypeTypeVariable p
    (e2, pm, πs, lΓ2) <- fmap unzip4 $
      for λs $ \(Bound pm e2) -> do
        (pm, τ') <- typeCheckRuntimePattern pm
        matchType p τ τ'
        Checked e2 (σ', π) lΓ2 <- traverse (checkEffect p) =<< augmentRuntimeTermPattern pm (typeCheck e2)
        matchType p σ σ'
        pure (e2, pm, π, lΓ2)
    let π = regions $ π1 : πs
    pure $ Checked (Term p $ TermRuntime $ Case e (Core τ) $ zipWith Bound pm e2) (TypeAst () $ Effect σ π) (lΓ1 `combine` branchAll lΓ2)
  TermRuntime (Extern sym (Source ()) (Source ()) (Source ())) -> do
    σ <- freshPretypeTypeVariable p
    π <- freshRegionTypeVariable p
    τ <- freshPretypeTypeVariable p
    pure $
      Checked
        (Term p $ TermRuntime $ Extern sym (Core σ) (Core π) (Core τ))
        (TypeAst () $ Effect (TypeAst () $ FunctionPointer σ π τ) none)
        useNothing
  TermRuntime (FunctionApplication e1 e2 (Source ())) -> do
    Checked e1' ((σ, π2, τ), π1) lΓ1 <- traverse (firstM (checkFunctionPointer p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' (σ', π3) lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
    matchType p σ σ'
    let π = regions [π1, π2, π3]
    pure $
      Checked
        (Term p $ TermRuntime $ FunctionApplication e1' e2' (Core σ))
        (TypeAst () $ Effect τ π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (TupleIntroduction es) -> do
    checked <- traverse (traverse (checkEffect p) <=< typeCheck) es
    let (es, σs, πs, lΓs) = unzip4 $ map (\(Checked es (σ, π) lΓ) -> (es, σ, π, lΓ)) checked
    let π = regions πs
    pure $
      Checked
        (Term p $ TermRuntime $ TupleIntroduction es)
        (TypeAst () $ Effect (TypeAst () (Tuple σs)) π)
        (combineAll lΓs)
  TermRuntime (ReadReference e) -> do
    Checked e' ((σ, π2), π1) lΓ <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck e
    let π = regions [π1, π2]
    requireUnrestricted p σ
    pure $ Checked (Term p $ TermRuntime $ ReadReference e') (TypeAst () $ Effect σ π) lΓ
  TermRuntime (WriteReference ep ev (Source ())) -> do
    Checked ep ((σ, π2), π1) lΓ1 <- traverse (firstM (firstM (checkPointer p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
    Checked ev (σ', π3) lΓ2 <- traverse (checkEffect p) =<< typeCheck ev
    matchType p σ σ'
    let π = regions [π1, π2, π3]
    requireUnrestricted p σ
    pure $
      Checked
        (Term p $ TermRuntime $ WriteReference ep ev (Core σ))
        (TypeAst () $ Effect (TypeAst () $ Tuple []) π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (NumberLiteral v) -> do
    ρ1 <- freshSignednessKindVariable p
    ρ2 <- freshSizeKindVariable p
    pure $
      Checked
        (Term p $ TermRuntime (NumberLiteral v))
        (TypeAst () $ Effect (TypeAst () $ Number ρ1 ρ2) none)
        useNothing
  TermRuntime (Arithmatic o e1 e2 (Source ())) -> do
    Checked e1' ((ρ1, ρ2), π1) lΓ1 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' ((ρ1', ρ2'), π2) lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e2
    matchType p ρ1 ρ1'
    matchType p ρ2 ρ2'
    let π = regions [π1, π2]
    pure $
      Checked
        (Term p $ TermRuntime $ Arithmatic o e1' e2' (Core ρ1))
        (TypeAst () $ Effect (TypeAst () $ Number ρ1 ρ2) π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (Relational o e1 e2 (Source ()) (Source ())) -> do
    Checked e1' ((ρ1, ρ2), π1) lΓ1 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e1
    Checked e2' ((ρ1', ρ2'), π2) lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck e2
    matchType p ρ1 ρ1'
    matchType p ρ2 ρ2'
    let π = regions [π1, π2]
    pure $
      Checked
        (Term p $ TermRuntime $ Relational o e1' e2' (Core (TypeAst () $ Number ρ1 ρ2)) (Core ρ1))
        (TypeAst () $ Effect (TypeAst () $ Boolean) π)
        (lΓ1 `combine` lΓ2)
  FunctionLiteral (Bound pm e) -> do
    (pm', σ) <- typeCheckRuntimePattern pm
    Checked e' (τ, π) lΓ <- traverse (checkEffect p) =<< augmentRuntimeTermPattern pm' (typeCheck e)
    pure $ Checked (Term p $ FunctionLiteral (Bound pm' e')) (TypeAst () $ FunctionLiteralType σ π τ) lΓ
  Annotation (Source (PretypeAnnotation (Term p (TermErasure (Wrap (Source ()) e))) σ)) -> do
    (σ, _) <- kindCheck σ
    case σ of
      (TypeAst () (TypeConstant (TypeVariable x))) -> (! x) <$> kindEnvironment <$> askEnvironment >>= go σ
      (TypeAst () (TypeConstant (TypeGlobalVariable x))) -> (! x) <$> kindGlobalEnvironment <$> askEnvironment >>= go σ
      _ -> quit $ ExpectedNewtype p (flexible σ)
    where
      go :: TypeInfer -> TypeBinding p -> Check p (Checked p TypeUnify)
      go σ (TypeBinding _ _ _ (Named τ)) = do
        Checked e (τ', π) lΓ <- traverse (checkEffect p) =<< typeCheck e
        matchType p (flexible τ) τ'
        pure $ Checked (Term p (TermErasure (Wrap (Core (flexible σ)) e))) (TypeAst () $ Effect (flexible σ) π) lΓ
      go σ (TypeBinding _ _ _ Unnamed) = quit $ ExpectedNewtype p (flexible σ)
  TermErasure (Wrap _ _) -> do
    quit $ ExpectedTypeAnnotation p
  TermErasure (Unwrap (Source ()) (Term _ (Annotation (Source (PretypeAnnotation e σ))))) -> do
    (σ, _) <- kindCheck σ
    case σ of
      (TypeAst () (TypeConstant (TypeVariable x))) -> (! x) <$> kindEnvironment <$> askEnvironment >>= go σ
      (TypeAst () (TypeConstant (TypeGlobalVariable x))) -> (! x) <$> kindGlobalEnvironment <$> askEnvironment >>= go σ
      _ -> quit $ ExpectedNewtype p (flexible σ)
    where
      go :: TypeInfer -> TypeBinding p -> Check p (Checked p TypeUnify)
      go σ (TypeBinding _ _ _ (Named τ)) = do
        Checked e (σ', π) lΓ <- traverse (checkEffect p) =<< typeCheck e
        matchType p (flexible σ) σ'
        pure $ Checked (Term p (TermErasure (Unwrap (Core (flexible σ)) e))) (TypeAst () $ Effect (flexible (flexible τ)) π) lΓ
      go σ (TypeBinding _ _ _ Unnamed) = quit $ ExpectedNewtype p (flexible σ)
  TermErasure (Unwrap _ (Term p _)) -> do
    quit $ ExpectedTypeAnnotation p
  Annotation (Source (TypeAnnotation e τ)) -> do
    Checked e σ lΓ <- typeCheck e
    (τ, _) <- kindCheck τ
    let ς = reLabel $ TypeScheme () $ MonoType $ flexible τ
    (σ', _) <- instantiateLabel p ς
    (σ'', _) <- instantiateLabel p ς
    matchType p σ σ'
    pure $ Checked e σ'' lΓ
  Annotation (Source (PretypeAnnotation e σ')) -> do
    Checked e τ lΓ <- typeCheck e
    (σ, _) <- checkEffect p τ
    σ' <- flexible <$> fst <$> kindCheck σ'
    matchType p σ σ'
    pure $ Checked e τ lΓ
  TermRuntime (BooleanLiteral b) -> do
    pure $ Checked (Term p $ TermRuntime $ BooleanLiteral b) (TypeAst () $ Effect (TypeAst () Boolean) none) useNothing
  TermSugar (If eb et ef) -> do
    Checked eb' ((), π1) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck eb
    Checked et' (σ, π2) lΓ2 <- traverse (checkEffect p) =<< typeCheck et
    Checked ef' (σ', π3) lΓ3 <- traverse (checkEffect p) =<< typeCheck ef
    matchType p σ σ'
    let π = regions [π1, π2, π3]
    pure $ Checked (Term p $ TermSugar $ If eb' et' ef') (TypeAst () $ Effect σ π) (lΓ1 `combine` (lΓ2 `branch` lΓ3))
  TermRuntime (PointerIncrement ep ei (Source ())) -> do
    Checked ep' ((σ, π2), π1) lΓ1 <- traverse (firstM (firstM (checkArray p) <=< checkShared p) <=< checkEffect p) =<< typeCheck ep
    Checked ei' ((κ1, κ2), π3) lΓ2 <- traverse (firstM (checkNumber p) <=< checkEffect p) =<< typeCheck ei
    matchType p κ1 (TypeAst () $ KindSignedness Unsigned)
    matchType p κ2 (TypeAst () $ KindSize Native)
    let π = regions [π1, π3]
    pure $
      Checked
        (Term p $ TermRuntime $ PointerIncrement ep' ei' (Core σ))
        (TypeAst () $ Effect (TypeAst () $ Shared (TypeAst () $ Array σ) π2) π)
        (lΓ1 `combine` lΓ2)
  TermRuntime (Continue e) -> do
    Checked e (σ, π) lΓ <- traverse (checkEffect p) =<< typeCheck e
    τ <- freshPretypeTypeVariable p
    pure $ Checked (Term p $ TermRuntime $ Continue e) (TypeAst () $ Effect (TypeAst () $ Step τ σ) π) lΓ
  TermRuntime (Break e) -> do
    Checked e (τ, π) lΓ <- traverse (checkEffect p) =<< typeCheck e
    σ <- freshPretypeTypeVariable p
    pure $ Checked (Term p $ TermRuntime $ Break e) (TypeAst () $ Effect (TypeAst () $ Step τ σ) π) lΓ
  TermRuntime (Loop e1 (Bound pm e2)) -> do
    (pm, σ) <- typeCheckRuntimePattern pm
    Checked e1 (σ', π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p σ σ'
    Checked e2 ((τ, σ''), π2) lΓ2 <- traverse (firstM (checkStep p) <=< checkEffect p) =<< augmentRuntimeTermPattern pm (typeCheck e2)
    matchType p σ σ''
    capture p unrestricted lΓ2
    let π = regions [π1, π2]
    pure $ Checked (Term p $ TermRuntime $ Loop e1 (Bound pm e2)) (TypeAst () $ Effect τ π) (combine lΓ1 lΓ2)
  TermErasure (IsolatePointer e) -> do
    Checked e ((σ, π2), π) lΓ <- traverse (firstM (firstM (checkArray p) <=< checkShared p) <=< checkEffect p) =<< typeCheck e
    pure $
      Checked
        (Term p $ TermErasure $ IsolatePointer e)
        (TypeAst () $ Effect (TypeAst () $ Shared (TypeAst () $ Pointer σ) π2) π)
        lΓ
  TermSugar (Not e) -> do
    Checked e' ((), π) lΓ <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    pure $ Checked (Term p $ TermSugar $ Not e') (TypeAst () $ Effect (TypeAst () Boolean) π) lΓ
  TermSugar (And e ey) -> do
    Checked e' ((), π1) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked ey' ((), π2) lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck ey
    let π = regions [π1, π2]
    pure $ Checked (Term p $ TermSugar $ And e' ey') (TypeAst () $ Effect (TypeAst () Boolean) π) (lΓ1 `combine` (lΓ2 `branch` useNothing))
  TermSugar (Or e en) -> do
    Checked e' ((), π1) lΓ1 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck e
    Checked en' ((), π2) lΓ2 <- traverse (firstM (checkBoolean p) <=< checkEffect p) =<< typeCheck en
    let π = regions [π1, π2]
    pure $ Checked (Term p $ TermSugar $ Or e' en') (TypeAst () $ Effect (TypeAst () Boolean) π) (lΓ1 `combine` (useNothing `branch` lΓ2))
  TermSugar (Do e1 e2) -> do
    Checked e1' (τ, π1) lΓ1 <- traverse (checkEffect p) =<< typeCheck e1
    matchType p τ (TypeAst () $ Tuple [])
    Checked e2' (σ, π2) lΓ2 <- traverse (checkEffect p) =<< typeCheck e2
    let π = regions [π1, π2]
    pure $ Checked (Term p $ TermSugar $ Do e1' e2') (TypeAst () $ Effect σ π) (lΓ1 `combine` lΓ2)
  TermErasure (Borrow eu (Bound (TypePattern p' α κ) (Bound pm e)) π2) -> do
    -- Shadowing type variables is prohibited
    α' <- flip fresh α . Map.keysSet . kindEnvironment <$> askEnvironment
    pm <- pure $ convertType α' α pm
    e <- pure $ convertType α' α e

    let α = α'

    Checked eu' (τ, π1) lΓ1 <- traverse (firstM (checkUnique p) <=< checkEffect p) =<< typeCheck eu
    (pmσ', ()) <- secondM (checkRegion p) =<< kindCheckPattern SymbolMode (TypePattern p' α κ)
    π2 <- (flexible . fst) <$> (secondM (checkRegion p) =<< kindCheck π2)
    σ <- freshPretypeTypeVariable p
    augmentTypePatternLevel pmσ' $ do
      (pm', (τ', α')) <- secondM (checkShared p) =<< typeCheckRuntimePattern pm
      matchType p τ τ'
      matchType p (TypeAst () $ TypeConstant $ TypeVariable α) α'
      augmentRuntimeTermPattern pm' $ do
        Checked e' (σ', πe) lΓ2 <- traverse (checkEffect p) =<< typeCheck e
        matchType p σ σ'
        ρ <- freshRegionTypeVariable p
        matchType p πe $
          TypeAst () $ TypeBoolean $ TypeOr π2 $ TypeAst () $ TypeBoolean $ TypeAnd ρ $ TypeAst () $ TypeConstant $ TypeVariable α
        let π = regions [π1, π2]
        pure $
          Checked
            (Term p $ TermErasure $ Borrow eu' (Bound (flexible $ toTypePattern pmσ') (Bound pm' e')) π2)
            (TypeAst () $ Effect (TypeAst () (Tuple [σ, TypeAst () $ Unique τ])) π)
            (lΓ1 `combine` lΓ2)

typeCheckScheme :: Mode -> TermSchemeSource p -> Check p (CheckedScheme p TypeSchemeUnify)
typeCheckScheme mode (TermScheme p (TypeAbstraction (Bound (TypePattern p' α κpm) e))) = do
  -- Shadowing type variables is prohibited
  vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
  let α' = fresh vars α
  let pm = TypePattern p' α' κpm
  e <- pure $ convertType α' α e

  (pm', _) <- kindCheckPattern mode pm

  augmentTypePatternLevel pm' $ do
    CheckedScheme e' σ' lΓ <- typeCheckScheme mode e
    pure $
      CheckedScheme
        (TermScheme p $ TypeAbstraction (Bound (flexible $ toTypePattern pm') e'))
        (TypeScheme () $ TypeForall (Bound (flexible $ toTypePattern pm') σ'))
        lΓ
typeCheckScheme _ (TermScheme p (MonoTerm e (Source ()))) = do
  Checked e σ lΓ <- typeCheck e
  pure $ CheckedScheme (TermScheme p $ MonoTerm e (Core σ)) (TypeScheme () $ MonoType σ) lΓ

defaultType p μ = do
  μ'@(TypeAst () μ) <- finish μ
  case μ of
    Representation -> pure $ TypeAst () $ KindRuntime $ PointerRep
    Size -> pure $ TypeAst () $ KindSize $ Int
    Signedness -> pure $ TypeAst () $ KindSignedness $ Signed
    Region -> pure $ TypeAst () $ TypeConstant World
    Multiplicity -> pure unrestricted
    Label -> pure $ TypeAst () $ AmbiguousLabel
    Transparency -> pure $ TypeAst () $ Transparent
    (TypeLogical v) -> absurd v
    _ -> quit $ AmbiguousType p μ'

unsolved :: TypeAlgebra u => Map TypeLogical (TypeLogicalState p) -> u Core () TypeLogical -> Map TypeLogical (p, TypeUnify, Level)
unsolved vars σ = Map.unions (lookup <$> freeTypeLogical σ)
  where
    lookup x | LinkType σ <- vars ! x = unsolved vars σ
    lookup x | UnboundType p κ l <- vars ! x = Map.singleton x (p, κ, l)
    lookup _ = Map.empty

unsolvedVariables :: TypeAlgebra u => Map TypeLogical (TypeLogicalState p) -> u Ast.Common.Core () TypeLogical -> [TypeLogical]
unsolvedVariables vars σ = Map.keys (unsolved vars σ)

zonk :: TypeAlgebra u => Map TypeLogical (TypeLogicalState p) -> u Core () TypeLogical -> u Core () TypeLogical
zonk vars σ = runIdentity $ zonkType (Identity . get) σ
  where
    get x = case vars ! x of
      UnboundType _ _ _ -> TypeAst () (TypeLogical x)
      LinkType σ -> zonk vars σ

finish :: TypeAlgebra u => u Core () TypeLogical -> Check p (u Core () Void)
finish σ = zonkType go σ
  where
    go x =
      (! x) <$> typeLogicalMap <$> getState >>= \case
        LinkType σ -> finish σ
        UnboundType p κ _ -> do
          σ <- defaultType p κ
          modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkType (flexible σ)) $ typeLogicalMap state}
          pure (flexible σ)

finishBooleans p = do
  solveBooleans
  sat <- booleans <$> getState
  case sat of
    [] -> pure ()
    σs -> quit $ TypeBooleanMismatch p $ map (\(σ, τ) -> TypeAst () $ TypeBoolean $ TypeXor σ τ) σs

topologicalBoundsSort :: Map TypeLogical (TypeLogicalState p) -> [TypeLogical] -> [TypeLogical]
topologicalBoundsSort vars = runIdentity . sortTopological id quit (Identity . children)
  where
    quit x = error $ "unexpected cycle: " ++ show x
    children x = case vars ! x of
      LinkType σ -> unsolvedVariables vars σ
      UnboundType _ κ _ -> unsolvedVariables vars κ

generalizable mode x = do
  level <- levelCounter <$> getState
  (! x) <$> typeLogicalMap <$> getState >>= \case
    UnboundType p κ level' -> do
      TypeAst () μ <- reconstruct p κ
      case μ of
        _ | level >= level' -> pure False
        Top -> pure False
        Kind _ _ | InlineMode <- mode -> pure True
        Kind _ (TypeAst () Opaque) -> pure False
        Kind _ (TypeAst () Transparent) -> pure True
        σ -> error $ "generalization error " ++ show σ
    LinkType _ -> error "generalization error"

generalizeExact _ [] e = pure e
generalizeExact scope ((n, x) : remaining) e = do
  e <- generalizeExact scope remaining e
  (! x) <$> typeLogicalMap <$> getState >>= \case
    UnboundType p κ _ -> do
      ( \f -> do
          modifyState $ \state ->
            state
              { typeLogicalMap = f $ typeLogicalMap state
              }
        )
        $ \σΓ -> Map.insert x (LinkType $ TypeAst () $ TypeConstant $ TypeVariable $ TypeIdentifier n) σΓ
      pure (scope p n κ e)
    _ -> error "generalization error"

-- todo refactor this
generalize :: Mode -> (TermUnify p, TypeUnify) -> Check p (TermSchemeUnify p, TypeSchemeUnify)
generalize mode (e@(Term p _), σ) = do
  logical <- typeLogicalMap <$> getState
  vars <- filterM (generalizable mode) $ topologicalBoundsSort logical (unsolvedVariables logical σ)
  used <- usedVars <$> getState
  let names = filter (\x -> x `Set.notMember` used) $ temporaries uppers
  generalizeExact scope (zip names vars) (TermScheme p $ MonoTerm e (Core σ), TypeScheme () $ MonoType σ)
  where
    scope p n κ (e, σ) =
      ( TermScheme p $ TypeAbstraction (Bound (TypePattern () (TypeIdentifier n) κ) e),
        TypeScheme () $ TypeForall (Bound (TypePattern () (TypeIdentifier n) κ) σ)
      )

typeCheckGlobalAuto ::
  Mode ->
  TermSource p ->
  Check p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalAuto mode e@(Term p _) = do
  Checked e σ _ <- leveled $ typeCheck e
  finishBooleans p
  (e, ς) <- generalize mode (e, σ)
  e <- finish e
  ς <- finish ς
  pure (e, ς)

typeCheckGlobalSemi ::
  Mode -> TermSchemeSource p -> Check p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalSemi mode e@(TermScheme p _) = do
  CheckedScheme e ς _ <- leveled $ typeCheckScheme mode e
  finishBooleans p
  ς <- finish ς
  e <- finish e
  pure (e, ς)

typeCheckGlobalManual ::
  forall p.
  Mode ->
  TermSchemeSource p ->
  TypeSchemeSource p ->
  Check p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalManual mode e ς = do
  (ς, _) <- kindCheckScheme mode ς
  e <- go ς e
  e <- finish e
  pure (e, ς)
  where
    go :: TypeSchemeInfer -> TermSchemeSource p -> Check p (TermSchemeUnify p)
    go (TypeScheme () (MonoType σ)) (TermScheme p (MonoTerm e (Source ()))) = leveled $ do
      Checked e σ' _ <- typeCheck e
      matchType p (flexible σ) σ'
      finishBooleans p
      pure (TermScheme p $ MonoTerm e (Core $ flexible σ))
    go
      (TypeScheme () (TypeForall (Bound (TypePattern () x κ) ς)))
      (TermScheme _ (TypeAbstraction (Bound (TypePattern p x' κ') e))) = do
        (κ', _) <- kindCheck κ'
        matchType p (flexible κ) (flexible κ')
        e' <- augmentKindEnvironment p x' (flexible κ) minBound $ go (convertType x' x ς) e
        pure $ TermScheme p $ TypeAbstraction (Bound (TypePattern () x' (flexible κ)) e')
    go _ (TermScheme p _) = quit $ MismatchedTypeLambdas p

typeCheckGlobalScope ::
  forall p.
  Mode ->
  TermSource p ->
  TypeSchemeSource p ->
  Check p (TermSchemeInfer p, TypeSchemeInfer)
typeCheckGlobalScope mode e@(Term p _) ς = do
  (ς, _) <- kindCheckScheme mode ς
  e <- go ς
  e <- finish e
  pure (e, ς)
  where
    go :: TypeSchemeInfer -> Check p (TermSchemeUnify p)
    go (TypeScheme () (MonoType σ)) = leveled $ do
      Checked e σ' _ <- typeCheck e
      matchType p (flexible σ) σ'
      finishBooleans p
      pure (TermScheme p $ MonoTerm e (Core $ flexible σ))
    go
      (TypeScheme () (TypeForall (Bound (TypePattern () x κ) ς))) =
        do
          e' <- augmentKindEnvironment p x (flexible κ) minBound $ go ς
          pure $ TermScheme p $ TypeAbstraction (Bound (TypePattern () x (flexible κ)) e')

typeCheckGlobalSyn :: TypeSource p -> Check p TypeInfer
typeCheckGlobalSyn σ = do
  (σ, _) <- kindCheck σ
  pure σ

typeCheckGlobalNew :: TypeSource p -> TypeSource p -> Check p (TypeInfer, TypeInfer)
typeCheckGlobalNew σ κ@(TypeAst p _) = do
  (κ', _) <- kindCheck κ
  checkPretype p (flexible κ')
  (σ, κ) <- kindCheck σ
  matchType p κ (flexible κ')
  pure (σ, κ')

typeCheckGlobalForward :: TypeSchemeSource p -> Check p TypeSchemeInfer
typeCheckGlobalForward ς = do
  (ς, _) <- kindCheckScheme SymbolMode ς
  pure ς

typeCheckGlobalNewForward :: TypeSource p -> Check p TypeInfer
typeCheckGlobalNewForward κ@(TypeAst p _) = do
  (κ, _) <- kindCheck κ
  checkPretype p (flexible κ)
  pure κ
