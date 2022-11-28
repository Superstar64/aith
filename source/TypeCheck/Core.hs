module TypeCheck.Core where

import Ast.Term
import Ast.Type
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT, withReaderT)
import Control.Monad.Trans.State.Strict (StateT, get, modify, put, runStateT)
import Data.Foldable (fold)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- levels are inspired from "How OCaml type checker works -- or what polymorphism and garbage collection have in common"
-- however, rather then using levels for let generalization, levels here are used for skolemization
-- where each level can be thought of as a ∀α ∃ βγδ... qualifier in unification under a mixed prefix
newtype Level = Level Int deriving (Eq, Ord, Show)

instance Bounded Level where
  minBound = Level 0
  maxBound = Level maxBound

data TypeError p
  = UnknownIdentifier p TermIdentifier
  | UnknownGlobalIdentifier p TermGlobalIdentifier
  | UnknownTypeIdentifier p TypeIdentifier
  | UnknownTypeGlobalIdentifier p TypeGlobalIdentifier
  | InvalidUsage p TermIdentifier
  | TypeMismatch p TypeUnify TypeUnify
  | TypeMisrelation p TypeSub TypeSub
  | TypeOccursCheck p TypeLogical TypeUnify
  | AmbiguousType p TypeInfer
  | EscapingSkolemType p TypeIdentifier TypeUnify
  | EscapingSkolemTypeGlobal p TypeGlobalIdentifier TypeUnify
  | CaptureLinear p TermIdentifier
  | ExpectedTypeAnnotation p
  | ExpectedFunctionLiteral p
  | NoCommonMeet p TypeSub TypeSub
  | MismatchedTypeLambdas p
  | ExpectedTypeAbstraction p
  | ExpectedPlainType p
  | IncorrectRegionBounds p
  | NotTypable p
  | ExpectedSubtypable p
  | ExpectedNewtype p TypeUnify
  | ExpectedFullAnnotation p
  deriving (Show)

newtype Check p a = Check {runChecker'' :: ReaderT (CheckEnvironment p) (StateT (CheckState p) (Either (TypeError p))) a} deriving (Functor, Applicative, Monad)

runChecker' c = runStateT . runReaderT (runChecker'' c)

runChecker :: Check p a -> CheckEnvironment p -> CheckState p -> Either (TypeError p) a
runChecker c = (fmap fst .) . runChecker' c

data TermBinding p = TermBinding
  { termPosition :: p,
    termMultiplicity :: TypeUnify,
    termType :: TypeSchemeUnify
  }
  deriving (Show, Functor)

data NominalBinding
  = Unnamed
  | Named TypeInfer
  deriving (Show)

data TypeBinding p
  = TypeBinding p TypeUnify (Set TypeSub) Level NominalBinding
  | LinkTypeBinding TypeInfer
  deriving (Show, Functor)

data CheckEnvironment p = CheckEnvironment
  { typeEnvironment :: Map TermIdentifier (TermBinding p),
    kindEnvironment :: Map TypeIdentifier (TypeBinding p),
    typeGlobalEnvironment :: Map TermGlobalIdentifier (TermBinding p),
    kindGlobalEnvironment :: Map TypeGlobalIdentifier (TypeBinding p)
  }
  deriving (Functor, Show)

data TypeLogicalState p
  = UnboundTypeLogical p TypeUnify [TypeUnify] (Maybe TypeSub) Level
  | LinkTypeLogical TypeUnify
  deriving (Show, Functor)

-- todo use int maps here
data CheckState p = CheckState
  { typeLogicalMap :: Map TypeLogical (TypeLogicalState p),
    freshTypeCounter :: Int,
    levelCounter :: Int,
    usedVars :: Set String
  }
  deriving (Functor, Show)

quit e = Check $ lift $ lift $ Left e

emptyEnvironment = CheckEnvironment Map.empty Map.empty Map.empty Map.empty

askEnvironment = Check ask

withEnvironment f (Check r) = Check $ withReaderT f r

lookupTypeEnviroment :: TermIdentifier -> Check p (Maybe (TermBinding p))
lookupTypeEnviroment x = do
  xΓ <- Check ask
  pure $ Map.lookup x (typeEnvironment xΓ)

lookuptypeGlobalEnvironment :: TermGlobalIdentifier -> Check p (Maybe (TermBinding p))
lookuptypeGlobalEnvironment x = do
  xΓ <- Check ask
  pure $ Map.lookup x (typeGlobalEnvironment xΓ)

augmentTypeEnvironment :: TermIdentifier -> p -> TypeUnify -> TypeSchemeUnify -> Check p a -> Check p a
augmentTypeEnvironment x p l σ = modifyTypeEnvironment (Map.insert x (TermBinding p l σ))
  where
    modifyTypeEnvironment f (Check r) = Check $ withReaderT (\env -> env {typeEnvironment = f (typeEnvironment env)}) r

lookupKindEnvironment :: TypeIdentifier -> Check p (Maybe (TypeBinding p))
lookupKindEnvironment x = do
  xΓ <- Check ask
  pure $ Map.lookup x (kindEnvironment xΓ)

lookupKindGlobalEnvironment x = do
  xΓ <- Check ask
  pure $ Map.lookup x (kindGlobalEnvironment xΓ)

indexKindEnvironment :: TypeIdentifier -> Check p (TypeBinding p)
indexKindEnvironment x = do
  xΓ <- Check ask
  if x `Map.notMember` kindEnvironment xΓ
    then error $ "Bad Type Variable " ++ show x
    else pure $ kindEnvironment xΓ ! x

indexKindGlobalEnvironment x = do
  xΓ <- Check ask
  if x `Map.notMember` kindGlobalEnvironment xΓ
    then error $ "Bad Type Variable " ++ show x
    else pure $ kindGlobalEnvironment xΓ ! x

lowerTypeBounds :: TypeSub -> Check p (Set TypeSub)
lowerTypeBounds (TypeVariable x) = do
  indexKindEnvironment x >>= \case
    TypeBinding _ _ π _ _ -> do
      pure π
    LinkTypeBinding (TypeAst _ (TypeSub σ)) -> lowerTypeBounds σ
    LinkTypeBinding _ -> error "unexpected subtypable"
lowerTypeBounds (TypeGlobalVariable x) = do
  indexKindGlobalEnvironment x >>= \case
    TypeBinding _ _ π _ _ -> do
      pure π
    LinkTypeBinding (TypeAst _ (TypeSub σ)) -> lowerTypeBounds σ
    LinkTypeBinding _ -> error "unexpected subtypable"
lowerTypeBounds World = pure (Set.singleton World)
lowerTypeBounds Linear = pure (Set.singleton Linear)
lowerTypeBounds Unrestricted = pure (Set.fromList [Linear, Unrestricted])

modifyKindEnvironment f (Check r) = Check $ withReaderT (\env -> env {kindEnvironment = f (kindEnvironment env)}) r

-- todo assertions to avoid shadowing
augmentKindEnvironment p x κ π lev f = do
  πs <- Set.insert (TypeVariable x) <$> closure π
  modifyKindEnvironment (Map.insert x (TypeBinding p κ πs lev Unnamed)) f
  where
    closure :: Set TypeSub -> Check p (Set TypeSub)
    closure x = fold <$> traverse lowerTypeBounds (Set.toList x)

augmentKindUnify occurs p x = modifyKindEnvironment (Map.insert x (TypeBinding p κ π (if occurs then minBound else maxBound) Unnamed))
  where
    κ = error "kind used during unification"
    π = error "bounds used during unification"

augmentTypePatternLevel (TypePatternIntermediate p x κ π) f = do
  enterLevel
  useTypeVar x
  lev <- Level <$> currentLevel
  f' <- augmentKindEnvironment p x (flexible κ) (Set.fromList π) lev f
  leaveLevel
  pure f'

emptyState = CheckState Map.empty 0 0 Set.empty

getState = Check $ lift $ get

putState state = Check $ lift $ put state

modifyState f = Check $ lift $ modify f

getTypeLogicalMap = typeLogicalMap <$> getState

modifyTypeLogicalMap f = do
  modifyState $ \state ->
    state
      { typeLogicalMap = f $ typeLogicalMap state
      }

modifyLevelCounter :: (Int -> Int) -> Check p ()
modifyLevelCounter f = do
  modifyState $ \state -> state {levelCounter = f $ levelCounter state}

enterLevel = modifyLevelCounter (+ 1)

-- todo lower levels of all type variables in state
leaveLevel = modifyLevelCounter (subtract 1)

currentLevel = levelCounter <$> getState

freshTypeVariableRaw :: p -> TypeUnify -> [TypeUnify] -> Maybe TypeSub -> Level -> Check p TypeLogical
freshTypeVariableRaw p κ lower upper lev = do
  v <- TypeLogicalRaw <$> newFreshType
  insertTypeLogicalMap v
  pure $ v
  where
    newFreshType = do
      state <- getState
      let i = freshTypeCounter state
      putState state {freshTypeCounter = i + 1}
      pure i
    insertTypeLogicalMap x = do
      state <- getState
      putState state {typeLogicalMap = Map.insert x (UnboundTypeLogical p κ lower upper lev) $ typeLogicalMap state}

freshKindVariableRaw p μ lev = freshTypeVariableRaw p μ [] Nothing lev

indexTypeLogicalMap :: TypeLogical -> Check p (TypeLogicalState p)
indexTypeLogicalMap x = do
  vars <- typeLogicalMap <$> getState
  if x `Map.notMember` vars
    then error $ "Bad Type Logical " ++ show x
    else pure $ vars ! x

useTypeVar :: TypeIdentifier -> Check p ()
useTypeVar (TypeIdentifier x) = do
  modifyState $ \state -> state {usedVars = Set.insert x $ usedVars state}
