{-# LANGUAGE UndecidableInstances #-}

module TypeCheck.Core where

import Ast.Common
import Ast.Kind
import Ast.Sort
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
import Data.Traversable (for)

data Multiplicity = Linear | Unrestricted | Automatic TypeUnify deriving (Show)

-- levels are inspired from "How OCaml type checker works -- or what polymorphism and garbage collection have in common"
-- however, rather then using levels for let generalization, levels here are used for skolemization
-- where each level can be thought of as a ∀α ∃ βγδ... qualifier in unification under a mixed prefix
newtype Level = Level Int deriving (Eq, Ord, Show)

instance Bounded Level where
  minBound = Level 0
  maxBound = Level maxBound

data TypeError p
  = UnknownIdentifier p TermIdentifier
  | UnknownTypeIdentifier p TypeIdentifier
  | UnknownKindIdentifier p KindIdentifier
  | InvalidUsage p TermIdentifier
  | TypeMismatch p TypeUnify TypeUnify
  | KindMismatch p KindUnify KindUnify
  | SortMismatch p Sort Sort
  | TypeOccursCheck p TypeLogical TypeUnify
  | KindOccursCheck p KindLogical KindUnify
  | AmbiguousType p TypeLogical
  | AmbiguousKind p KindLogical
  | EscapingSkolemType p TypeIdentifier TypeUnify
  | EscapingSkolemKind p KindIdentifier KindUnify
  | CaptureLinear p TermIdentifier
  | ExpectedTypeAnnotation p
  | ConstraintMismatch p Constraint TypeUnify
  | ConstraintKindError p Constraint KindUnify
  | ExpectedFunctionLiteral p
  | ExpectedTypeVariable p
  | TypeVariableOnlySuported p
  | NoCommonMeet p TypeIdentifier TypeIdentifier
  | MismatchedTypeLambdas p
  | ExpectedFullAnnotation p
  deriving (Show)

newtype Core p a = Core {runCore' :: ReaderT (CoreEnvironment p) (StateT (CoreState p) (Either (TypeError p))) a} deriving (Functor, Applicative, Monad)

-- todo define new types for environments

data CoreEnvironment p = CoreEnvironment
  { typeEnvironment :: Map TermIdentifier (p, Multiplicity, TypeSchemeUnify),
    kindEnvironment :: Map TypeIdentifier (p, KindUnify, Set Constraint, Set TypeIdentifier, Level),
    sortEnvironment :: Map KindIdentifier (p, Sort, Level)
  }
  deriving (Functor, Show)

data TypeLogicalState p
  = UnboundTypeLogical p KindUnify (Set Constraint) [TypeUnify] (Maybe TypeIdentifier) Level
  | LinkTypeLogical TypeUnify
  deriving (Show, Functor)

data KindLogicalState p
  = UnboundKindLogical p Sort Level
  | LinkKindLogical KindUnify
  deriving (Show, Functor)

data CoreState p = CoreState
  { typeLogicalMap :: Map TypeLogical (TypeLogicalState p),
    kindLogicalMap :: Map KindLogical (KindLogicalState p),
    freshTypeCounter :: Int,
    freshKindCounter :: Int,
    levelCounter :: Int,
    usedVars :: Set String
  }
  deriving (Functor, Show)

lookupTypeEnviroment :: TermIdentifier -> Core p (Maybe (p, Multiplicity, TypeSchemeUnify))
lookupTypeEnviroment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (typeEnvironment xΓ)

indexTypeEnviroment :: TermIdentifier -> Core p (p, Multiplicity, TypeSchemeUnify)
indexTypeEnviroment x = do
  xΓ <- Core ask
  pure $ typeEnvironment xΓ ! x

augmentTypeEnvironment :: TermIdentifier -> p -> Multiplicity -> TypeSchemeUnify -> Core p a -> Core p a
augmentTypeEnvironment x p l σ = modifyTypeEnvironment (Map.insert x (p, l, σ))
  where
    modifyTypeEnvironment f (Core r) = Core $ withReaderT (\env -> env {typeEnvironment = f (typeEnvironment env)}) r

lookupKindEnvironment :: TypeIdentifier -> Core p (Maybe (p, KindUnify, Set Constraint, Set TypeIdentifier, Level))
lookupKindEnvironment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (kindEnvironment xΓ)

indexKindEnvironment :: TypeIdentifier -> Core p (p, KindUnify, Set Constraint, Set TypeIdentifier, Level)
indexKindEnvironment x = do
  xΓ <- Core ask
  pure $ kindEnvironment xΓ ! x

lookupSortEnvironment :: KindIdentifier -> Core p (Maybe (p, Sort, Level))
lookupSortEnvironment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (sortEnvironment xΓ)

indexSortEnvironment :: KindIdentifier -> Core p (p, Sort, Level)
indexSortEnvironment x = do
  xΓ <- Core ask
  pure $ sortEnvironment xΓ ! x

modifyKindEnvironment f (Core r) = Core $ withReaderT (\env -> env {kindEnvironment = f (kindEnvironment env)}) r

-- todo assertions to avoid shadowing
augmentKindEnvironment x p κ c π lev e = do
  πs <- Set.insert x <$> closure π
  modifyKindEnvironment (Map.insert x (p, κ, c, πs, lev)) e
  where
    closure :: Set TypeIdentifier -> Core p (Set TypeIdentifier)
    closure x = do
      fold <$> traverse lookup (Set.toList x)
      where
    lookup x = do
      (_, _, _, x, _) <- indexKindEnvironment x
      pure x

augmentKindOccurs p x κ = modifyKindEnvironment (Map.insert x (p, κ, c, π, minBound))
  where
    c = error "constraints used during unification"
    π = error "bottom used during unification"

augmentTypePatternLevel (Pattern p x κ) c π e = do
  useTypeVar x
  lev <- Level <$> currentLevel
  augmentKindEnvironment x p κ c π lev e

augmentTypePatternBottom (Pattern p x κ) e = do
  useTypeVar x
  modifyKindEnvironment (Map.insert x (p, κ, c, π, sk)) e
  where
    c = error $ "constraints used during kind checking" ++ show x
    π = error $ "bottom used during kind checking" ++ show x
    sk = error $ "level usage during kind checking " ++ show x

augmentKindPatternBottom (Pattern p x μ) e = do
  useKindVar x
  augmentSortEnvironment x p μ (error $ "level usage during sort checking " ++ show x) e

augmentKindPatternLevel (Pattern p x μ) e = do
  useKindVar x
  lev <- Level <$> currentLevel
  augmentSortEnvironment x p μ lev e

augmentSortEnvironment :: KindIdentifier -> p -> Sort -> Level -> Core p a -> Core p a
augmentSortEnvironment x p μ sk = modifySortEnvironment (Map.insert x (p, μ, sk))
  where
    modifySortEnvironment f (Core r) = Core $ withReaderT (\env -> env {sortEnvironment = f (sortEnvironment env)}) r

freshTypeVariableRaw :: p -> KindUnify -> Set Constraint -> [TypeUnify] -> Maybe TypeIdentifier -> Level -> Core p TypeLogical
freshTypeVariableRaw p κ c lower upper lev = do
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
      putState state {typeLogicalMap = Map.insert x (UnboundTypeLogical p κ c lower upper lev) $ typeLogicalMap state}

freshKindVariableRaw :: p -> Sort -> Level -> Core p KindLogical
freshKindVariableRaw p μ lev = do
  v <- KindLogicalRaw <$> newFreshKind
  insertKindLogicalMap v
  pure $ v
  where
    newFreshKind = do
      state <- getState
      let i = freshKindCounter state
      putState state {freshKindCounter = i + 1}
      pure i
    insertKindLogicalMap x = do
      state <- getState
      putState state {kindLogicalMap = Map.insert x (UnboundKindLogical p μ lev) $ kindLogicalMap state}

quit e = Core $ lift $ lift $ Left e

emptyEnvironment = CoreEnvironment Map.empty Map.empty Map.empty

emptyState = CoreState Map.empty Map.empty 0 0 0 Set.empty

runCore :: Core p a -> CoreEnvironment p -> CoreState p -> Either (TypeError p) a
runCore c = (fmap fst .) . runStateT . runReaderT (runCore' c)

askEnvironment = Core $ ask

withEnvironment :: (CoreEnvironment p -> CoreEnvironment p) -> Core p a -> Core p a
withEnvironment f (Core r) = Core $ withReaderT f r

getState = Core $ lift $ get

putState state = Core $ lift $ put state

modifyState f = Core $ lift $ modify f

modifyLevelCounter :: (Int -> Int) -> Core p ()
modifyLevelCounter f = do
  modifyState $ \state -> state {levelCounter = f $ levelCounter state}

ambigousTypeCheck variables = do
  lev <- Level <$> currentLevel
  vars <- getTypeLogicalMap
  for (Map.toList vars) $ \case
    (x, (UnboundTypeLogical p _ _ _ _ lev')) -> do
      if lev' > lev && x `Set.notMember` variables
        then quit $ AmbiguousType p x
        else pure ()
    (_, LinkTypeLogical _) -> pure ()

ambigousKindCheck variables = do
  lev <- Level <$> currentLevel
  vars <- getKindLogicalMap
  for (Map.toList vars) $ \case
    (x, (UnboundKindLogical p _ lev')) -> do
      if lev' > lev && x `Set.notMember` variables
        then quit $ AmbiguousKind p x
        else pure ()
    (_, LinkKindLogical _) -> pure ()

enterLevel = modifyLevelCounter (+ 1)

leaveLevel = modifyLevelCounter (subtract 1)

currentLevel = levelCounter <$> getState

indexTypeLogicalMap :: TypeLogical -> Core p (TypeLogicalState p)
indexTypeLogicalMap x = do
  vars <- typeLogicalMap <$> getState
  if x `Map.notMember` vars
    then error $ "Bad Type Variable " ++ show x
    else pure $ vars ! x

indexKindLogicalMap :: KindLogical -> Core p (KindLogicalState p)
indexKindLogicalMap x = do
  vars <- kindLogicalMap <$> getState
  if x `Map.notMember` vars
    then error $ "Bad Kind Variable" ++ show x
    else pure $ vars ! x

getTypeLogicalMap = typeLogicalMap <$> getState

modifyTypeLogicalMap f = do
  modifyState $ \state ->
    state
      { typeLogicalMap = f $ typeLogicalMap state
      }

getKindLogicalMap = kindLogicalMap <$> getState

modifyKindLogicalMap f = do
  modifyState $ \state ->
    state
      { kindLogicalMap = f $ kindLogicalMap state
      }

useTypeVar :: TypeIdentifier -> Core p ()
useTypeVar (TypeIdentifier x) = do
  modifyState $ \state -> state {usedVars = Set.insert x $ usedVars state}

useKindVar :: KindIdentifier -> Core p ()
useKindVar (KindIdentifier x) = do
  modifyState $ \state -> state {usedVars = Set.insert x $ usedVars state}
