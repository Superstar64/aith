{-# LANGUAGE UndecidableInstances #-}

module TypeCheck.Core where

import Ast.Common
import Ast.Kind
import Ast.Sort
import Ast.Type
import Control.Monad.Reader (ReaderT, ask, runReaderT, withReaderT)
import Control.Monad.State.Strict (StateT, get, put, runStateT)
import Control.Monad.Trans (lift)
import Misc.MonoidMap (Map, (!))
import qualified Misc.MonoidMap as Map
import TypeCheck.Substitute

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
  | TypeOccursCheck p TypeLogicalRaw TypeUnify
  | KindOccursCheck p KindLogicalRaw KindUnify
  | AmbiguousType p TypeLogicalRaw
  | AmbiguousKind p KindLogicalRaw
  | EscapingSkolemType p TypeIdentifier TypeUnify
  | EscapingSkolemKind p KindIdentifier KindUnify
  | CaptureLinear p TermIdentifier
  | ExpectedTypeAnnotation p
  | ConstraintMismatch p Constraint TypeUnify [TypeUnify]
  | ConstraintKindError p Constraint KindUnify [KindUnify]
  | ExpectedFunctionLiteral p
  deriving (Show)

lookupTypeEnviroment :: TermIdentifier -> Core p (Maybe (p, Multiplicity, TypeSchemeUnify))
lookupTypeEnviroment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (typeEnvironment xΓ)

augmentTypeEnvironment :: TermIdentifier -> p -> Multiplicity -> TypeSchemeUnify -> Core p a -> Core p a
augmentTypeEnvironment x p l σ = modifyTypeEnvironment (Map.insert x (p, l, σ))
  where
    modifyTypeEnvironment f (Core r) = Core $ withReaderT (\env -> env {typeEnvironment = f (typeEnvironment env)}) r

lookupKindEnvironment :: TypeIdentifier -> Core p (Maybe (p, KindUnify, Map Constraint [TypeUnify], Level))
lookupKindEnvironment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (kindEnvironment xΓ)

lookupSortEnvironment :: KindIdentifier -> Core p (Maybe (p, Sort, Level))
lookupSortEnvironment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (sortEnvironment xΓ)

augmentKindEnvironment :: TypeIdentifier -> p -> KindUnify -> Map Constraint [TypeUnify] -> Level -> Core p a -> Core p a
augmentKindEnvironment x p κ c sk = modifyKindEnvironment (Map.insert x (p, κ, c, sk))
  where
    modifyKindEnvironment f (Core r) = Core $ withReaderT (\env -> env {kindEnvironment = f (kindEnvironment env)}) r

augmentSortEnvironment :: KindIdentifier -> p -> Sort -> Level -> Core p a -> Core p a
augmentSortEnvironment x p μ sk = modifySortEnvironment (Map.insert x (p, μ, sk))
  where
    modifySortEnvironment f (Core r) = Core $ withReaderT (\env -> env {sortEnvironment = f (sortEnvironment env)}) r

insertEquation :: Equation p -> Core p ()
insertEquation eq = modifyEquations (eq :)

freshTypeVariableRaw :: p -> KindUnify -> Map Constraint [TypeUnify] -> Level -> Core p TypeLogicalRaw
freshTypeVariableRaw p κ c lev = do
  v <- TypeLogicalRaw <$> newFreshType
  insertTypeVariableMap v
  pure $ v
  where
    newFreshType = do
      state <- getState
      let i = freshTypeCounter state
      putState state {freshTypeCounter = i + 1}
      pure i
    insertTypeVariableMap x = do
      state <- getState
      putState state {typeVariableMap = Map.insert x (p, κ, c, lev) $ typeVariableMap state}

freshKindVariableRaw :: p -> Sort -> Level -> Core p KindLogicalRaw
freshKindVariableRaw p μ lev = do
  v <- KindLogicalRaw <$> newFreshKind
  insertKindVariableMap v
  pure $ v
  where
    newFreshKind = do
      state <- getState
      let i = freshKindCounter state
      putState state {freshKindCounter = i + 1}
      pure i
    insertKindVariableMap x = do
      state <- getState
      putState state {kindVariableMap = Map.insert x (p, μ, lev) $ kindVariableMap state}

quit e = Core $ lift $ lift $ Left e

data CoreEnvironment p = CoreEnvironment
  { typeEnvironment :: Map TermIdentifier (p, Multiplicity, TypeSchemeUnify),
    kindEnvironment :: Map TypeIdentifier (p, KindUnify, Map Constraint [TypeUnify], Level),
    sortEnvironment :: Map KindIdentifier (p, Sort, Level)
  }
  deriving (Functor, Show)

emptyEnvironment = CoreEnvironment Map.empty Map.empty Map.empty

data CoreState p = CoreState
  { typeVariableMap :: Map TypeLogicalRaw (p, KindUnify, Map Constraint [TypeUnify], Level),
    kindVariableMap :: Map KindLogicalRaw (p, Sort, Level),
    freshTypeCounter :: Int,
    freshKindCounter :: Int,
    equations :: [Equation p],
    levelCounter :: Int
  }
  deriving (Functor, Show)

emptyState = CoreState Map.empty Map.empty 0 0 [] 0

newtype Core p a = Core {runCore' :: ReaderT (CoreEnvironment p) (StateT (CoreState p) (Either (TypeError p))) a} deriving (Functor, Applicative, Monad)

runCore c = runStateT . runReaderT (runCore' c)

askEnvironment = Core $ ask

modifyEnvironment :: (CoreEnvironment p -> CoreEnvironment p) -> Core p a -> Core p a
modifyEnvironment f (Core r) = Core $ withReaderT f r

getState = Core $ get

putState state = Core $ put state

modifyLevelCounter :: (Int -> Int) -> Core p ()
modifyLevelCounter f = do
  state <- getState
  putState state {levelCounter = f $ levelCounter state}

enterLevel = modifyLevelCounter (+ 1)

leaveLevel = modifyLevelCounter (subtract 1)

currentLevel = levelCounter <$> getState

getEquations = equations <$> getState

modifyEquations f = do
  state <- getState
  putState state {equations = f $ equations state}

indexTypeVariableMap x = (! x) <$> typeVariableMap <$> getState

insertTypeVariableMapConstraint x c σs = do
  state <- getState
  putState $ state {typeVariableMap = Map.adjust (\(p, κ, cs, lev) -> (p, κ, Map.insert c σs cs, lev)) x $ typeVariableMap state}

updateTypeLevel x lev = do
  state <- getState
  putState state {typeVariableMap = Map.adjust (\(p, κ, c, _) -> (p, κ, c, lev)) x $ typeVariableMap state}

indexKindVariableMap x = (! x) <$> kindVariableMap <$> getState

updateKindLevel x lev = do
  state <- getState
  putState state {kindVariableMap = Map.adjust (\(p, μ, _) -> (p, μ, lev)) x $ kindVariableMap state}

getTypeVariableMap = typeVariableMap <$> getState

modifyTypeVariableMap f = do
  state <- getState
  putState
    state
      { typeVariableMap = f $ typeVariableMap state
      }

removeTypeVariable x = do
  state <- getState
  putState state {typeVariableMap = Map.delete x $ typeVariableMap state}

getKindVariableMap = kindVariableMap <$> getState

modifyKindVariableMap f = do
  state <- getState
  putState
    state
      { kindVariableMap = f $ kindVariableMap state
      }

removeKindVariable x = do
  state <- getState
  putState state {kindVariableMap = Map.delete x $ kindVariableMap state}
