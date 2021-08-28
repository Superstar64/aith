{-# LANGUAGE UndecidableInstances #-}

module Language.TypeCheck.Core where

import Control.Monad.Reader (ReaderT, ask, runReaderT, withReaderT)
import Control.Monad.State (StateT, get, put, runStateT)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (WriterT)
import Data.Functor.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Set (Set)
import Data.Void (Void, absurd)
import Language.Ast.Common
import Language.Ast.Multiplicity
import Language.Ast.Sort
import Language.TypeCheck.Variable
import Misc.MonoidMap (Map, (!))
import qualified Misc.MonoidMap as Map

data TypeError p
  = UnknownIdentifier p TermIdentifier
  | UnknownTypeIdentifier p TypeIdentifier
  | UnknownKindIdentifier p KindIdentifier
  | InvalidUsage p TermIdentifier
  | TypeMismatch p TypeUnify TypeUnify
  | KindMismatch p KindUnify KindUnify
  | SortMismatch p Sort Sort
  | TypeOccursCheck p LogicVariableType TypeUnify
  | KindOccursCheck p LogicVariableKind KindUnify
  | AmbiguousType p LogicVariableType (Set LogicVariableType)
  | AmbiguousKind p LogicVariableKind (Set LogicVariableKind)
  | CaptureLinear p TermIdentifier
  | ExpectedMetaPattern p
  | ExpectedRuntimePattern p
  deriving (Show)

class Monad m => TypeErrorQuit p m | m -> p where
  quit :: TypeError p -> m a

class Monad m => Index m k v where
  index :: k -> m v

class Monad m => Environment p m | m -> p where
  lookupTypeEnviroment :: TermIdentifier -> m (Maybe (p, Multiplicity, TypeSchemeUnify))
  augmentTypeEnvironment :: TermIdentifier -> p -> Multiplicity -> TypeSchemeUnify -> m a -> m a
  lookupKindEnvironment :: TypeIdentifier -> m (Maybe (p, KindUnify))
  augmentKindEnvironment :: TypeIdentifier -> p -> KindUnify -> m a -> m a
  lookupSortEnvironment :: KindIdentifier -> m (Maybe (p, Sort))
  augmentSortEnvironment :: KindIdentifier -> p -> Sort -> m a -> m a

class Monad m => System p m | m -> p where
  insertTypeEquation :: TypeEquation p TypeUnify -> m ()
  freshTypeVariableRaw :: p -> KindUnify -> m LogicVariableType
  insertKindEquation :: KindEquation p KindUnify -> m ()
  freshKindVariableRaw :: p -> Sort -> m LogicVariableKind

instance TypeErrorQuit Internal Identity where
  quit e = error $ "internal type error:" ++ show e

instance (Monad m, Ord k) => Index (ReaderT (Map k v) m) k v where
  index k = do
    m <- ask
    pure $ m ! k

instance Monad m => Index m Void v where
  index = absurd

instance TypeErrorQuit p m => TypeErrorQuit p (ReaderT a m) where
  quit = lift . quit

instance TypeErrorQuit p m => TypeErrorQuit p (StateT s m) where
  quit = lift . quit

instance (TypeErrorQuit p m, Monoid a) => TypeErrorQuit p (WriterT a m) where
  quit = lift . quit

instance TypeErrorQuit p m => TypeErrorQuit p (Core p m) where
  quit = Core . quit

instance (System p m, Monoid a) => System p (WriterT a m) where
  insertTypeEquation eq = lift $ insertTypeEquation eq
  freshTypeVariableRaw p κ = lift $ freshTypeVariableRaw p κ
  insertKindEquation eq = lift $ insertKindEquation eq
  freshKindVariableRaw p μ = lift $ freshKindVariableRaw p μ

data CoreEnvironment p = CoreEnvironment
  { typeEnvironment :: Map TermIdentifier (p, Multiplicity, TypeSchemeUnify),
    kindEnvironment :: Map TypeIdentifier (p, KindUnify),
    sortEnvironment :: Map KindIdentifier (p, Sort)
  }
  deriving (Functor, Show)

emptyEnvironment = CoreEnvironment Map.empty Map.empty Map.empty

data CoreState p = CoreState
  { typeVariableMap :: Map LogicVariableType (p, KindUnify),
    kindVariableMap :: Map LogicVariableKind (p, Sort),
    freshTypeCounter :: Int,
    freshKindCounter :: Int,
    typeEquations :: [TypeEquation p TypeUnify],
    kindEquations :: [KindEquation p KindUnify]
  }
  deriving (Show)

emptyState = CoreState Map.empty Map.empty 0 0 [] []

newtype Core p m a = Core {runCore' :: ReaderT (CoreEnvironment p) (StateT (CoreState p) m) a} deriving (Functor, Applicative, Monad)

runCore c = runStateT . runReaderT (runCore' c)

modifyEnvironment :: (CoreEnvironment p -> CoreEnvironment p) -> Core p m a -> Core p m a
modifyEnvironment f (Core r) = Core $ withReaderT f r

instance Monad m => Environment p (Core p m) where
  lookupTypeEnviroment x = do
    xΓ <- Core ask
    pure $ Map.lookup x (typeEnvironment xΓ)
  augmentTypeEnvironment x p l σ = modifyTypeEnvironment (Map.insert x (p, l, σ))
    where
      modifyTypeEnvironment f (Core r) = Core $ withReaderT (\env -> env {typeEnvironment = f (typeEnvironment env)}) r
  lookupKindEnvironment x = do
    xΓ <- Core ask
    pure $ Map.lookup x (kindEnvironment xΓ)
  augmentKindEnvironment x p κ = modifyKindEnvironment (Map.insert x (p, κ))
    where
      modifyKindEnvironment f (Core r) = Core $ withReaderT (\env -> env {kindEnvironment = f (kindEnvironment env)}) r
  lookupSortEnvironment x = do
    xΓ <- Core ask
    pure $ Map.lookup x (sortEnvironment xΓ)
  augmentSortEnvironment x p μ = modifySortEnvironment (Map.insert x (p, μ))
    where
      modifySortEnvironment f (Core r) = Core $ withReaderT (\env -> env {sortEnvironment = f (sortEnvironment env)}) r

getState = Core $ lift $ get

putState state = Core $ lift $ put state

getTypeEquations = typeEquations <$> getState

instance Monad m => System p (Core p m) where
  insertTypeEquation eq = modifyTypeEquations (eq :)
  freshTypeVariableRaw p κ = do
    v <- LogicVariableType <$> newFreshType
    insertTypeVariableMap v p κ
    pure $ v
    where
      newFreshType = do
        state <- getState
        let i = freshTypeCounter state
        putState state {freshTypeCounter = i + 1}
        pure i
      insertTypeVariableMap x p κ = do
        state <- getState
        putState state {typeVariableMap = Map.insert x (p, κ) $ typeVariableMap state}
  insertKindEquation eq = modifyKindEquations (eq :)

  freshKindVariableRaw p μ = do
    v <- LogicVariableKind <$> newFreshKind
    insertKindVariableMap v p μ
    pure $ v
    where
      newFreshKind = do
        state <- getState
        let i = freshKindCounter state
        putState state {freshKindCounter = i + 1}
        pure i
      insertKindVariableMap x p μ = do
        state <- getState
        putState state {kindVariableMap = Map.insert x (p, μ) $ kindVariableMap state}

modifyTypeEquations f = do
  state <- getState
  putState state {typeEquations = f $ typeEquations state}

getKindEquations = kindEquations <$> getState

modifyKindEquations f = do
  state <- getState
  putState state {kindEquations = f $ kindEquations state}

instance Monad m => Index (Core p m) LogicVariableType KindUnify where
  index = indexTypeVariableMap

instance Monad m => Index (Core p m) TypeIdentifier KindUnify where
  index x = snd <$> fromJust <$> lookupKindEnvironment x

indexTypeVariableMap x = snd <$> (! x) <$> typeVariableMap <$> getState

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

instance Monad m => Index (Core p m) LogicVariableKind Sort where
  index = indexKindVariableMap

instance Monad m => Index (Core p m) KindIdentifier Sort where
  index x = snd <$> fromJust <$> lookupSortEnvironment x

indexKindVariableMap x = snd <$> (! x) <$> kindVariableMap <$> getState

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
