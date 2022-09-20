{-# LANGUAGE UndecidableInstances #-}

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
  | ExpectedSort p TypeInfer
  | ExpectedKind p TypeInfer
  | ExpectedType p TypeInfer
  | ExpectedPretype p TypeInfer
  | ExpectedBoxed p TypeInfer
  | ExpectedLength p TypeInfer
  | ExpectedRegion p TypeInfer
  | ExpectedSubtypable' p TypeInfer
  | ExpectedRepresentation p TypeInfer
  | ExpectedSize p TypeInfer
  | ExpectedSignedness p TypeInfer
  | ExpectedSubstitutability p TypeInfer
  | ExpectedMultiplicity p TypeInfer
  | ExpectedNewtype p TypeInfer
  deriving (Show)

newtype Core p a = Core {runCore'' :: ReaderT (CoreEnvironment p) (StateT (CoreState p) (Either (TypeError p))) a} deriving (Functor, Applicative, Monad)

runCore' c = runStateT . runReaderT (runCore'' c)

runCore :: Core p a -> CoreEnvironment p -> CoreState p -> Either (TypeError p) a
runCore c = (fmap fst .) . runCore' c

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
  = TypeBinding p TypeInfer (Set TypeSub) Level NominalBinding
  | LinkTypeBinding TypeInfer
  deriving (Show, Functor)

data CoreEnvironment p = CoreEnvironment
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
data CoreState p = CoreState
  { typeLogicalMap :: Map TypeLogical (TypeLogicalState p),
    freshTypeCounter :: Int,
    levelCounter :: Int,
    usedVars :: Set String
  }
  deriving (Functor, Show)

quit e = Core $ lift $ lift $ Left e

emptyEnvironment = CoreEnvironment Map.empty Map.empty Map.empty Map.empty

askEnvironment = Core ask

withEnvironment f (Core r) = Core $ withReaderT f r

lookupTypeEnviroment :: TermIdentifier -> Core p (Maybe (TermBinding p))
lookupTypeEnviroment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (typeEnvironment xΓ)

lookuptypeGlobalEnvironment :: TermGlobalIdentifier -> Core p (Maybe (TermBinding p))
lookuptypeGlobalEnvironment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (typeGlobalEnvironment xΓ)

augmentTypeEnvironment :: TermIdentifier -> p -> TypeUnify -> TypeSchemeUnify -> Core p a -> Core p a
augmentTypeEnvironment x p l σ = modifyTypeEnvironment (Map.insert x (TermBinding p l σ))
  where
    modifyTypeEnvironment f (Core r) = Core $ withReaderT (\env -> env {typeEnvironment = f (typeEnvironment env)}) r

lookupKindEnvironment :: TypeIdentifier -> Core p (Maybe (TypeBinding p))
lookupKindEnvironment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (kindEnvironment xΓ)

lookupKindGlobalEnvironment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (kindGlobalEnvironment xΓ)

indexKindEnvironment :: TypeIdentifier -> Core p (TypeBinding p)
indexKindEnvironment x = do
  xΓ <- Core ask
  if x `Map.notMember` kindEnvironment xΓ
    then error $ "Bad Type Variable " ++ show x
    else pure $ kindEnvironment xΓ ! x

indexKindGlobalEnvironment x = do
  xΓ <- Core ask
  if x `Map.notMember` kindGlobalEnvironment xΓ
    then error $ "Bad Type Variable " ++ show x
    else pure $ kindGlobalEnvironment xΓ ! x

lowerTypeBounds :: TypeSub -> Core p (Set TypeSub)
lowerTypeBounds (TypeVariable x) = do
  indexKindEnvironment x >>= \case
    TypeBinding _ _ π _ _ -> do
      pure π
    LinkTypeBinding (TypeCore (TypeSub σ)) -> lowerTypeBounds σ
    LinkTypeBinding _ -> error "unexpected subtypable"
lowerTypeBounds (TypeGlobalVariable x) = do
  indexKindGlobalEnvironment x >>= \case
    TypeBinding _ _ π _ _ -> do
      pure π
    LinkTypeBinding (TypeCore (TypeSub σ)) -> lowerTypeBounds σ
    LinkTypeBinding _ -> error "unexpected subtypable"
lowerTypeBounds World = pure (Set.singleton World)
lowerTypeBounds Linear = pure (Set.singleton Linear)
lowerTypeBounds Unrestricted = pure (Set.fromList [Linear, Unrestricted])

modifyKindEnvironment f (Core r) = Core $ withReaderT (\env -> env {kindEnvironment = f (kindEnvironment env)}) r

-- todo assertions to avoid shadowing
augmentKindEnvironment p x κ π lev f = do
  πs <- Set.insert (TypeVariable x) <$> closure π
  modifyKindEnvironment (Map.insert x (TypeBinding p κ πs lev Unnamed)) f
  where
    closure :: Set TypeSub -> Core p (Set TypeSub)
    closure x = fold <$> traverse lowerTypeBounds (Set.toList x)

augmentKindUnify occurs p x = modifyKindEnvironment (Map.insert x (TypeBinding p κ π (if occurs then minBound else maxBound) Unnamed))
  where
    κ = error "kind used during unification"
    π = error "bounds used during unification"

augmentTypePatternLevel (TypePatternIntermediate p x κ π) f = do
  enterLevel
  useTypeVar x
  lev <- Level <$> currentLevel
  f' <- augmentKindEnvironment p x κ (Set.fromList π) lev f
  leaveLevel
  pure f'

emptyState = CoreState Map.empty 0 0 Set.empty

getState = Core $ lift $ get

putState state = Core $ lift $ put state

modifyState f = Core $ lift $ modify f

getTypeLogicalMap = typeLogicalMap <$> getState

modifyTypeLogicalMap f = do
  modifyState $ \state ->
    state
      { typeLogicalMap = f $ typeLogicalMap state
      }

modifyLevelCounter :: (Int -> Int) -> Core p ()
modifyLevelCounter f = do
  modifyState $ \state -> state {levelCounter = f $ levelCounter state}

enterLevel = modifyLevelCounter (+ 1)

-- todo lower levels of all type variables in state
leaveLevel = modifyLevelCounter (subtract 1)

currentLevel = levelCounter <$> getState

freshTypeVariableRaw :: p -> TypeUnify -> [TypeUnify] -> Maybe TypeSub -> Level -> Core p TypeLogical
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

indexTypeLogicalMap :: TypeLogical -> Core p (TypeLogicalState p)
indexTypeLogicalMap x = do
  vars <- typeLogicalMap <$> getState
  if x `Map.notMember` vars
    then error $ "Bad Type Logical " ++ show x
    else pure $ vars ! x

useTypeVar :: TypeIdentifier -> Core p ()
useTypeVar (TypeIdentifier x) = do
  modifyState $ \state -> state {usedVars = Set.insert x $ usedVars state}
