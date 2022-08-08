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
  | UnknownGlobalIdentifier p TermGlobalIdentifier
  | UnknownTypeIdentifier p TypeIdentifier
  | InvalidUsage p TermIdentifier
  | TypeMismatch p TypeUnify TypeUnify
  | TypeMisrelation p TypeSub TypeSub
  | TypeOccursCheck p TypeLogical TypeUnify
  | AmbiguousType p TypeInfer
  | EscapingSkolemType p TypeIdentifier TypeUnify
  | CaptureLinear p TermIdentifier
  | ExpectedTypeAnnotation p
  | ConstraintMismatch p Constraint TypeUnify
  | ConstraintKindError p Constraint TypeUnify
  | ExpectedFunctionLiteral p
  | NoCommonMeet p TypeSub TypeSub
  | MismatchedTypeLambdas p
  | ExpectedTypeAbstraction p
  | ExpectedPlainType p
  | IncorrectRegionBounds p
  | NotTypable p
  | ExpectedSubtypable p
  | BadConstraintAnnotation p
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
  deriving (Show)

newtype Core p a = Core {runCore'' :: ReaderT (CoreEnvironment p) (StateT (CoreState p) (Either (TypeError p))) a} deriving (Functor, Applicative, Monad)

runCore' c = runStateT . runReaderT (runCore'' c)

runCore :: Core p a -> CoreEnvironment p -> CoreState p -> Either (TypeError p) a
runCore c = (fmap fst .) . runCore' c

data TermBinding p = TermBinding p Multiplicity TypeSchemeUnify deriving (Show, Functor)

data TypeBinding p = TypeBinding p TypeInfer (Set Constraint) (Set TypeSub) Level deriving (Show, Functor)

data CoreEnvironment p = CoreEnvironment
  { typeEnvironment :: Map TermIdentifier (TermBinding p),
    kindEnvironment :: Map TypeIdentifier (TypeBinding p),
    typeGlobalEnviroment :: Map TermGlobalIdentifier (TermBinding p)
  }
  deriving (Functor, Show)

data TypeLogicalState p
  = UnboundTypeLogical p TypeUnify (Set Constraint) [TypeUnify] (Maybe TypeSub) Level
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

emptyEnvironment = CoreEnvironment Map.empty Map.empty Map.empty

askEnvironment = Core ask

withEnvironment f (Core r) = Core $ withReaderT f r

lookupTypeEnviroment :: TermIdentifier -> Core p (Maybe (TermBinding p))
lookupTypeEnviroment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (typeEnvironment xΓ)

lookupTypeGlobalEnviroment :: TermGlobalIdentifier -> Core p (Maybe (TermBinding p))
lookupTypeGlobalEnviroment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (typeGlobalEnviroment xΓ)

augmentTypeEnvironment :: TermIdentifier -> p -> Multiplicity -> TypeSchemeUnify -> Core p a -> Core p a
augmentTypeEnvironment x p l σ = modifyTypeEnvironment (Map.insert x (TermBinding p l σ))
  where
    modifyTypeEnvironment f (Core r) = Core $ withReaderT (\env -> env {typeEnvironment = f (typeEnvironment env)}) r

lookupKindEnvironment :: TypeIdentifier -> Core p (Maybe (TypeBinding p))
lookupKindEnvironment x = do
  xΓ <- Core ask
  pure $ Map.lookup x (kindEnvironment xΓ)

indexKindEnvironment :: TypeIdentifier -> Core p (TypeBinding p)
indexKindEnvironment x = do
  xΓ <- Core ask
  if x `Map.notMember` kindEnvironment xΓ
    then error $ "Bad Type Variable " ++ show x
    else pure $ kindEnvironment xΓ ! x

lowerTypeBounds :: TypeSub -> Core p (Set TypeSub)
lowerTypeBounds (TypeVariable x) = do
  TypeBinding _ _ _ π _ <- indexKindEnvironment x
  pure π
lowerTypeBounds World = pure (Set.singleton World)

modifyKindEnvironment f (Core r) = Core $ withReaderT (\env -> env {kindEnvironment = f (kindEnvironment env)}) r

-- todo assertions to avoid shadowing
augmentKindEnvironment p x κ c π lev f = do
  πs <- Set.insert (TypeVariable x) <$> closure π
  modifyKindEnvironment (Map.insert x (TypeBinding p κ c πs lev)) f
  where
    closure :: Set TypeSub -> Core p (Set TypeSub)
    closure x = fold <$> traverse lowerTypeBounds (Set.toList x)

augmentKindUnify occurs p x = modifyKindEnvironment (Map.insert x (TypeBinding p κ c π (if occurs then minBound else maxBound)))
  where
    κ = error "kind used during unification"
    c = error "constraints used during unification"
    π = error "bottom used during unification"

augmentTypePatternLevel (TypePatternIntermediate p x κ c π) f = do
  enterLevel
  useTypeVar x
  lev <- Level <$> currentLevel
  f' <- augmentKindEnvironment p x κ c (Set.fromList π) lev f
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

freshTypeVariableRaw :: p -> TypeUnify -> Set Constraint -> [TypeUnify] -> Maybe TypeSub -> Level -> Core p TypeLogical
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

freshKindVariableRaw p μ lev = freshTypeVariableRaw p μ Set.empty [] Nothing lev

indexTypeLogicalMap :: TypeLogical -> Core p (TypeLogicalState p)
indexTypeLogicalMap x = do
  vars <- typeLogicalMap <$> getState
  if x `Map.notMember` vars
    then error $ "Bad Type Logical " ++ show x
    else pure $ vars ! x

useTypeVar :: TypeIdentifier -> Core p ()
useTypeVar (TypeIdentifier x) = do
  modifyState $ \state -> state {usedVars = Set.insert x $ usedVars state}
