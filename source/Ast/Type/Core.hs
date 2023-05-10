module Ast.Type.Core where

import Ast.Common.Variable
import Ast.Type.Algebra hiding (Type)
import qualified Ast.Type.Algebra as Algebra
import Ast.Type.Runtime
import Control.Monad.Trans.State (get, put, runState)
import Data.Functor.Identity (Identity (..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (fmapDefault, foldMapDefault)
import Data.Void (Void, absurd)
import Misc.Boolean

newtype Type v
  = Type
      ( TypeF
          Void
          v
          (TypeScheme v)
          (Type v)
      )
  deriving (Show)

type TypeUnify = Type TypeLogical

type TypeInfer = Type Void

data TypeScheme v
  = MonoType (Type v)
  | TypeForall (TypePattern v) (TypeScheme v)
  deriving (Show)

type TypeSchemeUnify = TypeScheme TypeLogical

type TypeSchemeInfer = TypeScheme Void

data TypePattern v = TypePattern TypeIdentifier (Type v)
  deriving (Show)

type TypePatternUnify = TypePattern TypeLogical

type TypePatternInfer = TypePattern Void

data TypePatternIntermediate p = TypePatternIntermediate
  { intermediatePosition :: p,
    intermediateBinder :: TypeIdentifier,
    intermediateKind :: TypeInfer
  }

data LabelScheme v
  = MonoLabel (TypeScheme v)
  | LabelForall TypeIdentifier (LabelScheme v)

type LabelSchemeUnify = LabelScheme TypeLogical

type LabelSchemeInfer = LabelScheme Void

data Instantiation v
  = InstantiateType (Type v) (Instantiation v)
  | InstantiateEmpty

type InstantiationUnify = Instantiation TypeLogical

type InstantiationInfer = Instantiation Void

toTypePattern (TypePatternIntermediate _ x κ) = TypePattern x κ

data ReLabel = ReLabel (Set TypeIdentifier) [TypeIdentifier]

relabel :: TypeScheme v -> LabelScheme v
relabel ς = foldr LabelForall (MonoLabel ς') schemes
  where
    (ς', ReLabel _ schemes) = runState (goTypeScheme ς) (ReLabel (freeLocalVariablesType ς) [])
    goType (Type (Poly _ ς)) = do
      ReLabel free schemes <- get
      let new = fresh free (TypeIdentifier "L")
      put $ ReLabel (Set.insert new free) (new : schemes)
      ς <- goTypeScheme ς
      pure $ Type $ Poly (Type $ TypeConstant $ TypeVariable new) ς
    goType (Type σ) = Type <$> traverseTypeF pure pure (error "handled manually") goType σ
    goTypeScheme (MonoType σ) = MonoType <$> goType σ
    goTypeScheme (TypeForall (TypePattern x κ) ς) = do
      κ <- goType κ
      ς <- goTypeScheme ς
      pure $ TypeForall (TypePattern x κ) ς

linear = Type TypeFalse

unrestricted = Type TypeTrue

none = Type TypeFalse

reconstruct
  indexVariable
  indexGlobalVariable
  indexLogical
  poly
  reconstructRuntime
  reconstructMultiplicities
  reconstructPropositonal
  (Type σ) = case σ of
    TypeConstant (TypeVariable x) -> do
      indexVariable x
    TypeConstant (TypeGlobalVariable x) -> do
      indexGlobalVariable x
    TypeLogical v -> do
      indexLogical v
    Inline _ _ _ -> do
      pure $ Type $ Algebra.Type
    Poly _ ς -> do
      poly ς
    FunctionPointer _ _ _ -> do
      pure $ Type $ Pretype (Type $ KindRuntime PointerRep) unrestricted
    FunctionLiteralType _ _ _ -> do
      pure $ Type $ Algebra.Type
    Tuple σs -> do
      ρs <- traverse reconstructRuntime σs
      τ <- reconstructMultiplicities σs
      pure $ Type $ Pretype (Type $ KindRuntime $ StructRep ρs) τ
    Step σ τ -> do
      κ <- reconstructRuntime σ
      μ <- reconstructRuntime τ
      let union = Type $ KindRuntime $ UnionRep $ [κ, μ]
      let wrap = Type $ KindRuntime $ StructRep $ [Type $ KindRuntime $ WordRep $ Type $ KindSize $ Byte, union]
      pure (Type $ Pretype wrap $ linear)
    Effect _ _ -> pure $ Type $ Algebra.Type
    Unique _ ->
      pure $ Type $ Pretype (Type $ KindRuntime $ PointerRep) linear
    Shared _ _ ->
      pure $ Type $ Pretype (Type $ KindRuntime $ PointerRep) unrestricted
    Number _ ρ -> do
      pure $ Type $ Pretype (Type $ KindRuntime $ WordRep ρ) unrestricted
    Pointer _ -> pure $ Type $ Boxed
    Array _ -> pure $ Type $ Boxed
    Boolean -> pure $ Type $ Pretype (Type $ KindRuntime $ WordRep $ Type $ KindSize $ Byte) unrestricted
    TypeConstant World -> pure $ Type $ Region
    Algebra.Type -> pure $ Type $ Kind (Type Syntactic) (Type Transparent)
    Region -> pure $ Type $ Kind (Type Propositional) (Type Transparent)
    Pretype _ _ -> pure $ Type $ Kind (Type Syntactic) (Type Transparent)
    Boxed -> pure $ Type $ Kind (Type Syntactic) (Type Transparent)
    Multiplicity -> pure $ Type $ Kind (Type Propositional) (Type Transparent)
    KindRuntime _ -> pure $ Type $ Representation
    KindSize _ -> pure $ Type $ Size
    KindSignedness _ -> pure $ Type $ Signedness
    Representation -> pure $ Type $ Kind (Type Syntactic) (Type Opaque)
    Size -> pure $ Type $ Kind (Type Syntactic) (Type Opaque)
    Signedness -> pure $ Type $ Kind (Type Syntactic) (Type Opaque)
    Syntactic -> pure (Type Unification)
    Propositional -> pure (Type Unification)
    Transparent -> pure (Type Transparency)
    Opaque -> pure (Type Transparency)
    Transparency -> pure (Type Top)
    Unification -> pure (Type Top)
    Kind _ _ -> do
      pure (Type $ Top)
    AmbiguousLabel -> pure (Type Label)
    Label -> pure $ Type $ Top
    TypeTrue -> reconstructPropositonal []
    TypeFalse -> reconstructPropositonal []
    TypeBoolean (TypeXor σ τ) -> reconstructPropositonal [σ, τ]
    TypeBoolean (TypeOr σ τ) -> reconstructPropositonal [σ, τ]
    TypeBoolean (TypeAnd σ τ) -> reconstructPropositonal [σ, τ]
    TypeBoolean (TypeNot σ) -> reconstructPropositonal [σ]
    Hole v -> absurd v
    Top -> error "reconstruct top"

convertBoolean (Type (TypeLogical v)) = variable v
convertBoolean (Type (TypeConstant c)) = constant c
convertBoolean (Type (TypeBoolean σ)) = case σ of
  TypeAnd σ τ -> convertBoolean σ * convertBoolean τ
  TypeOr σ τ -> x + y + x * y
    where
      x = convertBoolean σ
      y = convertBoolean τ
  TypeXor σ τ -> convertBoolean σ + convertBoolean τ
  TypeNot σ -> convertBoolean σ + 1
convertBoolean (Type TypeTrue) = 1
convertBoolean (Type TypeFalse) = 0
convertBoolean _ = error "convert boolean error"

unconvertBoolean (Polynomial e) | Set.null e = Type TypeFalse
unconvertBoolean (Polynomial e) = foldl1 (\σ τ -> Type $ TypeBoolean $ TypeXor σ τ) (map prod $ Set.toList e)
  where
    prod e | Set.null e = Type TypeTrue
    prod e = foldl1 (\σ τ -> Type $ TypeBoolean $ TypeAnd σ τ) (map var $ Set.toList e)
      where
        var (Flexible v) = Type $ TypeLogical v
        var (Constant c) = Type $ TypeConstant c

data TypeSubstitution v = TypeSubstitution (Map TypeIdentifier (Type v)) (Map TypeGlobalIdentifier (Type v))

typeSubstitutionShadow (TypeSubstitution locals _) = Map.keysSet locals

typeSubstitutionMask x (TypeSubstitution locals globals) = TypeSubstitution (Map.delete x locals) globals

typeSubstitutionLocalVariables :: TypeSubstitution v -> Set TypeIdentifier
typeSubstitutionLocalVariables (TypeSubstitution locals globals) =
  foldMap freeLocalVariablesType locals <> foldMap freeLocalVariablesType globals

class TypeAlgebra u where
  freeLocalVariablesType :: u v -> Set TypeIdentifier
  substituteTypes :: TypeSubstitution v -> u v -> u v
  zonkType :: Applicative m => (v -> m (Type v')) -> u v -> m (u v')
  simplify :: Ord v => u v -> u v

convertType :: TypeAlgebra u => TypeIdentifier -> TypeIdentifier -> u v -> u v
convertType ux x = substituteType (Type $ TypeConstant $ TypeVariable ux) x

substituteType :: TypeAlgebra u => Type v -> TypeIdentifier -> u v -> u v
substituteType ux x = substituteTypes (TypeSubstitution (Map.singleton x ux) Map.empty)

substituteGlobalType :: TypeAlgebra u => Type v -> TypeGlobalIdentifier -> u v -> u v
substituteGlobalType ux x = substituteTypes (TypeSubstitution Map.empty (Map.singleton x ux))

traverseDefault f = zonkType (\x -> Type <$> TypeLogical <$> f x)

substituteLogical f = runIdentity . zonkType (Identity . f)

instance Functor Type where
  fmap = fmapDefault

instance Functor TypeScheme where
  fmap = fmapDefault

instance Functor TypePattern where
  fmap = fmapDefault

instance Foldable Type where
  foldMap = foldMapDefault

instance Foldable TypeScheme where
  foldMap = foldMapDefault

instance Foldable TypePattern where
  foldMap = foldMapDefault

instance Traversable Type where
  traverse = traverseDefault

instance Traversable TypeScheme where
  traverse = traverseDefault

instance Traversable TypePattern where
  traverse f (TypePattern x κ) = TypePattern x <$> (traverse f κ)

instance TypeAlgebra Type where
  freeLocalVariablesType (Type (TypeConstant (TypeVariable x))) = Set.singleton x
  freeLocalVariablesType (Type σ) = foldTypeF mempty mempty go go σ
    where
      go = freeLocalVariablesType
  substituteTypes (TypeSubstitution xs _) (Type (TypeConstant (TypeVariable x)))
    | Just σ <- Map.lookup x xs = σ
  substituteTypes (TypeSubstitution _ xs) (Type (TypeConstant (TypeGlobalVariable x)))
    | Just σ <- Map.lookup x xs = σ
  substituteTypes θ (Type σ) = Type $ mapTypeF id id go go σ
    where
      go = substituteTypes θ
  zonkType f (Type (TypeLogical x)) = f x
  zonkType f (Type σ) = Type <$> traverseTypeF absurd (error "handled manually") go go σ
    where
      go = zonkType f
  simplify σ@(Type (TypeBoolean _)) = unconvertBoolean $ convertBoolean σ
  simplify (Type σ) = Type $ mapTypeF id id go go σ
    where
      go = simplify

instance TypeAlgebra Instantiation where
  freeLocalVariablesType InstantiateEmpty = mempty
  freeLocalVariablesType (InstantiateType σ θ) = go σ <> go θ
    where
      go = freeLocalVariablesType
  substituteTypes _ InstantiateEmpty = InstantiateEmpty
  substituteTypes θ' (InstantiateType σ θ) = InstantiateType (go σ) (go θ)
    where
      go = substituteTypes θ'
  zonkType _ InstantiateEmpty = pure InstantiateEmpty
  zonkType f (InstantiateType σ θ) = InstantiateType <$> go σ <*> go θ
    where
      go = zonkType f
  simplify InstantiateEmpty = InstantiateEmpty
  simplify (InstantiateType σ θ) = InstantiateType (go σ) (go θ)
    where
      go = simplify

instance TypeAlgebra TypeScheme where
  freeLocalVariablesType (MonoType σ) = freeLocalVariablesType σ
  freeLocalVariablesType (TypeForall (TypePattern x κ) σ) =
    freeLocalVariablesType κ <> Set.delete x (freeLocalVariablesType σ)
  substituteTypes θ (MonoType σ) = MonoType $ substituteTypes θ σ
  substituteTypes θ (TypeForall (TypePattern x κ) σ)
    | Set.member x (typeSubstitutionShadow θ) = let go = substituteTypes (typeSubstitutionMask x θ) in TypeForall (TypePattern x (go κ)) (go σ)
    | otherwise = TypeForall (TypePattern x' (go κ)) (go σ')
    where
      variables = typeSubstitutionLocalVariables θ
      x' = fresh variables x
      σ' = convertType x' x σ
      go = substituteTypes θ
  zonkType f (MonoType σ) = MonoType <$> zonkType f σ
  zonkType f (TypeForall (TypePattern x κ) σ) = TypeForall <$> (TypePattern x <$> go κ) <*> go σ
    where
      go = zonkType f
  simplify (MonoType σ) = MonoType $ simplify σ
  simplify (TypeForall (TypePattern x κ) σ) = TypeForall (TypePattern x (simplify κ)) (simplify σ)

instance TypeAlgebra LabelScheme where
  freeLocalVariablesType (MonoLabel σ) = freeLocalVariablesType σ
  freeLocalVariablesType (LabelForall x σ) = Set.delete x (freeLocalVariablesType σ)
  substituteTypes θ (MonoLabel σ) = MonoLabel $ substituteTypes θ σ
  substituteTypes θ (LabelForall x σ)
    | Set.member x (typeSubstitutionShadow θ) = LabelForall x σ
    | otherwise = LabelForall x' (go σ')
    where
      variables = typeSubstitutionLocalVariables θ
      x' = fresh variables x
      σ' = convertType x' x σ
      go = substituteTypes θ
  zonkType f (MonoLabel σ) = MonoLabel <$> zonkType f σ
  zonkType f (LabelForall x σ) = LabelForall x <$> zonkType f σ
  simplify (MonoLabel σ) = MonoLabel $ simplify σ
  simplify (LabelForall x σ) = LabelForall x $ simplify σ
