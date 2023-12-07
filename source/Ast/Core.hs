module Ast.Core
  ( Arithmatic (..),
    Relational (..),
    Erasure (..),
    GlobalImpl (..),
    Global,
    Term (..),
    TermUnify,
    TermInfer,
    TermPattern (..),
    TermPatternUnify,
    TermPatternInfer,
    TermMetaPattern (..),
    TermMetaPatternUnify,
    TermMetaPatternInfer,
    TermScheme (..),
    TermSchemeUnify,
    TermSchemeInfer,
    TypeLogical (..),
    Type (..),
    TypeUnify,
    TypeInfer,
    TypeScheme (..),
    TypeSchemeUnify,
    TypeSchemeInfer,
    LabelScheme (..),
    LabelSchemeUnify,
    LabelSchemeInfer,
    TypeAlgebra,
    reconstruct,
    convertBoolean,
    unconvertBoolean,
    freeLocalVariablesType,
    convertType,
    substituteType,
    substituteLogical,
    simplify,
    zonkType,
    relabel,
    reduceModule,
    textType,
    nameType,
    global,
  )
where

import Ast.Surface (Arithmatic (..), Erasure (..), Relational (..))
import qualified Ast.Surface as Surface
import Ast.Symbol
import Control.Monad.Trans.State.Strict (get, put, runState)
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
import qualified Misc.Boolean as Boolean

data GlobalImpl p v
  = Text (TermScheme p v)
  | Macro (TermScheme p v)
  | Synonym (Type v)
  | ForwardText (TypeScheme v)
  | ForwardNewType (Type v)
  deriving (Show)

type Global p = GlobalImpl p Void

data Term p v
  = Variable p TermIdentifier [Type v]
  | GlobalVariable p TermGlobalIdentifier [Type v]
  | Let p (TermPattern p v) (Term p v) (Term p v)
  | Case p (Term p v) (Type v) [(TermPattern p v, Term p v)] (Type v)
  | Extern p Symbol (Type v) (Type v) (Type v)
  | Application p (Term p v) (Term p v) (Type v)
  | TupleLiteral p [Term p v]
  | Read p (Term p v)
  | Write p (Term p v) (Term p v) (Type v)
  | NumberLiteral p Integer (Type v)
  | Arithmatic p Arithmatic (Term p v) (Term p v) (Type v)
  | Relational p Relational (Term p v) (Term p v) (Type v) (Type v)
  | BooleanLiteral p Bool
  | PointerAddition p (Term p v) (Term p v) (Type v)
  | Continue p (Term p v) (Type v)
  | Break p (Term p v) (Type v)
  | Loop p (TermPattern p v) (Term p v) (Term p v)
  | Isolate p (Term p v)
  | Cast p (Term p v) (Type v)
  | Not p (Term p v)
  | And p (Term p v) (Term p v)
  | Or p (Term p v) (Term p v)
  | Do p (Term p v) (Term p v)
  | If p (Term p v) (Term p v) (Term p v)
  | FunctionLiteral p (TermPattern p v) (Type v) (Type v) (Term p v)
  | InlineAbstraction p (TermMetaPattern p v) (Term p v)
  | InlineApplication p (Term p v) (Term p v)
  | InlineLet p (TermMetaPattern p v) (Term p v) (Term p v)
  | PolyIntroduction p (TermScheme p v)
  | PolyElimination p (Term p v) [Type v]
  deriving (Show, Functor, Foldable, Traversable)

type TermUnify p = Term p TypeLogical

type TermInfer p = Term p Void

data TermPattern p v
  = MatchVariable p TermIdentifier (Type v)
  | MatchTuple p [TermPattern p v]
  | MatchBoolean p Bool
  deriving (Show, Functor, Foldable, Traversable)

type TermPatternUnify p = TermPattern p TypeLogical

type TermPatternInfer p = TermPattern p Void

data TermMetaPattern p v
  = InlineMatchVariable p TermIdentifier (Type v) (Type v)
  deriving (Show, Functor, Foldable, Traversable)

type TermMetaPatternUnify p = TermMetaPattern p TypeLogical

type TermMetaPatternInfer p = TermMetaPattern p Void

data TermScheme p v
  = MonoTerm (Term p v)
  | TypeAbstraction TypeIdentifier Erasure (Type v) (TermScheme p v)
  deriving (Show, Functor, Foldable, Traversable)

type TermSchemeUnify p = TermScheme p TypeLogical

type TermSchemeInfer p = TermScheme p Void

data TypeLogical = TypeLogicalRaw Int
  deriving (Show, Eq, Ord)

data Type v
  = TypeLogical v
  | TypeVariable TypeIdentifier
  | TypeGlobalVariable TypeGlobalIdentifier
  | TypeTrue
  | TypeFalse
  | TypeNot (Type v)
  | TypeAnd (Type v) (Type v)
  | TypeOr (Type v) (Type v)
  | TypeXor (Type v) (Type v)
  | World
  | Inline (Type v) (Type v) (Type v)
  | FunctionPointer (Type v) (Type v) (Type v)
  | FunctionLiteralType (Type v) (Type v) (Type v)
  | Tuple [Type v]
  | Effect (Type v) (Type v)
  | Unique (Type v)
  | Shared (Type v) (Type v)
  | Pointer (Type v)
  | Array (Type v)
  | Number (Type v) (Type v)
  | Boolean
  | Step (Type v) (Type v)
  | Type
  | Region
  | Multiplicity
  | Pretype (Type v) (Type v)
  | Boxed
  | PointerRepresentation
  | StructRepresentation [Type v]
  | UnionRepresentation [Type v]
  | WordRepresentation (Type v)
  | Signed
  | Unsigned
  | Byte
  | Short
  | Int
  | Long
  | Native
  | Representation
  | Size
  | Signedness
  | Kind (Type v)
  | Syntactic
  | Propositional
  | Unification
  | AmbiguousLabel
  | Label
  | Top
  | TypeScheme (Type v) (TypeScheme v)
  deriving (Show, Functor, Foldable, Traversable)

type TypeUnify = Type TypeLogical

type TypeInfer = Type Void

data TypeScheme v
  = MonoType (Type v)
  | TypeForall TypeIdentifier Erasure (Type v) (TypeScheme v)
  deriving (Show, Functor, Foldable, Traversable)

type TypeSchemeUnify = TypeScheme TypeLogical

type TypeSchemeInfer = TypeScheme Void

data LabelScheme v
  = MonoLabel (TypeScheme v)
  | LabelForall TypeIdentifier (LabelScheme v)
  deriving (Show)

type LabelSchemeUnify = LabelScheme TypeLogical

type LabelSchemeInfer = LabelScheme Void

traverseTerm fς fσ fλ2 fλ f = \case
  Variable p x θ -> Variable p x <$> traverse fσ θ
  GlobalVariable p x θ -> GlobalVariable p x <$> traverse fσ θ
  Let p pm e1 e2 -> (\e1 (pm, e2) -> Let p pm e1 e2) <$> f e1 <*> fλ pm e2
  Case p e σ λ τ -> Case p <$> f e <*> fσ σ <*> traverse (uncurry fλ) λ <*> fσ τ
  Extern p sym σ π τ -> Extern p sym <$> fσ σ <*> fσ π <*> fσ τ
  Application p e1 e2 σ -> Application p <$> f e1 <*> f e2 <*> fσ σ
  TupleLiteral p es -> TupleLiteral p <$> traverse f es
  Read p e -> Read p <$> f e
  Write p e1 e2 σ -> Write p <$> f e1 <*> f e2 <*> fσ σ
  NumberLiteral p n σ -> NumberLiteral p n <$> fσ σ
  Arithmatic p o e1 e2 σ -> Arithmatic p o <$> f e1 <*> f e2 <*> fσ σ
  Relational p o e1 e2 σ τ -> Relational p o <$> f e1 <*> f e2 <*> fσ σ <*> fσ τ
  BooleanLiteral p b -> pure (BooleanLiteral p b)
  PointerAddition p e1 e2 σ -> PointerAddition p <$> f e1 <*> f e2 <*> fσ σ
  Continue p e σ -> Continue p <$> f e <*> fσ σ
  Break p e σ -> Break p <$> f e <*> fσ σ
  Loop p pm e1 e2 -> (\e1 (pm, e2) -> Loop p pm e1 e2) <$> f e1 <*> fλ pm e2
  Isolate p e -> Isolate p <$> f e
  Cast p e σ -> Cast p <$> f e <*> fσ σ
  Not p e -> Not p <$> f e
  And p e1 e2 -> And p <$> f e1 <*> f e2
  Or p e1 e2 -> Or p <$> f e1 <*> f e2
  Do p e1 e2 -> Do p <$> f e1 <*> f e2
  If p e1 e2 e3 -> If p <$> f e1 <*> f e2 <*> f e3
  FunctionLiteral p pm σ τ e -> (\σ τ (pm, e) -> FunctionLiteral p pm σ τ e) <$> fσ σ <*> fσ τ <*> fλ pm e
  InlineAbstraction p pm e -> (\(pm, e) -> InlineAbstraction p pm e) <$> fλ2 pm e
  InlineApplication p e1 e2 -> InlineApplication p <$> f e1 <*> f e2
  InlineLet p pm e1 e2 -> (\e1 (pm, e2) -> InlineLet p pm e1 e2) <$> f e1 <*> fλ2 pm e2
  PolyIntroduction p ς -> PolyIntroduction p <$> fς ς
  PolyElimination p e θ -> PolyElimination p <$> f e <*> traverse fσ θ

mapTerm fς fσ fλ2 fλ f = runIdentity . traverseTerm (Identity . fς) (Identity . fσ) ((Identity .) . fλ2) ((Identity .) . fλ) (Identity . f)

foldTerm fς fσ fλ2 fλ f = getConst . traverseTerm (Const . fς) (Const . fσ) ((Const .) . fλ2) ((Const .) . fλ) (Const . f)

traverseType logical scheme f = \case
  TypeLogical v -> logical v
  TypeVariable x -> pure (TypeVariable x)
  TypeGlobalVariable x -> pure (TypeGlobalVariable x)
  TypeTrue -> pure TypeTrue
  TypeFalse -> pure TypeFalse
  TypeNot σ -> TypeNot <$> f σ
  TypeAnd σ τ -> TypeAnd <$> f σ <*> f τ
  TypeOr σ τ -> TypeOr <$> f σ <*> f τ
  TypeXor σ τ -> TypeXor <$> f σ <*> f τ
  World -> pure World
  Inline σ π τ -> Inline <$> f σ <*> f π <*> f τ
  FunctionPointer σ π τ -> FunctionPointer <$> f σ <*> f π <*> f τ
  FunctionLiteralType σ π τ -> FunctionLiteralType <$> f σ <*> f π <*> f τ
  Tuple σs -> Tuple <$> traverse f σs
  Effect σ π -> Effect <$> f σ <*> f π
  Unique σ -> Unique <$> f σ
  Shared σ τ -> Shared <$> f σ <*> f τ
  Pointer σ -> Pointer <$> f σ
  Array σ -> Array <$> f σ
  Number σ τ -> Number <$> f σ <*> f τ
  Boolean -> pure Boolean
  Step σ τ -> Step <$> f σ <*> f τ
  Type -> pure Type
  Region -> pure Region
  Multiplicity -> pure Multiplicity
  Pretype σ τ -> Pretype <$> f σ <*> f τ
  Boxed -> pure Boxed
  PointerRepresentation -> pure PointerRepresentation
  StructRepresentation σs -> StructRepresentation <$> traverse f σs
  UnionRepresentation σs -> UnionRepresentation <$> traverse f σs
  WordRepresentation σ -> WordRepresentation <$> f σ
  Signed -> pure Signed
  Unsigned -> pure Unsigned
  Byte -> pure Byte
  Short -> pure Short
  Int -> pure Int
  Long -> pure Long
  Native -> pure Native
  Representation -> pure Representation
  Size -> pure Size
  Signedness -> pure Signedness
  Kind σ -> Kind <$> f σ
  Syntactic -> pure Syntactic
  Propositional -> pure Propositional
  Unification -> pure Unification
  AmbiguousLabel -> pure AmbiguousLabel
  Label -> pure Label
  Top -> pure Top
  TypeScheme σ λ -> scheme σ λ

mapType logical scheme f = runIdentity . traverseType (Identity . logical) ((Identity .) . scheme) (Identity . f)

foldType logical scheme f = getConst . traverseType (Const . logical) ((Const .) . scheme) (Const . f)

reconstruct
  variable
  globalVariable
  logical
  poly
  reconstructRuntime
  reconstructMultiplicities
  reconstructPropositonal
  σ = case σ of
    TypeLogical v -> logical v
    TypeScheme _ ς -> poly ς
    TypeVariable x -> variable x
    TypeGlobalVariable x -> globalVariable x
    Inline {} -> pure Type
    FunctionPointer {} -> pure (Pretype PointerRepresentation unrestricted)
    FunctionLiteralType {} -> pure Type
    Tuple σs -> do
      ρs <- traverse reconstructRuntime σs
      τ <- reconstructMultiplicities σs
      pure (Pretype (StructRepresentation ρs) τ)
    Step σ τ -> do
      κ <- reconstructRuntime σ
      ρ <- reconstructRuntime τ
      let representation = StructRepresentation [WordRepresentation Byte, UnionRepresentation [κ, ρ]]
      pure (Pretype representation linear)
    Effect {} -> pure Type
    Unique {} -> pure (Pretype PointerRepresentation linear)
    Shared {} -> pure (Pretype PointerRepresentation unrestricted)
    Number _ ρ -> pure (Pretype (WordRepresentation ρ) unrestricted)
    Pointer {} -> pure Boxed
    Array {} -> pure Boxed
    Boolean {} -> pure (Pretype (WordRepresentation Byte) unrestricted)
    World -> pure Region
    Type -> pure (Kind Syntactic)
    Region -> pure (Kind Propositional)
    Pretype {} -> pure (Kind Syntactic)
    Boxed -> pure (Kind Syntactic)
    Multiplicity -> pure (Kind Propositional)
    PointerRepresentation -> pure Representation
    StructRepresentation {} -> pure Representation
    UnionRepresentation {} -> pure Representation
    WordRepresentation {} -> pure Representation
    Signed -> pure Signedness
    Unsigned -> pure Signedness
    Byte -> pure Size
    Short -> pure Size
    Int -> pure Size
    Long -> pure Size
    Native -> pure Size
    Representation -> pure (Kind Syntactic)
    Size -> pure (Kind Syntactic)
    Signedness -> pure (Kind Syntactic)
    Syntactic -> pure Unification
    Propositional -> pure Unification
    Unification -> pure Top
    Kind {} -> pure Top
    AmbiguousLabel -> pure Label
    Label -> pure Top
    TypeTrue -> reconstructPropositonal []
    TypeFalse -> reconstructPropositonal []
    TypeXor σ τ -> reconstructPropositonal [σ, τ]
    TypeOr σ τ -> reconstructPropositonal [σ, τ]
    TypeAnd σ τ -> reconstructPropositonal [σ, τ]
    TypeNot σ -> reconstructPropositonal [σ]
    Top -> error "reconstruct top"
    where
      linear = TypeFalse
      unrestricted = TypeTrue

data TermVariables = TermVariables (Set TermIdentifier) (Set TermGlobalIdentifier)

instance Semigroup TermVariables where
  TermVariables a b <> TermVariables a' b' = TermVariables (a <> a') (b <> b')

instance Monoid TermVariables where
  mempty = TermVariables mempty mempty
  mappend = (<>)

variablesRemoveLocal x (TermVariables locals globals) = TermVariables (Set.delete x locals) globals

data TermSubstitution p
  = TermSubstitution
      (Map TermIdentifier (TermSchemeInfer p))
      (Map TermGlobalIdentifier (TermSchemeInfer p))
      (Map TermIdentifier TermIdentifier)

termSubstitutionMask x (TermSubstitution locals globals alpha) = TermSubstitution (Map.delete x locals) globals (Map.delete x alpha)

termSubstitutionLocalVariables (TermSubstitution locals globals alpha) =
  foldMap freeLocalVariablesTerm locals <> foldMap freeLocalVariablesTerm globals <> foldMap Set.singleton alpha

termSubstitutionLocalTypeVariables (TermSubstitution locals globals _) =
  foldMap freeLocalVariablesType locals <> foldMap freeLocalVariablesType globals

class TermAlgebra u where
  freeVariablesTerm :: u p v -> TermVariables
  substituteTerms :: TermSubstitution p -> u p Void -> u p Void

  -- Demonstrating Lambda Calculus Reduction
  -- https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf

  -- Applicative Order Reduction
  reduce :: u p Void -> u p Void

class Binder pm where
  bindings :: pm -> Set TermIdentifier
  rename :: TermIdentifier -> TermIdentifier -> pm -> pm

freeLocalVariablesTerm :: TermAlgebra u => u p v -> Set TermIdentifier
freeLocalVariablesTerm e = case freeVariablesTerm e of
  TermVariables variables _ -> variables

convertTerm ux x = substituteTerms (TermSubstitution Map.empty Map.empty (Map.singleton x ux))

substituteLocalTerm ux x = substituteTerms (TermSubstitution (Map.singleton x ux) Map.empty Map.empty)

applyScheme :: TermSchemeInfer p -> [TypeInfer] -> TermInfer p
applyScheme (MonoTerm e) [] = e
applyScheme (TypeAbstraction x _ _ e) (σ : θ) =
  applyScheme (substituteType σ x e) θ
applyScheme _ _ = error "bad scheme pair"

applyTerm :: Term p Void -> TermMetaPattern p Void -> Term p Void -> Term p Void
applyTerm e (InlineMatchVariable _ x _ _) ex = reduce $ substituteLocalTerm (MonoTerm e) x ex

substituteBound θ pm e =
  let binders = Set.toList $ bindings pm
      θ' = foldr termSubstitutionMask θ binders
      illegal = termSubstitutionLocalVariables θ'
      target = filter (flip Set.member illegal) binders
      alphaPattern x pm = let x' = fresh illegal x in rename x' x pm
      alphaTerm x e = let x' = fresh illegal x in convertTerm x' x e
      pm' = foldr alphaPattern pm target
      e' = foldr alphaTerm e target
      go = substituteTerms θ'
   in (pm', go e')

instance TermAlgebra Term where
  freeVariablesTerm (Variable _ x _) = TermVariables (Set.singleton x) Set.empty
  freeVariablesTerm (GlobalVariable _ x _) = TermVariables Set.empty (Set.singleton x)
  freeVariablesTerm e = foldTerm go mempty bound bound go e
    where
      bound pm e = foldr variablesRemoveLocal (go e) (bindings pm)
      go = freeVariablesTerm

  substituteTerms (TermSubstitution locals _ alpha) (Variable p x θ)
    | Just e <- Map.lookup x locals = applyScheme e θ
    | Just x' <- Map.lookup x alpha = Variable p x' θ
  substituteTerms (TermSubstitution _ globals _) (GlobalVariable _ x θ)
    | Just e <- Map.lookup x globals = applyScheme e θ
  substituteTerms θ e = mapTerm go id bound bound go e
    where
      bound = substituteBound θ
      go = substituteTerms θ

  reduce (InlineLet _ pm e ex) = applyTerm e pm (reduce ex)
  reduce (InlineApplication _ e1 e) | InlineAbstraction _ pm ex <- reduce e1 = applyTerm e pm ex
  reduce (PolyElimination _ e θ) | PolyIntroduction _ e <- reduce e = reduce $ applyScheme e θ
  reduce e = mapTerm go id bound bound go e
    where
      go = reduce
      bound pm e = (pm, reduce e)

instance TermAlgebra TermScheme where
  freeVariablesTerm (MonoTerm e) = freeVariablesTerm e
  freeVariablesTerm (TypeAbstraction _ _ _ e) = freeVariablesTerm e
  substituteTerms θ (MonoTerm e) = MonoTerm $ substituteTerms θ e
  substituteTerms θ (TypeAbstraction x π κ e) =
    TypeAbstraction x' π κ (go e')
    where
      variables = termSubstitutionLocalTypeVariables θ
      x' = fresh variables x
      e' = convertType x' x e
      go = substituteTerms θ

  reduce (MonoTerm e) = MonoTerm (reduce e)
  reduce (TypeAbstraction x π κ e) = TypeAbstraction x π κ (reduce e)

instance Binder (TermPattern p v) where
  bindings = \case
    MatchVariable _ x _ -> Set.singleton x
    MatchTuple _ pms -> foldMap bindings pms
    MatchBoolean _ _ -> Set.empty
  rename ux x = \case
    MatchVariable p x' σ
      | x == x' -> MatchVariable p ux σ
      | otherwise -> MatchVariable p x' σ
    MatchTuple p pms -> MatchTuple p (map (rename ux x) pms)
    MatchBoolean p b -> MatchBoolean p b

instance Binder (TermMetaPattern p v) where
  bindings = \case
    InlineMatchVariable _ x _ _ -> Set.singleton x
  rename ux x = \case
    InlineMatchVariable p x' π σ
      | x == x' ->
        InlineMatchVariable p ux π σ
      | otherwise ->
        InlineMatchVariable p x' π σ

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
convertType ux x = substituteType (TypeVariable ux) x

substituteType :: TypeAlgebra u => Type v -> TypeIdentifier -> u v -> u v
substituteType ux x = substituteTypes (TypeSubstitution (Map.singleton x ux) Map.empty)

substituteLogical f = runIdentity . zonkType (Identity . f)

instance TypeAlgebra (Term p) where
  freeLocalVariablesType = foldTerm go go bound bound go
    where
      go = freeLocalVariablesType
      bound pm e = go pm <> go e
  substituteTypes θ = mapTerm go go bound bound go
    where
      bound pm e = (go pm, go e)
      go = substituteTypes θ
  zonkType f = traverseTerm go go bound bound go
    where
      go = zonkType f
      bound pm e = pure (,) <*> zonkType f pm <*> zonkType f e
  simplify = mapTerm go go bound bound go
    where
      go = simplify
      bound pm e = (simplify pm, simplify e)

instance TypeAlgebra (TermScheme p) where
  freeLocalVariablesType (MonoTerm e) = freeLocalVariablesType e
  freeLocalVariablesType (TypeAbstraction x _ κ e) =
    go κ <> Set.delete x (go e)
    where
      go = freeLocalVariablesType
  substituteTypes θ (MonoTerm e) = MonoTerm (substituteTypes θ e)
  substituteTypes θ (TypeAbstraction x π κ e)
    | Set.member x (typeSubstitutionShadow θ) = TypeAbstraction x π (go κ) e
    | otherwise = TypeAbstraction x' π (go κ) (go e')
    where
      variables = typeSubstitutionLocalVariables θ
      x' = fresh variables x
      e' = convertType x' x e
      go = substituteTypes θ

  zonkType f (MonoTerm e) = MonoTerm <$> zonkType f e
  zonkType f (TypeAbstraction x π κ λ) = TypeAbstraction x π <$> zonkType f κ <*> zonkType f λ

  simplify (MonoTerm e) = MonoTerm (simplify e)
  simplify (TypeAbstraction x π κ λ) = TypeAbstraction x π (simplify κ) (simplify λ)

instance TypeAlgebra (TermMetaPattern p) where
  freeLocalVariablesType = \case
    InlineMatchVariable _ _ π σ -> go π <> go σ
      where
        go = freeLocalVariablesType
  substituteTypes θ = \case
    InlineMatchVariable p x π σ -> InlineMatchVariable p x (go π) (go σ)
    where
      go = substituteTypes θ

  zonkType f (InlineMatchVariable p x π σ) =
    InlineMatchVariable p x <$> zonkType f π <*> zonkType f σ
  simplify (InlineMatchVariable p x π σ) =
    InlineMatchVariable p x (simplify π) (simplify σ)

instance TypeAlgebra (TermPattern p) where
  freeLocalVariablesType = \case
    MatchVariable _ _ σ -> go σ
    MatchTuple _ pms -> foldMap go pms
    MatchBoolean _ _ -> mempty
    where
      go = freeLocalVariablesType
  substituteTypes θ = \case
    MatchVariable p x σ -> MatchVariable p x (go σ)
    MatchTuple p pms -> MatchTuple p (map go pms)
    MatchBoolean p b -> MatchBoolean p b
    where
      go = substituteTypes θ
  zonkType f = \case
    MatchVariable p x σ -> MatchVariable p x <$> zonkType f σ
    MatchTuple p pms -> MatchTuple p <$> traverse (zonkType f) pms
    MatchBoolean p b -> pure (MatchBoolean p b)

  simplify = \case
    MatchVariable p x σ ->
      MatchVariable p x (simplify σ)
    MatchTuple p pms ->
      MatchTuple p (map simplify pms)
    MatchBoolean p b -> MatchBoolean p b

instance TypeAlgebra Type where
  freeLocalVariablesType (TypeVariable x) = Set.singleton x
  freeLocalVariablesType σ = foldType mempty scheme typex σ
    where
      typex = freeLocalVariablesType
      scheme σ λ = freeLocalVariablesType σ <> freeLocalVariablesType λ
  substituteTypes (TypeSubstitution xs _) (TypeVariable x)
    | Just σ <- Map.lookup x xs = σ
  substituteTypes (TypeSubstitution _ xs) (TypeGlobalVariable x)
    | Just σ <- Map.lookup x xs = σ
  substituteTypes θ σ = mapType TypeLogical bound go σ
    where
      bound σ λ = TypeScheme (go σ) (go λ)
      go = substituteTypes θ
  zonkType f = traverseType f scheme typex
    where
      typex = zonkType f
      scheme σ λ = TypeScheme <$> zonkType f σ <*> zonkType f λ

  simplify σ = case σ of
    TypeLogical {} -> normalize
    TypeVariable {} -> normalize
    TypeGlobalVariable {} -> normalize
    World {} -> normalize
    TypeTrue {} -> normalize
    TypeFalse {} -> normalize
    TypeAnd {} -> normalize
    TypeOr {} -> normalize
    TypeXor {} -> normalize
    TypeNot {} -> normalize
    _ -> mapType TypeLogical scheme simplify σ
      where
        scheme σ λ = TypeScheme (simplify σ) (simplify λ)
    where
      normalize = unconvertBoolean (convertBoolean σ)

instance TypeAlgebra TypeScheme where
  freeLocalVariablesType (MonoType σ) = freeLocalVariablesType σ
  freeLocalVariablesType (TypeForall x _ κ σ) =
    freeLocalVariablesType κ <> Set.delete x (freeLocalVariablesType σ)

  substituteTypes θ (MonoType σ) = MonoType $ substituteTypes θ σ
  substituteTypes θ (TypeForall x π κ σ)
    | Set.member x (typeSubstitutionShadow θ) =
      TypeForall x π (go κ) (substituteTypes (typeSubstitutionMask x θ) σ)
    | otherwise = TypeForall x' π (go κ) (go σ')
    where
      variables = typeSubstitutionLocalVariables θ
      x' = fresh variables x
      σ' = convertType x' x σ
      go = substituteTypes θ
  zonkType f (MonoType σ) = MonoType <$> zonkType f σ
  zonkType f (TypeForall x π κ λ) = TypeForall x π <$> zonkType f κ <*> zonkType f λ

  simplify (MonoType σ) = MonoType (simplify σ)
  simplify (TypeForall x π κ λ) = TypeForall x π (simplify κ) (simplify λ)

instance TypeAlgebra LabelScheme where
  freeLocalVariablesType (MonoLabel σ) = freeLocalVariablesType σ
  freeLocalVariablesType (LabelForall x σ) = Set.delete x (freeLocalVariablesType σ)
  substituteTypes θ (MonoLabel σ) = MonoLabel (substituteTypes θ σ)
  substituteTypes θ (LabelForall x σ)
    | Set.member x (typeSubstitutionShadow θ) = LabelForall x σ
    | otherwise = LabelForall x' (go σ')
    where
      variables = typeSubstitutionLocalVariables θ
      x' = fresh variables x
      σ' = convertType x' x σ
      go = substituteTypes θ

  zonkType f (MonoLabel σ) = MonoLabel <$> zonkType f σ
  zonkType f (LabelForall x λ) = LabelForall x <$> zonkType f λ

  simplify (MonoLabel σ) = MonoLabel (simplify σ)
  simplify (LabelForall x λ) = LabelForall x (simplify λ)

data TypeCore
  = CoreWorld
  | CoreVariable TypeIdentifier
  | CoreGlobalVariable TypeGlobalIdentifier
  deriving (Show, Eq, Ord)

convertBoolean :: Ord v => Type v -> Boolean.Polynomial TypeCore v
convertBoolean = \case
  TypeLogical v -> Boolean.variable v
  TypeVariable x -> Boolean.constant (CoreVariable x)
  TypeGlobalVariable x -> Boolean.constant (CoreGlobalVariable x)
  World -> Boolean.constant CoreWorld
  TypeTrue -> 1
  TypeFalse -> 0
  TypeAnd σ τ -> convertBoolean σ * convertBoolean τ
  TypeOr σ τ -> x + y + x * y
    where
      x = convertBoolean σ
      y = convertBoolean τ
  TypeXor σ τ -> convertBoolean σ + convertBoolean τ
  TypeNot σ -> convertBoolean σ + 1
  _ -> error "convert boolean error"

unconvertBoolean :: Boolean.Polynomial TypeCore v -> Type v
unconvertBoolean (Boolean.Polynomial e)
  | Set.null e = TypeFalse
  | otherwise = foldl1 TypeXor (map prod $ Set.toList e)
  where
    prod e
      | Set.null e = TypeTrue
      | otherwise = foldl1 TypeAnd (map var $ Set.toList e)
      where
        var = \case
          Boolean.Flexible v -> TypeLogical v
          Boolean.Constant c -> case c of
            CoreVariable x -> TypeVariable x
            CoreGlobalVariable x -> TypeGlobalVariable x
            CoreWorld -> World

textType :: TermSchemeInfer p -> TypeSchemeInfer
textType = \case
  TypeAbstraction x er κ e -> TypeForall x er κ (textType e)
  MonoTerm (FunctionLiteral _ pm τ π _) -> MonoType (FunctionLiteralType (patternType pm) π τ)
    where
      patternType pm = case pm of
        MatchVariable _ _ σ -> σ
        MatchTuple _ pms -> Tuple (map patternType pms)
        MatchBoolean _ _ -> Boolean
  _ -> error "expected function literal"

makeExtern ::
  Path ->
  p ->
  TypeSchemeInfer ->
  TermSchemeInfer p
makeExtern path p ς = case ς of
  MonoType (FunctionLiteralType σ π τ) ->
    MonoTerm $ Extern p (mangle path) σ π τ
  TypeForall x π κ e ->
    TypeAbstraction x π κ $ makeExtern path p e
  _ -> error "not function literal"

-- uses integers as type names
-- so integers cannot be type names (as is currently enforced by the syntax)
-- type logicals are ignored
relabel :: TypeScheme v -> LabelScheme v
relabel ς = foldr LabelForall (MonoLabel ς') (map labelN [0 .. n - 1])
  where
    (ς', n) = runState (scheme ς) 0
    labelN = TypeIdentifier . show

    typex = traverseType (pure . TypeLogical) typeScheme typex
    typeScheme _ λ = do
      n <- get
      put $ n + 1
      λ <- scheme λ
      pure $ TypeScheme (TypeVariable $ labelN n) λ
    scheme (MonoType σ) = MonoType <$> typex σ
    scheme (TypeForall x π κ ς) = do
      κ <- typex κ
      ς <- scheme ς
      pure $ TypeForall x π κ ς

reduceModule :: [(Path, Global p)] -> [(Path, Global p)]
reduceModule = reduceModule Map.empty
  where
    reduceModule ::
      Map TermGlobalIdentifier (TermSchemeInfer p) ->
      [(Path, Global p)] ->
      [(Path, Global p)]
    reduceModule _ [] = []
    reduceModule globals ((path, item) : nodes) =
      (path, item') : reduceModule globals' nodes
      where
        (item', binding) = case item of
          Macro e ->
            let e' = reduce $ applyGlobalTerms e
             in (Macro e', Just e')
          Text e ->
            let e' = reduce $ applyGlobalTerms e
             in (Text e', Just (makeExtern path (error "todo scheme position") $ textType e))
          Synonym σ ->
            (Synonym σ, Nothing)
          ForwardNewType κ ->
            (ForwardNewType κ, Nothing)
          ForwardText σ ->
            let p = error "todo use actual position"
             in (ForwardText σ, Just (makeExtern path p σ))

        globals' = case binding of
          Nothing -> globals
          Just e -> Map.insert (TermGlobalIdentifier path) e globals
        applyGlobalTerms e = substituteTerms (TermSubstitution Map.empty globals Map.empty) e where

nameType :: TypeUnify -> Surface.Type ()
nameType = typex . substituteLogical name
  where
    name (TypeLogicalRaw i) = TypeVariable $ TypeIdentifier $ show i

global :: Global p -> Surface.Global ()
global = \case
  Text e -> Surface.Text (Surface.TermManual $ termScheme e)
  Macro e -> Surface.Macro (Surface.TermManual $ termScheme e)
  Synonym σ -> Surface.Synonym (typex σ)
  ForwardNewType σ -> Surface.ForwardNewType (typex σ)
  ForwardText σ -> Surface.ForwardText (typeScheme σ)

term :: TermInfer p -> Surface.Term ()
term = \case
  Variable _ x θ -> Surface.Variable () x (instantiation θ)
  GlobalVariable _ x θ -> Surface.GlobalVariable () x (instantiation θ)
  Let _ pm e1 e2 -> Surface.Let () (termPattern False pm) (term e1) (term e2)
  Case _ e _ [] σ -> Surface.PretypeAnnotation () (Surface.Case () (term e) []) (typex σ)
  Case _ e _ λs _ -> Surface.Case () (term e) (map (\(pm, e) -> (termPattern True pm, term e)) λs)
  Extern _ sym σ π τ -> Surface.PretypeAnnotation () (Surface.Extern () sym) (Surface.FunctionPointer () (typex σ) (typex π) (typex τ))
  Application _ e1 e2 _ -> Surface.Application () (term e1) (term e2)
  TupleLiteral _ es -> Surface.TupleLiteral () (map term es)
  Read _ e -> Surface.Read () (term e)
  Write _ e1 e2 _ -> Surface.Write () (term e1) (term e2)
  NumberLiteral _ i σ -> Surface.PretypeAnnotation () (Surface.NumberLiteral () i) (typex σ)
  Arithmatic _ o e1 e2 _ -> Surface.Arithmatic () o (term e1) (term e2)
  Relational _ o e1 e2 _ _ -> Surface.Relational () o (term e1) (term e2)
  BooleanLiteral _ b -> Surface.BooleanLiteral () b
  PointerAddition _ e1 e2 _ -> Surface.PointerAddition () (term e1) (term e2)
  Continue _ e σ -> Surface.PretypeAnnotation () (Surface.Continue () (term e)) (typex σ)
  Break _ e σ -> Surface.PretypeAnnotation () (Surface.Break () (term e)) (typex σ)
  Loop _ pm e1 e2 -> Surface.Loop () (termPattern False pm) (term e1) (term e2)
  Isolate _ e -> Surface.Isolate () (term e)
  Cast _ e σ -> Surface.TypeAnnotation () (Surface.Cast () (term e)) (typex σ)
  Not _ e -> Surface.Not () (term e)
  And _ e1 e2 -> Surface.And () (term e1) (term e2)
  Or _ e1 e2 -> Surface.Or () (term e1) (term e2)
  Do _ e1 e2 -> Surface.Do () (term e1) (term e2)
  If _ e1 e2 e3 -> Surface.If () (term e1) (term e2) (term e3)
  FunctionLiteral _ pm σ τ e -> Surface.FunctionLiteral () (termPattern True pm) (typex σ) (typex τ) (term e)
  InlineAbstraction _ pm e -> Surface.InlineAbstraction () (termMetaPattern pm) (term e)
  InlineApplication _ e1 e2 -> Surface.InlineApplication () (term e1) (term e2)
  InlineLet _ pm e1 e2 -> Surface.InlineLet () (termMetaPattern pm) (term e1) (term e2)
  PolyIntroduction _ λ -> Surface.PolyIntroduction () (termScheme λ)
  PolyElimination _ e θ -> Surface.PolyElimination () (term e) (instantiation θ)

termScheme :: TermSchemeInfer p -> Surface.TermScheme ()
termScheme = \case
  MonoTerm e -> Surface.MonoTerm (term e)
  TypeAbstraction x er π e -> Surface.TypeAbstraction (Surface.TypePattern () x er (typex π)) (termScheme e)

termPattern :: Bool -> TermPatternInfer p -> Surface.TermPattern ()
termPattern annotate = \case
  MatchVariable _ x σ -> Surface.MatchVariable () x (if annotate then typex σ else Surface.Hole ())
  MatchTuple _ pms -> Surface.MatchTuple () (map (termPattern annotate) pms)
  MatchBoolean _ b -> Surface.MatchBoolean () b

termMetaPattern :: TermMetaPatternInfer p -> Surface.TermMetaPattern ()
termMetaPattern (InlineMatchVariable _ x π σ) = Surface.InlineMatchVariable () x (typex π) (typex σ)

instantiation :: [TypeInfer] -> Surface.Instantiation ()
instantiation [] = Surface.InstantiationInfer
instantiation θ = Surface.Instantiation (map typex θ)

typex :: TypeInfer -> Surface.Type ()
typex = \case
  TypeLogical v -> absurd v
  TypeVariable x -> Surface.TypeVariable () x
  TypeGlobalVariable x -> Surface.TypeGlobalVariable () x
  TypeTrue -> Surface.TypeTrue ()
  TypeFalse -> Surface.TypeFalse ()
  TypeNot σ -> Surface.TypeNot () (typex σ)
  TypeAnd σ τ -> Surface.TypeAnd () (typex σ) (typex τ)
  TypeOr σ τ -> Surface.TypeOr () (typex σ) (typex τ)
  TypeXor σ τ -> Surface.TypeXor () (typex σ) (typex τ)
  World -> Surface.World ()
  Inline σ π τ -> Surface.Inline () (typex σ) (typex π) (typex τ)
  FunctionPointer σ π τ -> Surface.FunctionPointer () (typex σ) (typex π) (typex τ)
  FunctionLiteralType σ π τ -> Surface.FunctionLiteralType () (typex σ) (typex π) (typex τ)
  Tuple σs -> Surface.Tuple () (map typex σs)
  Effect σ π -> Surface.Effect () (typex σ) (typex π)
  Unique σ -> Surface.Unique () (typex σ)
  Shared σ π -> Surface.Shared () (typex σ) (typex π)
  Pointer σ -> Surface.Pointer () (typex σ)
  Array σ -> Surface.Array () (typex σ)
  Number σ τ -> Surface.Number () (typex σ) (typex τ)
  Boolean -> Surface.Boolean ()
  Step σ τ -> Surface.Step () (typex σ) (typex τ)
  Type -> Surface.Type ()
  Region -> Surface.Region ()
  Multiplicity -> Surface.Multiplicity ()
  Pretype σ τ -> Surface.Pretype () (typex σ) (typex τ)
  Boxed -> Surface.Boxed ()
  PointerRepresentation -> Surface.PointerRepresentation ()
  StructRepresentation σs -> Surface.StructRepresentation () (map typex σs)
  UnionRepresentation σs -> Surface.UnionRepresentation () (map typex σs)
  WordRepresentation σ -> Surface.WordRepresentation () (typex σ)
  Signed -> Surface.Signed ()
  Unsigned -> Surface.Unsigned ()
  Byte -> Surface.Byte ()
  Short -> Surface.Short ()
  Int -> Surface.Int ()
  Long -> Surface.Long ()
  Native -> Surface.Native ()
  Representation -> Surface.Representation ()
  Size -> Surface.Size ()
  Signedness -> Surface.Signedness ()
  Kind σ -> Surface.Kind () (typex σ)
  Syntactic -> Surface.Syntactic ()
  Propositional -> Surface.Propositional ()
  Unification -> Surface.Unification ()
  AmbiguousLabel -> Surface.AmbiguousLabel ()
  Label -> Surface.Label ()
  Top -> Surface.Top ()
  TypeScheme _ λ -> Surface.TypeScheme () (typeScheme λ)

typeScheme :: TypeSchemeInfer -> Surface.TypeScheme ()
typeScheme = \case
  MonoType σ -> Surface.MonoType (typex σ)
  TypeForall x π κ λ ->
    Surface.TypeForall (Surface.TypePattern () x π (typex κ)) (typeScheme λ)
