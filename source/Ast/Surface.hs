module Ast.Surface where

import Ast.Symbol
import Control.Category ((.))
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (for)
import Misc.Isomorph
import Misc.Prism
import Misc.Util (sortTopological)
import Prelude hiding (id, (.))

data Variables p = Variables
  { termLocals :: Map TermIdentifier p,
    termGlobals :: Map TermGlobalIdentifier p,
    typeLocals :: Map TypeIdentifier p,
    typeGlobals :: Map TypeGlobalIdentifier p
  }

termLocal x p = Variables (Map.singleton x p) Map.empty Map.empty Map.empty

termGlobal x p = Variables Map.empty (Map.singleton x p) Map.empty Map.empty

typeLocal x p = Variables Map.empty Map.empty (Map.singleton x p) Map.empty

typeGlobal x p = Variables Map.empty Map.empty Map.empty (Map.singleton x p)

deleteTermLocal x variables = variables {termLocals = Map.delete x $ termLocals variables}

deleteTypeLocal x variables = variables {typeLocals = Map.delete x $ typeLocals variables}

instance Semigroup p => Semigroup (Variables p) where
  Variables a b c d <> Variables a' b' c' d' =
    let go = Map.unionWith (<>) in Variables (go a a') (go b b') (go c c') (go d d')

instance Semigroup p => Monoid (Variables p) where
  mappend = (<>)
  mempty = let go = Map.empty in Variables go go go go

class Alpha u where
  freeVariables :: Semigroup p => u p -> Variables p

class TermBindings pm where
  bindings :: pm -> [TermIdentifier]

class Position e where
  position :: e p -> p

data Global p
  = Text (TermControl p)
  | Macro (TermControl p)
  | Synonym (Type p)
  | ForwardText (TypeScheme p)
  | ForwardNewType (Type p)
  deriving (Show, Functor, Foldable, Traversable)

-- todo inline these two
data Arithmatic
  = Addition
  | Subtraction
  | Multiplication
  | Division
  deriving (Show, Eq)

data Relational
  = Equal
  | NotEqual
  | LessThen
  | LessThenEqual
  | GreaterThen
  | GreaterThenEqual
  deriving (Show, Eq)

data Term p
  = Variable p TermIdentifier (Instantiation p)
  | GlobalVariable p TermGlobalIdentifier (Instantiation p)
  | Let p (TermPattern p) (Term p) (Term p)
  | Case p (Term p) [(TermPattern p, Term p)]
  | Extern p Symbol
  | Application p (Term p) (Term p)
  | TupleLiteral p [Term p]
  | Read p (Term p)
  | Write p (Term p) (Term p)
  | NumberLiteral p Integer
  | Arithmatic p Arithmatic (Term p) (Term p)
  | Relational p Relational (Term p) (Term p)
  | BooleanLiteral p Bool
  | PointerAddition p (Term p) (Term p)
  | Continue p (Term p)
  | Break p (Term p)
  | Loop p (TermPattern p) (Term p) (Term p)
  | Isolate p (Term p)
  | Cast p (Term p)
  | Not p (Term p)
  | And p (Term p) (Term p)
  | Or p (Term p) (Term p)
  | Do p (Term p) (Term p)
  | If p (Term p) (Term p) (Term p)
  | TypeAnnotation p (Term p) (Type p)
  | PretypeAnnotation p (Term p) (Type p)
  | FunctionLiteral p (TermPattern p) (Type p) (Type p) (Term p)
  | InlineAbstraction p (TermMetaPattern p) (Term p)
  | InlineApplication p (Term p) (Term p)
  | InlineLet p (TermMetaPattern p) (Term p) (Term p)
  | PolyIntroduction p (TermScheme p)
  | PolyElimination p (Term p) (Instantiation p)
  deriving (Show, Functor, Foldable, Traversable)

data TermPattern p
  = MatchVariable p TermIdentifier (Type p)
  | MatchTuple p [TermPattern p]
  | MatchBoolean p Bool
  deriving (Show, Functor, Foldable, Traversable)

data TermMetaPattern p
  = InlineMatchVariable p TermIdentifier (Type p) (Type p)
  deriving (Show, Functor, Foldable, Traversable)

data TermScheme p
  = MonoTerm (Term p)
  | TypeAbstraction (TypePattern p) (TermScheme p)
  deriving (Show, Functor, Foldable, Traversable)

data TermControl p
  = TermAuto (Term p)
  | TermManual (TermScheme p)
  deriving (Show, Functor, Foldable, Traversable)

data Type p
  = TypeVariable p TypeIdentifier
  | TypeGlobalVariable p TypeGlobalIdentifier
  | TypeTrue p
  | TypeFalse p
  | TypeNot p (Type p)
  | TypeAnd p (Type p) (Type p)
  | TypeOr p (Type p) (Type p)
  | TypeXor p (Type p) (Type p)
  | World p
  | Inline p (Type p) (Type p) (Type p)
  | FunctionPointer p (Type p) (Type p) (Type p)
  | FunctionLiteralType p (Type p) (Type p) (Type p)
  | Tuple p [Type p]
  | Effect p (Type p) (Type p)
  | Unique p (Type p)
  | Shared p (Type p) (Type p)
  | Pointer p (Type p)
  | Array p (Type p)
  | Number p (Type p) (Type p)
  | Boolean p
  | Step p (Type p) (Type p)
  | Type p
  | Region p
  | Multiplicity p
  | Pretype p (Type p) (Type p)
  | Boxed p
  | PointerRepresentation p
  | StructRepresentation p [Type p]
  | UnionRepresentation p [Type p]
  | WordRepresentation p (Type p)
  | Signed p
  | Unsigned p
  | Byte p
  | Short p
  | Int p
  | Long p
  | Native p
  | Representation p
  | Size p
  | Signedness p
  | Kind p (Type p)
  | Syntactic p
  | Propositional p
  | Unification p
  | AmbiguousLabel p
  | Label p
  | Top p
  | TypeScheme p (TypeScheme p)
  | Hole p
  deriving (Show, Functor, Foldable, Traversable)

data TypeScheme p
  = MonoType (Type p)
  | TypeForall (TypePattern p) (TypeScheme p)
  deriving (Show, Functor, Foldable, Traversable)

data Erasure
  = Transparent
  | Concrete
  deriving (Show)

data TypePattern p = TypePattern p TypeIdentifier Erasure (Type p)
  deriving (Show, Functor, Foldable, Traversable)

data Instantiation p
  = Instantiation [Type p]
  | InstantiationInfer
  deriving (Show, Functor, Foldable, Traversable)

instance Position Term where
  position = head . toList

instance Position TermScheme where
  position = head . toList

instance Position Type where
  position = head . toList

instance Position Global where
  position = head . toList

instance Alpha Term where
  freeVariables = \case
    Variable p x θ -> termLocal x p <> go θ
    GlobalVariable p x θ -> termGlobal x p <> go θ
    Let _ pm e1 e2 -> go e1 <> goBound pm e2
    Case _ e λ -> go e <> foldMap (uncurry goBound) λ
    Extern _ _ -> mempty
    Application _ e1 e2 -> goMany [e1, e2]
    TupleLiteral _ es -> goMany es
    Read _ e -> go e
    Write _ e1 e2 -> goMany [e1, e2]
    NumberLiteral _ _ -> mempty
    Arithmatic _ _ e1 e2 -> goMany [e1, e2]
    Relational _ _ e1 e2 -> goMany [e1, e2]
    BooleanLiteral _ _ -> mempty
    PointerAddition _ e1 e2 -> goMany [e1, e2]
    Continue _ e -> go e
    Break _ e -> go e
    Loop _ pm e1 e2 -> go e1 <> goBound pm e2
    Isolate _ e -> go e
    Cast _ e -> go e
    Not _ e -> go e
    And _ e1 e2 -> goMany [e1, e2]
    Or _ e1 e2 -> goMany [e1, e2]
    Do _ e1 e2 -> goMany [e1, e2]
    If _ e1 e2 e3 -> goMany [e1, e2, e3]
    TypeAnnotation _ e σ -> go e <> go σ
    PretypeAnnotation _ e σ -> go e <> go σ
    FunctionLiteral _ pm σ τ e -> goMany [σ, τ] <> goBound pm e
    InlineAbstraction _ pm e -> goBound pm e
    InlineApplication _ e1 e2 -> goMany [e1, e2]
    InlineLet _ pm e1 e2 -> go e1 <> goBound pm e2
    PolyIntroduction _ λ -> go λ
    PolyElimination _ e θ -> go e <> go θ
    where
      go = freeVariables
      goBound pm e = freeVariables pm <> foldr deleteTermLocal (freeVariables e) (bindings pm)
      goMany = foldMap go

instance Alpha TermScheme where
  freeVariables (MonoTerm e) = freeVariables e
  freeVariables (TypeAbstraction (TypePattern _ x _ κ) e) =
    freeVariables κ <> deleteTypeLocal x (freeVariables e)

instance Alpha TermControl where
  freeVariables (TermManual e) = freeVariables e
  freeVariables (TermAuto e) = freeVariables e

instance Alpha TermPattern where
  freeVariables = \case
    MatchVariable _ _ σ -> go σ
    MatchTuple _ pms -> foldMap go pms
    MatchBoolean _ _ -> mempty
    where
      go = freeVariables

instance Alpha TermMetaPattern where
  freeVariables = \case
    InlineMatchVariable _ _ π σ ->
      freeVariables π <> freeVariables σ

instance TermBindings (TermPattern p) where
  bindings = \case
    MatchVariable _ x _ -> [x]
    MatchTuple _ pms -> foldMap bindings pms
    MatchBoolean _ _ -> mempty

instance TermBindings (TermMetaPattern p) where
  bindings = \case
    InlineMatchVariable _ x _ _ -> [x]

instance Alpha Type where
  freeVariables = \case
    TypeVariable p x -> typeLocal x p
    TypeGlobalVariable p x -> typeGlobal x p
    TypeTrue _ -> mempty
    TypeFalse _ -> mempty
    TypeNot _ σ -> go σ
    TypeAnd _ σ τ -> goMany [σ, τ]
    TypeOr _ σ τ -> goMany [σ, τ]
    TypeXor _ σ τ -> goMany [σ, τ]
    World _ -> mempty
    Inline _ σ π τ -> goMany [σ, π, τ]
    FunctionPointer _ σ π τ -> goMany [σ, π, τ]
    FunctionLiteralType _ σ π τ -> goMany [σ, π, τ]
    Tuple _ σs -> goMany σs
    Effect _ σ π -> goMany [σ, π]
    Unique _ σ -> go σ
    Shared _ σ π -> goMany [σ, π]
    Pointer _ σ -> go σ
    Array _ σ -> go σ
    Number _ σ τ -> goMany [σ, τ]
    Boolean _ -> mempty
    Step _ σ τ -> goMany [σ, τ]
    Type _ -> mempty
    Region _ -> mempty
    Multiplicity _ -> mempty
    Pretype _ σ τ -> goMany [σ, τ]
    Boxed _ -> mempty
    PointerRepresentation _ -> mempty
    StructRepresentation _ σ -> goMany σ
    UnionRepresentation _ σ -> goMany σ
    WordRepresentation _ σ -> go σ
    Signed _ -> mempty
    Unsigned _ -> mempty
    Byte _ -> mempty
    Short _ -> mempty
    Int _ -> mempty
    Long _ -> mempty
    Native _ -> mempty
    Representation _ -> mempty
    Size _ -> mempty
    Signedness _ -> mempty
    Kind _ κ -> go κ
    Syntactic _ -> mempty
    Propositional _ -> mempty
    Unification _ -> mempty
    AmbiguousLabel _ -> mempty
    Label _ -> mempty
    Top _ -> mempty
    TypeScheme _ λ -> freeVariables λ
    Hole _ -> mempty
    where
      go = freeVariables
      goMany = foldMap freeVariables

instance Alpha TypeScheme where
  freeVariables (MonoType σ) = freeVariables σ
  freeVariables (TypeForall (TypePattern _ x _ κ) σ) =
    freeVariables κ <> deleteTypeLocal x (freeVariables σ)

instance Alpha Instantiation where
  freeVariables InstantiationInfer = mempty
  freeVariables (Instantiation θ) = foldMap freeVariables θ

annotated :: TermControl p -> Maybe (TypeScheme p)
annotated (TermManual e) = annotatedScheme e
  where
    annotatedScheme (MonoTerm e) = MonoType <$> annotatedTerm e
    annotatedScheme (TypeAbstraction pm e) = TypeForall pm <$> annotatedScheme e
    annotatedTerm (FunctionLiteral p pm τ π _)
      | Hole _ <- τ = Nothing
      | Hole _ <- π = Nothing
      | otherwise = FunctionLiteralType p <$> annotatedPattern pm <*> Just π <*> Just τ
    annotatedTerm _ = Nothing
    annotatedPattern (MatchVariable _ _ (Hole _)) = Nothing
    annotatedPattern (MatchVariable _ _ σ) = Just σ
    annotatedPattern (MatchTuple p pms) = Tuple p <$> traverse annotatedPattern pms
    annotatedPattern (MatchBoolean p _) = Just $ Boolean p
annotated (TermAuto _) = Nothing

data Origin = Manual | Auto

data ModuleError p
  = IllegalPath p Path
  | Cycle p Path
  | Duplicate p Path
  deriving (Show)

removeInserted :: [(Origin, a, b)] -> [(a, b)]
removeInserted items = do
  (existance, a, b) <- items
  case existance of
    Manual -> [(a, b)]
    Auto -> []

order :: Semigroup p => Map Path (NonEmpty (Global p)) -> Either (ModuleError p) [(Origin, Path, Global p)]
order code = sortTopological key quit children globals <* validateDuplicates code
  where
    key (_, path, item) = (forward, path)
      where
        forward = case item of
          ForwardNewType _ -> True
          ForwardText _ -> True
          _ -> False
    quit (_, path, item) = Left $ Cycle (position item) path
    children (_, path, item) = fmap concat $
      for (Map.toList $ depend path item) $ \(path, p) -> do
        case Map.lookup path code of
          Nothing -> Left $ IllegalPath p path
          Just (Text e :| [])
            | Just σ <- annotated e ->
              pure [(Auto, path, ForwardText σ)]
          Just (global :| []) -> pure [(Manual, path, global)]
          Just (_ :| _) -> error "unexpected module item"
    globals =
      Map.toList code >>= \(path, items) -> do
        item <- NonEmpty.toList items
        pure (Manual, path, item)

    depend path item = case item of
      Macro e -> free e
      Text e -> free e
      Synonym σ -> free σ
      ForwardNewType σ -> free σ
      ForwardText ς -> free ς
      where
        scope = Map.mapKeysMonotonic (combine (directory path))
        free e =
          let (Variables {termLocals, termGlobals, typeLocals, typeGlobals}) = freeVariables e
              termLocals' = scope $ Map.mapKeysMonotonic runTermIdentifier termLocals
              termGlobals' = Map.mapKeysMonotonic runTermGlobalIdentifier termGlobals
              typeLocals' = scope $ Map.mapKeysMonotonic runTypeIdentifier typeLocals
              typeGlobals' = Map.mapKeysMonotonic runTypeGlobalIdentifier typeGlobals
           in foldr (Map.unionWith (<>)) (Map.empty) [termLocals', termGlobals', typeLocals', typeGlobals']

    validateDuplicates :: Map Path (NonEmpty (Global p)) -> Either (ModuleError p) ()
    validateDuplicates code = Map.traverseWithKey check code >> pure ()
      where
        check _ (_ :| []) = Right ()
        check path (global :| _) = Left (Duplicate (position global) path)

termIdentifier = Isomorph TermIdentifier runTermIdentifier

termGlobalIdentifier = Isomorph TermGlobalIdentifier runTermGlobalIdentifier

typeIdentifier = Isomorph TypeIdentifier runTypeIdentifier

typeGlobalIdentifier = Isomorph TypeGlobalIdentifier runTypeGlobalIdentifier

text = Prism to from
  where
    to = Text
    from (Text e) = Just e
    from _ = Nothing

macro = Prism to from
  where
    to = Macro
    from (Macro e) = Just e
    from _ = Nothing

synonym = Prism to from
  where
    to = Synonym
    from (Synonym σ) = Just σ
    from _ = Nothing

forwardText = Prism to from
  where
    to = ForwardText
    from (ForwardText σ) = Just σ
    from _ = Nothing

forwardNewtype = Prism to from
  where
    to = ForwardNewType
    from (ForwardNewType σ) = Just σ
    from _ = Nothing

variable = Prism to from . toPrism tuple3
  where
    to (p, x, θ) = Variable p x θ
    from (Variable p x θ) = Just (p, x, θ)
    from _ = Nothing

globalVariable = Prism to from . toPrism tuple3
  where
    to (p, x, θ) = GlobalVariable p x θ
    from (GlobalVariable p x θ) = Just (p, x, θ)
    from _ = Nothing

letx = Prism to from . toPrism tuple4'
  where
    to (p, pm, e, e') = Let p pm e e'
    from (Let p pm e e') = Just (p, pm, e, e')
    from _ = Nothing

casex = Prism to from . toPrism tuple3'
  where
    to (p, e, λs) = Case p e λs
    from (Case p e λs) = Just (p, e, λs)
    from _ = Nothing

extern = Prism to from
  where
    to (p, sym) = Extern p sym
    from (Extern p sym) = Just (p, sym)
    from _ = Nothing

application = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Application p e e'
    from (Application p e e') = Just (e, p, e')
    from _ = Nothing

tupleLiteral = Prism to from
  where
    to (p, es) = TupleLiteral p es
    from (TupleLiteral p es) = Just (p, es)
    from _ = Nothing

read = Prism to from
  where
    to (p, e) = Read p e
    from (Read p e) = Just (p, e)
    from _ = Nothing

write = Prism to from . toPrism tuple3'
  where
    to (p, e, e') = Write p e e'
    from (Write p e e') = Just (p, e, e')
    from _ = Nothing

numberLiteral = Prism to from
  where
    to (p, n) = NumberLiteral p n
    from (NumberLiteral p n) = Just (p, n)
    from _ = Nothing

arithmatic o = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Arithmatic p o e e'
    from (Arithmatic p o' e e') | o == o' = Just (e, p, e')
    from _ = Nothing

relational o = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Relational p o e e'
    from (Relational p o' e e') | o == o' = Just (e, p, e')
    from _ = Nothing

booleanLiteral b = Prism to from
  where
    to p = BooleanLiteral p b
    from (BooleanLiteral p b') | b == b' = Just p
    from _ = Nothing

true = booleanLiteral True

false = booleanLiteral False

pointerAddition = Prism to from . toPrism tuple3
  where
    to (p, e, e') = PointerAddition p e e'
    from (PointerAddition p e e') = Just (p, e, e')
    from _ = Nothing

continue = Prism to from
  where
    to (p, e) = Continue p e
    from (Continue p e) = Just (p, e)
    from _ = Nothing

break = Prism to from
  where
    to (p, e) = Break p e
    from (Break p e) = Just (p, e)
    from _ = Nothing

loop = Prism to from
  where
    to (p, ((pm, e), e')) = Loop p pm e e'
    from (Loop p pm e e') = Just (p, ((pm, e), e'))
    from _ = Nothing

isolate = Prism to from
  where
    to (p, e) = Isolate p e
    from (Isolate p e) = Just (p, e)
    from _ = Nothing

cast = Prism to from
  where
    to (p, e) = Cast p e
    from (Cast p e) = Just (p, e)
    from _ = Nothing

not = Prism to from
  where
    to (p, e) = Not p e
    from (Not p e) = Just (p, e)
    from _ = Nothing

and = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = And p e e'
    from (And p e e') = Just (e, p, e')
    from _ = Nothing

or = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Or p e e'
    from (Or p e e') = Just (e, p, e')
    from _ = Nothing

dox = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Do p e e'
    from (Do p e e') = Just (e, p, e')
    from _ = Nothing

ifx = Prism to from . toPrism (secondI tuple3)
  where
    to (p, (e1, e2, e3)) = If p e1 e2 e3
    from (If p e1 e2 e3) = Just (p, (e1, e2, e3))
    from _ = Nothing

typeAnnotation = Prism to from . toPrism tuple3'
  where
    to (e, p, σ) = TypeAnnotation p e σ
    from (TypeAnnotation p e σ) = Just (e, p, σ)
    from _ = Nothing

typeAnnotation' = Prism to from . toPrism tuple3
  where
    to (p, σ, e) = TypeAnnotation p e σ
    from (TypeAnnotation p e σ) = Just (p, σ, e)
    from _ = Nothing

pretypeAnnotation = Prism to from . toPrism tuple3'
  where
    to (e, p, σ) = PretypeAnnotation p e σ
    from (PretypeAnnotation p e σ) = Just (e, p, σ)
    from _ = Nothing

functionLiteral = Prism to from
  where
    to (p, (pm, ((τ, π), e))) = FunctionLiteral p pm τ π e
    from (FunctionLiteral p pm τ π e) = Just (p, (pm, ((τ, π), e)))
    from _ = Nothing

inlineAbstraction = Prism to from . toPrism tuple3'
  where
    to (p, pm, e) = InlineAbstraction p pm e
    from (InlineAbstraction p pm e) = Just (p, pm, e)
    from _ = Nothing

inlineApplication = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = InlineApplication p e e'
    from (InlineApplication p e e') = Just (e, p, e')
    from _ = Nothing

inlineLet = Prism to from . toPrism tuple4'
  where
    to (p, pm, e, e') = InlineLet p pm e e'
    from (InlineLet p pm e e') = Just (p, pm, e, e')
    from _ = Nothing

polyIntroduction = Prism to from
  where
    to (p, λ) = PolyIntroduction p λ
    from (PolyIntroduction p λ) = Just (p, λ)
    from _ = Nothing

polyElimination = Prism to from . toPrism tuple3'
  where
    to (e, p, θ) = PolyElimination p e θ
    from (PolyElimination p e θ) = Just (e, p, θ)
    from _ = Nothing

matchVariable = Prism to from . toPrism tuple3
  where
    to (p, x, σ) = MatchVariable p x σ
    from (MatchVariable p x σ) = Just (p, x, σ)
    from _ = Nothing

matchTuple = Prism to from
  where
    to (p, pms) = MatchTuple p pms
    from (MatchTuple p pms) = Just (p, pms)
    from _ = Nothing

matchBoolean b = Prism to from
  where
    to p = MatchBoolean p b
    from (MatchBoolean p b') | b == b' = Just p
    from _ = Nothing

matchTrue = matchBoolean True

matchFalse = matchBoolean False

inlineMatchVariable = Prism to from
  where
    to ((p, x), (π, σ)) = InlineMatchVariable p x π σ
    from (InlineMatchVariable p x π σ) = Just ((p, x), (π, σ))

monoTerm = Prism to from
  where
    to e = MonoTerm e
    from (MonoTerm e) = pure (e)
    from _ = Nothing

typeAbstraction = Prism to from
  where
    to (pm, e) = TypeAbstraction pm e
    from (TypeAbstraction pm e) = Just (pm, e)
    from _ = Nothing

termAuto = Prism TermAuto $ \case
  TermAuto e -> Just e
  _ -> Nothing

termManual = Prism TermManual $ \case
  TermManual e -> Just e
  _ -> Nothing

typeVariable = Prism to from
  where
    to (p, x) = TypeVariable p x
    from (TypeVariable p x) = Just (p, x)
    from _ = Nothing

typeGlobalVariable = Prism to from
  where
    to (p, x) = TypeGlobalVariable p x
    from (TypeGlobalVariable p x) = Just (p, x)
    from _ = Nothing

typeTrue = Prism to from
  where
    to p = TypeTrue p
    from (TypeTrue p) = Just p
    from _ = Nothing

typeFalse = Prism to from
  where
    to p = TypeFalse p
    from (TypeFalse p) = Just p
    from _ = Nothing

typeNot = Prism to from
  where
    to (p, σ) = TypeNot p σ
    from (TypeNot p σ) = Just (p, σ)
    from _ = Nothing

typeAnd = Prism to from . toPrism tuple3'
  where
    to (σ, p, τ) = TypeAnd p σ τ
    from (TypeAnd p σ τ) = Just (σ, p, τ)
    from _ = Nothing

typeOr = Prism to from . toPrism tuple3'
  where
    to (σ, p, τ) = TypeOr p σ τ
    from (TypeOr p σ τ) = Just (σ, p, τ)
    from _ = Nothing

typeXor = Prism to from . toPrism tuple3'
  where
    to (σ, p, τ) = TypeXor p σ τ
    from (TypeXor p σ τ) = Just (σ, p, τ)
    from _ = Nothing

world = Prism to from
  where
    to p = World p
    from (World p) = Just p
    from _ = Nothing

inline = Prism to from . toPrism tuple4'
  where
    to (σ, p, π, τ) = Inline p σ π τ
    from (Inline p σ π τ) = Just (σ, p, π, τ)
    from _ = Nothing

functionPointer = Prism to from
  where
    to (p, ((σ, π), τ)) = FunctionPointer p σ π τ
    from (FunctionPointer p σ π τ) = Just (p, ((σ, π), τ))
    from _ = Nothing

functionLiteralType = Prism to from
  where
    to (p, ((σ, π), τ)) = FunctionLiteralType p σ π τ
    from (FunctionLiteralType p σ π τ) = Just (p, ((σ, π), τ))
    from _ = Nothing

tuple = Prism to from
  where
    to (p, σ) = Tuple p σ
    from (Tuple p σ) = Just (p, σ)
    from _ = Nothing

effect = Prism to from . toPrism tuple3'
  where
    to (σ, p, π) = Effect p σ π
    from (Effect p σ π) = Just (σ, p, π)
    from _ = Nothing

unique = Prism to from
  where
    to (p, σ) = Unique p σ
    from (Unique p σ) = Just (p, σ)
    from _ = Nothing

shared = Prism to from . toPrism tuple3'
  where
    to (σ, p, τ) = Shared p σ τ
    from (Shared p σ τ) = Just (σ, p, τ)
    from _ = Nothing

pointer = Prism to from
  where
    to (σ, p) = Pointer p σ
    from (Pointer p σ) = Just (σ, p)
    from _ = Nothing

array = Prism to from
  where
    to (σ, p) = Array p σ
    from (Array p σ) = Just (σ, p)
    from _ = Nothing

number = Prism to from . toPrism tuple3'
  where
    to (σ, p, τ) = Number p σ τ
    from (Number p σ τ) = Just (σ, p, τ)
    from _ = Nothing

number' = Prism to from . toPrism tuple3
  where
    to (p, σ, τ) = Number p σ τ
    from (Number p σ τ) = Just (p, σ, τ)
    from _ = Nothing

boolean = Prism to from
  where
    to p = Boolean p
    from (Boolean p) = Just p
    from _ = Nothing

step = Prism to from . toPrism tuple3'
  where
    to (p, σ, τ) = Step p σ τ
    from (Step p σ τ) = Just (p, σ, τ)
    from _ = Nothing

typex = Prism to from
  where
    to p = Type p
    from (Type p) = Just p
    from _ = Nothing

region = Prism to from
  where
    to p = Region p
    from (Region p) = Just p
    from _ = Nothing

multiplicity = Prism to from
  where
    to p = Multiplicity p
    from (Multiplicity p) = Just p
    from _ = Nothing

pretype = Prism to from . toPrism tuple3'
  where
    to (p, κ, κ') = Pretype p κ κ'
    from (Pretype p κ κ') = Just (p, κ, κ')
    from _ = Nothing

boxed = Prism to from
  where
    to p = Boxed p
    from (Boxed p) = Just p
    from _ = Nothing

pointerRep = Prism to from
  where
    to p = PointerRepresentation p
    from (PointerRepresentation p) = Just p
    from _ = Nothing

structRep = Prism to from
  where
    to (p, ρs) = StructRepresentation p ρs
    from (StructRepresentation p ρs) = Just (p, ρs)
    from _ = Nothing

unionRep = Prism to from
  where
    to (p, ρs) = UnionRepresentation p ρs
    from (UnionRepresentation p ρs) = Just (p, ρs)
    from _ = Nothing

wordRep = Prism to from
  where
    to (σ, p) = WordRepresentation p σ
    from (WordRepresentation p σ) = Just (σ, p)
    from _ = Nothing

signed = Prism to from
  where
    to p = Signed p
    from (Signed p) = Just p
    from _ = Nothing

unsigned = Prism to from
  where
    to p = Unsigned p
    from (Unsigned p) = Just p
    from _ = Nothing

byte = Prism to from
  where
    to p = Byte p
    from (Byte p) = Just p
    from _ = Nothing

short = Prism to from
  where
    to p = Short p
    from (Short p) = Just p
    from _ = Nothing

int = Prism to from
  where
    to p = Int p
    from (Int p) = Just p
    from _ = Nothing

long = Prism to from
  where
    to p = Long p
    from (Long p) = Just p
    from _ = Nothing

native = Prism to from
  where
    to p = Native p
    from (Native p) = Just p
    from _ = Nothing

representation = Prism to from
  where
    to p = Representation p
    from (Representation p) = Just p
    from _ = Nothing

size = Prism to from
  where
    to p = Size p
    from (Size p) = Just p
    from _ = Nothing

signedness = Prism to from
  where
    to p = Signedness p
    from (Signedness p) = Just p
    from _ = Nothing

kind = Prism to from
  where
    to (p, κ) = Kind p κ
    from (Kind p κ) = Just (p, κ)
    from _ = Nothing

syntactic = Prism to from
  where
    to p = Syntactic p
    from (Syntactic p) = Just p
    from _ = Nothing

propositional = Prism to from
  where
    to p = Propositional p
    from (Propositional p) = Just p
    from _ = Nothing

unification = Prism to from
  where
    to p = Unification p
    from (Unification p) = Just p
    from _ = Nothing

ambiguousLabel = Prism to from
  where
    to p = AmbiguousLabel p
    from (AmbiguousLabel p) = Just p
    from _ = Nothing

label = Prism to from
  where
    to p = Label p
    from (Label p) = Just p
    from _ = Nothing

top = Prism to from
  where
    to p = Top p
    from (Top p) = Just p
    from _ = Nothing

typeScheme = Prism to from
  where
    to (p, λ) = TypeScheme p λ
    from (TypeScheme p λ) = Just (p, λ)
    from _ = Nothing

hole = Prism to from
  where
    to p = Hole p
    from (Hole p) = Just p
    from _ = Nothing

monoType = Prism to from
  where
    to σ = MonoType σ
    from (MonoType σ) = pure σ
    from _ = Nothing

typeForall = Prism to from
  where
    to (pm, σ) = TypeForall pm σ
    from (TypeForall pm σ) = Just (pm, σ)
    from _ = Nothing

transparent = Prism to from
  where
    to () = Transparent
    from Transparent = Just ()
    from _ = Nothing

concrete = Prism to from
  where
    to () = Concrete
    from Concrete = Just ()
    from _ = Nothing

typePattern = Isomorph to from
  where
    to (((p, x), π), κ) = TypePattern p x π κ
    from (TypePattern p x π κ) = (((p, x), π), κ)

instanciation = Prism to from
  where
    to = Instantiation
    from (Instantiation σ) = Just σ
    from _ = Nothing

instantiationInfer = Prism to from
  where
    to () = InstantiationInfer
    from InstantiationInfer = Just ()
    from _ = Nothing
