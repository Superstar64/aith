module Simple
  ( Bound (..),
    Function (..),
    FunctionType (..),
    Term (..),
    Type (..),
    Size (..),
    Signedness (..),
    Pattern (..),
    Arithmatic (..),
    Relational (..),
    Context (..),
    TermIdentifier,
    TypeIdentifier,
    Symbol (..),
    patternType,
    mangleType,
    convertFunction,
    convertFunctionType,
  )
where

import Ast.Core (Arithmatic (..), Relational (..))
import qualified Ast.Core as Core
import Ast.Symbol
import Data.Functor.Identity (runIdentity)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Void (absurd)

data Context = Context
  { localKinds :: Map TypeIdentifier Core.TypeInfer,
    globalKinds :: Map TypeGlobalIdentifier Core.TypeInfer
  }

data Size
  = Byte
  | Short
  | Int
  | Long
  | Native
  deriving (Show, Eq, Ord)

data Signedness
  = Signed
  | Unsigned
  deriving (Show, Eq, Ord)

data Type
  = Pointer
  | Struct [Type]
  | Union [Type]
  | Word Size
  deriving (Eq, Ord)

data Pattern p
  = MatchVariable p TermIdentifier Type
  | MatchTuple p [Pattern p]
  | MatchBoolean p Bool

data Term p
  = Variable p TermIdentifier
  | Let p (Term p) (Bound p)
  | Case p (Term p) Type [Bound p]
  | Extern p Symbol [Type] Type
  | Application p (Term p) [(Term p, Type)]
  | TupleLiteral p [Term p]
  | Read p (Term p)
  | Write p (Term p) (Term p) Type
  | NumberLiteral p Integer
  | Arithmatic p Arithmatic (Term p) (Term p) Signedness
  | Relational p Relational (Term p) (Term p) Type Signedness
  | Resize p (Term p) Type
  | BooleanLiteral p Bool
  | PointerAddition p (Term p) (Term p) Type
  | Continue p (Term p)
  | Break p (Term p)
  | Loop p (Term p) (Bound p)

data Bound p = Bound (Pattern p) (Term p)

data Function p = Function p [Pattern p] (Term p)

data FunctionType = FunctionType [Type] Type

mangleType :: Type -> String
mangleType σ = case σ of
  Pointer -> "p"
  Struct σs -> "s" ++ (σs >>= mangleType) ++ "e"
  Union σs -> "u" ++ (σs >>= mangleType) ++ "e"
  Word Byte -> "b"
  Word Short -> "s"
  Word Int -> "i"
  Word Long -> "l"
  Word Native -> "n"

convertSize :: Core.TypeInfer -> Size
convertSize σ = case σ of
  Core.Byte -> Byte
  Core.Short -> Short
  Core.Int -> Int
  Core.Long -> Long
  Core.Native -> Native
  _ -> simpleFailType

convertRepresentation :: Core.TypeInfer -> Type
convertRepresentation σ = case σ of
  Core.PointerRepresentation -> Pointer
  Core.StructRepresentation ρs -> Struct (map convertRepresentation ρs)
  Core.UnionRepresentation ρs -> Union (map convertRepresentation ρs)
  Core.WordRepresentation ρ -> Word (convertSize ρ)
  _ -> simpleFailType

simpleFailType = error "illegal simple type"

convertKind :: Core.TypeInfer -> Type
convertKind (Core.Pretype κ _) = convertRepresentation κ
convertKind _ = simpleFailType

reconstruct Context {localKinds, globalKinds} = runIdentity . reconstruct
  where
    reconstruct = Core.reconstruct index indexGlobal absurd poly representation multiplicities propositional
    poly = error "poly type in runtime types"
    index x = pure (localKinds ! x)
    indexGlobal x = pure (globalKinds ! x)
    representation σ = checkRepresentation <$> reconstruct σ
    multiplicities _ = error "multiplicity not needed during simple reconstruction"
    propositional _ = error "propostional not needed during simple reconstruction"

    checkRepresentation (Core.Pretype κ _) = κ
    checkRepresentation _ = error "reconstruction of pair didn't return pretype"

convertType context σ = convertKind (reconstruct context σ)

convertSigned Core.Signed = Signed
convertSigned Core.Unsigned = Unsigned
convertSigned _ = error "bad sign"

convertPattern :: Context -> Core.TermPatternInfer p -> Pattern p
convertPattern context pm = case pm of
  Core.MatchVariable p x σ -> MatchVariable p x (convertType context σ)
  Core.MatchTuple p pms -> MatchTuple p (map (convertPattern context) pms)
  Core.MatchBoolean p b -> MatchBoolean p b

convertTerm :: Context -> Core.TermInfer p -> Term p
convertTerm context e = case e of
  Core.Variable p x _ -> Variable p x
  Core.Let p pm e1 e2 -> Let p (go e1) (Bound (go' pm) (go e2))
  Core.Case p e σ λ _ -> Case p (go e) (go'' σ) [Bound (go' pm) (go e) | (pm, e) <- λ]
  Core.Extern p sym σ _ τ -> Extern p sym (map go'' σ) (go'' τ)
  Core.Application p e1 e2s -> Application p (go e1) [(go e, go'' σ) | (e, σ) <- e2s]
  Core.TupleLiteral p es -> TupleLiteral p (map go es)
  Core.Read p e -> Read p (go e)
  Core.Write p e1 e2 σ -> Write p (go e1) (go e2) (go'' σ)
  Core.NumberLiteral p i _ -> NumberLiteral p i
  Core.Arithmatic p o e1 e2 s -> Arithmatic p o (go e1) (go e2) (convertSigned s)
  Core.Relational p o e1 e2 σ s -> Relational p o (go e1) (go e2) (go'' σ) (convertSigned s)
  Core.Resize p e σ _ -> Resize p (go e) (go'' σ)
  Core.BooleanLiteral p b -> BooleanLiteral p b
  Core.PointerAddition p e1 e2 σ -> PointerAddition p (go e1) (go e2) (go'' σ)
  Core.Continue p e _ -> Continue p (go e)
  Core.Break p e _ -> Break p (go e)
  Core.Loop p pm e1 e2 -> Loop p (go e1) (Bound (go' pm) (go e2))
  -- desugaring
  Core.Not p e -> go (Core.If p e (Core.BooleanLiteral p False) (Core.BooleanLiteral p True))
  Core.And p e1 e2 -> go (Core.If p e1 e2 (Core.BooleanLiteral p False))
  Core.Or p e1 e2 -> go (Core.If p e1 (Core.BooleanLiteral p True) e2)
  Core.Do p e1 e2 -> go (Core.Let p (Core.MatchTuple p []) e1 e2)
  Core.If p eb et ef -> go (Core.Case p eb Core.Boolean [(Core.MatchBoolean p True, et), (Core.MatchBoolean p False, ef)] undefined)
  Core.Isolate _ e -> go e
  Core.Cast _ e _ -> go e
  _ -> error "illegal simple term"
  where
    go = convertTerm context
    go' = convertPattern context
    go'' = convertType context

convertFunctionType context@Context {localKinds} (Core.TypeForall x _ κ σ) =
  convertFunctionType context {localKinds = Map.insert x κ localKinds} σ
convertFunctionType context (Core.MonoType (Core.FunctionLiteralType σ _ τ)) = do
  FunctionType (map (convertType context) σ) (convertType context τ)
convertFunctionType _ _ = error "failed to convert function type"

convertFunction context@Context {localKinds} (Core.TypeAbstraction x _ κ e) =
  convertFunction context {localKinds = Map.insert x κ localKinds} e
convertFunction context (Core.MonoTerm (Core.FunctionLiteral p pm _ _ e)) =
  Function p (map (convertPattern context) pm) (convertTerm context e)
convertFunction _ _ = error "failed to convert function"

patternType :: Pattern p -> Type
patternType (MatchVariable _ _ σ) = σ
patternType (MatchTuple _ pms) = Struct $ map patternType pms
patternType (MatchBoolean _ _) = Word Byte
