module Ast.Term.Surface where

import Ast.Common.Surface
import Ast.Common.Variable
import Ast.Term.Algebra
import Ast.Term.Runtime
import Ast.Type.Algebra hiding (Type)
import Ast.Type.Surface
import Control.Category ((.))
import Misc.Isomorph
import Misc.Prism
import Prelude hiding (id, (.))

data Term p
  = Term
      p
      ( TermF
          (Annotation p)
          (Instantiation p)
          (Type p)
          (NoType p)
          (TermScheme p)
          (TermMetaBound p)
          (TermBound p)
          (Term p)
      )
  deriving (Show)

data NoType p = NoType
  deriving (Show)

data TermMetaBound p = TermMetaBound (TermMetaPattern p) (Term p)
  deriving (Show)

data TermBound p = TermBound (TermPattern p) (Term p)
  deriving (Show)

data TermScheme p = TermScheme p (TermSchemeF p)
  deriving (Show)

data TermSchemeF p
  = MonoTerm (Term p)
  | TypeAbstraction (TypePattern p) (TermScheme p)
  deriving (Show)

data TermMetaPattern p = TermMetaPattern p (TermMetaPatternF (Type p) (TermMetaPattern p))
  deriving (Show)

data TermPattern p = TermPattern p (TermPatternF (Type p) (TermPattern p))
  deriving (Show)

data Annotation p
  = TypeAnnotation (Term p) (Type p)
  | PretypeAnnotation (Term p) (Type p)
  deriving (Show)

data TermControl p
  = TermAuto (Term p)
  | TermManual (TermScheme p)
  deriving (Show)

termMetaPattern = Isomorph (uncurry TermMetaPattern) $ \(TermMetaPattern p pm) -> (p, pm)

termPattern = Isomorph (uncurry TermPattern) $ \(TermPattern p pm) -> (p, pm)

patternVariable =
  Prism (uncurry $ uncurry PatternVariable) $ \case
    (PatternVariable x π σ) -> Just ((x, π), σ)

runtimePatternVariable =
  Prism (uncurry RuntimePatternVariable) $ \case
    (RuntimePatternVariable x σ) -> Just (x, σ)
    _ -> Nothing

runtimePatternTuple = Prism RuntimePatternTuple $ \case
  (RuntimePatternTuple pms) -> Just pms
  _ -> Nothing

runtimePatternTrue = Prism (const $ RuntimePatternBoolean True) $ \case
  (RuntimePatternBoolean True) -> Just ()
  _ -> Nothing

runtimePatternFalse = Prism (const $ RuntimePatternBoolean False) $ \case
  (RuntimePatternBoolean False) -> Just ()
  _ -> Nothing

term = Isomorph (uncurry Term) $ \(Term p e) -> (p, e)

termRuntime = Prism TermRuntime $ \case
  (TermRuntime e) -> Just e
  _ -> Nothing

termSugar = Prism TermSugar $ \case
  (TermSugar e) -> Just e
  _ -> Nothing

variable = (termRuntime .) $
  Prism (\(x, θ) -> Variable x θ) $ \case
    (Variable x θ) -> Just (x, θ)
    _ -> Nothing

globalVariable = Prism (\(x, θ) -> GlobalVariable x θ) $ \case
  (GlobalVariable x θ) -> Just (x, θ)
  _ -> Nothing

inlineAbstraction = Prism (InlineAbstraction) $ \case
  (InlineAbstraction λ) -> Just λ
  _ -> Nothing

inlineApplication = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Term p (InlineApplication e e')
    from (Term p (InlineApplication e e')) = Just (e, p, e')
    from _ = Nothing

bind = Prism (uncurry $ Bind) $ \case
  (Bind e λ) -> Just (e, λ)
  _ -> Nothing

alias = (termRuntime .) $
  Prism (uncurry $ Alias) $ \case
    (Alias e λ) -> Just (e, λ)
    _ -> Nothing

casex = (termRuntime .) $
  Prism (\(e, λ) -> Case e NoType λ NoType) $ \case
    (Case e NoType λ NoType) -> Just (e, λ)
    _ -> Nothing

extern = (termRuntime .) $
  Prism (\sym -> Extern sym NoType NoType NoType) $ \case
    (Extern sym NoType NoType NoType) -> Just sym
    _ -> Nothing

functionApplication = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Term p (TermRuntime (FunctionApplication e e' NoType))
    from (Term p (TermRuntime (FunctionApplication e e' NoType))) = Just (e, p, e')
    from _ = Nothing

functionLiteral =
  Prism (uncurry $ uncurry FunctionLiteral) $ \case
    FunctionLiteral λ τ π -> Just ((λ, τ), π)
    _ -> Nothing

tupleIntroduction = (termRuntime .) $
  Prism TupleIntroduction $ \case
    (TupleIntroduction es) -> Just es
    _ -> Nothing

readReference = (termRuntime .) $
  Prism (ReadReference) $ \case
    (ReadReference e) -> Just (e)
    _ -> Nothing

writeReference = (termRuntime .) $
  Prism (\(e, e') -> WriteReference e e' NoType) $ \case
    (WriteReference e e' NoType) -> Just (e, e')
    _ -> Nothing

numberLiteral = (termRuntime .) $
  Prism (\n -> NumberLiteral n NoType) $ \case
    (NumberLiteral n NoType) -> Just n
    _ -> Nothing

truex = (termRuntime .) $
  Prism (const $ BooleanLiteral True) $ \case
    BooleanLiteral True -> Just ()
    _ -> Nothing

falsex = (termRuntime .) $
  Prism (const $ BooleanLiteral False) $ \case
    BooleanLiteral False -> Just ()
    _ -> Nothing

ifx = (termSugar .) $
  Prism (\((e1, e2), e3) -> If e1 e2 e3 NoType) $ \case
    If eb et ef NoType -> Just ((eb, et), ef)
    _ -> Nothing

arithmatic o = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Term p (TermRuntime (Arithmatic o e e' NoType))
    from (Term p (TermRuntime (Arithmatic o' e e' NoType))) | o == o' = Just (e, p, e')
    from _ = Nothing

relational o = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Term p (TermRuntime (Relational o e e' NoType NoType))
    from (Term p (TermRuntime (Relational o' e e' NoType NoType))) | o == o' = Just (e, p, e')
    from _ = Nothing

pointerIncrement = (termRuntime .) $
  Prism (\(e, e') -> PointerIncrement e e' NoType) $ \case
    PointerIncrement e e' NoType -> Just (e, e')
    _ -> Nothing

continue = (termRuntime .) $
  Prism (\e -> Continue e NoType) $ \case
    Continue e NoType -> Just e
    _ -> Nothing

break = (termRuntime .) $
  Prism (\e -> Break e NoType) $ \case
    Break e NoType -> Just e
    _ -> Nothing

loop = (termRuntime .) $
  Prism (uncurry Loop) $ \case
    Loop e λ -> Just (e, λ)
    _ -> Nothing

not = (termSugar .) $
  Prism Not $ \case
    Not e -> Just e
    _ -> Nothing

and = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Term p (TermSugar (And e e'))
    from (Term p (TermSugar (And e e'))) = Just (e, p, e')
    from _ = Nothing

or = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Term p (TermSugar (Or e e'))
    from (Term p (TermSugar (Or e e'))) = Just (e, p, e')
    from _ = Nothing

dox = Prism to from . toPrism tuple3'
  where
    to (e, p, e') = Term p (TermSugar (Do e e'))
    from (Term p (TermSugar (Do e e'))) = Just (e, p, e')
    from _ = Nothing

polyIntroduction = Prism PolyIntroduction $ \case
  PolyIntroduction λ -> Just λ
  _ -> Nothing

polyElimination = Prism to from . toPrism tuple3'
  where
    to (e, p, θ) = Term p (PolyElimination e θ)
    from (Term p (PolyElimination e θ)) = Just (e, p, θ)
    from _ = Nothing

termScheme = Isomorph (uncurry TermScheme) $ \(TermScheme p e) -> (p, e)

monoTerm = Prism to from
  where
    to (p, e) = TermScheme p (MonoTerm e)
    from (TermScheme p (MonoTerm e)) = pure (p, e)
    from _ = Nothing

typeAbstraction = Prism to from
  where
    to ((p, pm), e) = TermScheme p (TypeAbstraction pm e)
    from (TermScheme p (TypeAbstraction pm e)) = Just ((p, pm), e)
    from _ = Nothing

annotation = Prism Annotation $ \case
  Annotation e -> Just e
  _ -> Nothing

typeAnnotation = Prism to from . toPrism tuple3'
  where
    to (e, p, σ) = Term p (Annotation (TypeAnnotation e σ))
    from (Term p (Annotation (TypeAnnotation e σ))) = Just (e, p, σ)
    from _ = Nothing

typeAnnotation' = Prism to from . toPrism tuple3
  where
    to (p, σ, e) = Term p (Annotation (TypeAnnotation e σ))
    from (Term p (Annotation (TypeAnnotation e σ))) = Just (p, σ, e)
    from _ = Nothing

pretypeAnnotation = Prism to from . toPrism tuple3'
  where
    to (e, p, σ) = Term p (Annotation (PretypeAnnotation e σ))
    from (Term p (Annotation (PretypeAnnotation e σ))) = Just (e, p, σ)
    from _ = Nothing

termErasure = Prism TermErasure $ \case
  TermErasure e -> Just e
  _ -> Nothing

isolatePointer = (termErasure .) $
  Prism IsolatePointer $ \case
    IsolatePointer e -> Just e
    _ -> Nothing

cast = (termErasure .) $
  Prism (\e -> Cast e NoType) $ \case
    Cast e NoType -> Just e
    _ -> Nothing

termAuto = Prism TermAuto $ \case
  TermAuto e -> Just e
  _ -> Nothing

termManual = Prism TermManual $ \case
  TermManual e -> Just e
  _ -> Nothing

termIdentifier = Isomorph TermIdentifier runTermIdentifier

termGlobalIdentifier = Isomorph TermGlobalIdentifier runTermGlobalIdentifier

termMetaBound = Isomorph (uncurry TermMetaBound) (\(TermMetaBound pm e) -> (pm, e))

termBound = Isomorph (uncurry TermBound) (\(TermBound pm e) -> (pm, e))

annotated :: TermControl p -> Maybe (TypeScheme p)
annotated (TermManual e) = annotatedScheme e
  where
    annotatedScheme (TermScheme p (MonoTerm e)) = TypeScheme p <$> (MonoType <$> annotatedTerm e)
    annotatedScheme (TermScheme p (TypeAbstraction pm e)) = TypeScheme p <$> (TypeForall pm <$> annotatedScheme e)
    annotatedTerm (Term p (FunctionLiteral (TermBound pm _) τ π))
      | Type _ (Hole _) <- τ = Nothing
      | Type _ (Hole _) <- π = Nothing
      | otherwise = Type p <$> (FunctionLiteralType <$> (annotatedPattern pm) <*> Just π <*> Just τ)
    annotatedTerm _ = Nothing
    annotatedPattern (TermPattern _ (RuntimePatternVariable _ (Type _ (Hole ())))) = Nothing
    annotatedPattern (TermPattern _ (RuntimePatternVariable _ σ)) = Just σ
    annotatedPattern (TermPattern p (RuntimePatternTuple pms)) = Type p <$> (Tuple <$> traverse annotatedPattern pms)
    annotatedPattern (TermPattern p (RuntimePatternBoolean _)) = Just $ Type p Boolean
annotated (TermAuto _) = Nothing

class Bindings pm where
  bindings :: pm p -> [TermIdentifier]

instance Bindings TermMetaPattern where
  bindings (TermMetaPattern _ (PatternVariable x _ _)) = [x]

instance Bindings TermPattern where
  bindings (TermPattern _ (RuntimePatternVariable x _)) = [x]
  bindings (TermPattern _ pm) = foldTermPatternF mempty go pm
    where
      go = bindings

instance Alpha Term where
  freeVariables (Term p (TermRuntime (Variable x θ))) = termLocal x p <> freeVariables θ
  freeVariables (Term p (GlobalVariable x θ)) = termGlobal x p <> freeVariables θ
  freeVariables (Term _ e) = foldTermF go go go go go go go go e
    where
      go = freeVariables

instance Alpha TermScheme where
  freeVariables (TermScheme _ (MonoTerm e)) = freeVariables e
  freeVariables (TermScheme _ (TypeAbstraction (TypePattern _ x _ κ) e)) =
    freeVariables κ <> deleteTypeLocal x (freeVariables e)

instance Alpha Annotation where
  freeVariables (TypeAnnotation e σ) = freeVariables e <> freeVariables σ
  freeVariables (PretypeAnnotation e σ) = freeVariables e <> freeVariables σ

instance Alpha NoType where
  freeVariables = mempty

instance Alpha TermMetaBound where
  freeVariables (TermMetaBound pm e) = freeVariables pm <> foldr deleteTermLocal (freeVariables e) (bindings pm)

instance Alpha TermBound where
  freeVariables (TermBound pm e) = freeVariables pm <> foldr deleteTermLocal (freeVariables e) (bindings pm)

instance Alpha TermMetaPattern where
  freeVariables (TermMetaPattern _ pm) = foldTermMetaPatternF go go pm
    where
      go = freeVariables

instance Alpha TermPattern where
  freeVariables (TermPattern _ pm) = foldTermPatternF go go pm
    where
      go = freeVariables

instance Alpha TermControl where
  freeVariables (TermAuto e) = freeVariables e
  freeVariables (TermManual e) = freeVariables e

instance Functor Term where
  fmap f (Term p e) = Term (f p) (mapTermF go go go go go go go go e)
    where
      go = fmap f

instance Functor TermScheme where
  fmap f (TermScheme p (MonoTerm e)) = TermScheme (f p) (MonoTerm (fmap f e))
  fmap f (TermScheme p (TypeAbstraction pm e)) = TermScheme (f p) (TypeAbstraction (go pm) (go e))
    where
      go = fmap f

instance Functor Annotation where
  fmap f (TypeAnnotation e σ) = TypeAnnotation (go e) (go σ)
    where
      go = fmap f
  fmap f (PretypeAnnotation e σ) = PretypeAnnotation (go e) (go σ)
    where
      go = fmap f

instance Functor NoType where
  fmap _ NoType = NoType

instance Functor TermMetaBound where
  fmap f (TermMetaBound pm e) = TermMetaBound (go pm) (go e)
    where
      go = fmap f

instance Functor TermBound where
  fmap f (TermBound pm e) = TermBound (go pm) (go e)
    where
      go = fmap f

instance Functor TermMetaPattern where
  fmap f (TermMetaPattern p pm) = TermMetaPattern (f p) (mapTermMetaPatternF go go pm)
    where
      go = fmap f

instance Functor TermPattern where
  fmap f (TermPattern p pm) = TermPattern (f p) (mapTermPatternF go go pm)
    where
      go = fmap f

instance Functor TermControl where
  fmap f (TermAuto e) = TermAuto (fmap f e)
  fmap f (TermManual e) = TermManual (fmap f e)
