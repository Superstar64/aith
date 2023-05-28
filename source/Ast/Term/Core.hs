module Ast.Term.Core where

import Ast.Common.Variable
import Ast.Term.Algebra
import Ast.Term.Runtime
import Ast.Type.Algebra hiding (Type)
import Ast.Type.Core
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void (Void)
import Misc.Path (Path (..))
import qualified Misc.Path as Path

data Term p v
  = Term
      p
      ( TermF
          Void
          (Instantiation v)
          (Type v)
          (Type v)
          (TermScheme p v)
          (TermMetaBound p v)
          (TermBound p v)
          (Term p v)
      )

type TermUnify p = Term p TypeLogical

type TermInfer p = Term p Void

data TermMetaBound p v = TermMetaBound (TermMetaPattern p v) (Term p v)

data TermBound p v = TermBound (TermPattern p v) (Term p v)

data TermScheme p v = TermScheme p (TermSchemeF p v)

type TermSchemeUnify p = TermScheme p TypeLogical

type TermSchemeInfer p = TermScheme p Void

data TermSchemeF p v
  = MonoTerm (Term p v)
  | TypeAbstraction (TypePattern v) (TermScheme p v)

data TermMetaPattern p v = TermMetaPattern p (TermMetaPatternF (Type v) (TermMetaPattern p v))

type TermMetaPatternUnify p = TermMetaPattern p TypeLogical

type TermMetaPatternInfer p = TermMetaPattern p Void

data TermPattern p v = TermPattern p (TermPatternF (Type v) (TermPattern p v))

type TermPatternUnify p = TermPattern p TypeLogical

type TermPatternInfer p = TermPattern p Void

textType :: TermSchemeInfer p -> TypeSchemeInfer
textType (TermScheme _ (MonoTerm (Term _ (FunctionLiteral (TermBound pm _) τ π)))) =
  MonoType $ Type $ FunctionLiteralType σ π τ
  where
    σ = textPattern pm
    textPattern (TermPattern _ (RuntimePatternVariable _ σ)) = σ
    textPattern (TermPattern _ (RuntimePatternTuple pms)) = Type $ Tuple $ map textPattern pms
    textPattern (TermPattern _ (RuntimePatternBoolean _)) = Type $ Boolean
textType (TermScheme _ (TypeAbstraction pm e)) = TypeForall pm $ textType e
textType _ = error "expected function literal"

makeExtern ::
  Path ->
  p ->
  TypeSchemeInfer ->
  TermSchemeInfer p
makeExtern path p ς = case ς of
  MonoType (Type (FunctionLiteralType σ π τ)) ->
    ( TermScheme p $
        MonoTerm
          (Term p (TermRuntime $ Extern (Path.mangle path) σ π τ))
    )
  TypeForall (TypePattern x κ) e ->
    TermScheme p (TypeAbstraction (TypePattern x κ) $ makeExtern path p e)
  _ -> error "not function literal"

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

freeVariablesGlobalTerm :: TermAlgebra u => u p v -> Set TermGlobalIdentifier
freeVariablesGlobalTerm e = case freeVariablesTerm e of
  TermVariables _ variables -> variables

convertTerm ux x = substituteTerms (TermSubstitution Map.empty Map.empty (Map.singleton x ux))

substituteLocalTerm ux x = substituteTerms (TermSubstitution (Map.singleton x ux) Map.empty Map.empty)

substituteGlobalTerm :: TermAlgebra u => TermSchemeInfer p -> TermGlobalIdentifier -> u p Void -> u p Void
substituteGlobalTerm ux x = substituteTerms (TermSubstitution Map.empty (Map.singleton x ux) Map.empty)

applyScheme :: TermSchemeInfer p -> InstantiationInfer -> TermInfer p
applyScheme (TermScheme _ (MonoTerm e)) InstantiateEmpty = e
applyScheme (TermScheme _ (TypeAbstraction (TypePattern x _) e)) (InstantiateType σ θ) =
  applyScheme (substituteType σ x e) θ
applyScheme _ _ = error "bad scheme pair"

applyTerm e (TermMetaBound (TermMetaPattern _ (PatternVariable x _ _)) ex@(Term p _)) =
  reduce $ substituteLocalTerm (TermScheme p (MonoTerm e)) x ex

desugar p (Not e) =
  Term
    p
    ( TermSugar $
        If
          e
          (Term p $ TermRuntime $ BooleanLiteral False)
          (Term p $ TermRuntime $ BooleanLiteral True)
          (Type Boolean)
    )
desugar p (And e e') =
  Term
    p
    ( TermSugar $
        If
          e
          e'
          (Term p $ TermRuntime $ BooleanLiteral False)
          (Type Boolean)
    )
desugar p (Or e e') =
  Term
    p
    ( TermSugar $
        If
          e
          (Term p $ TermRuntime $ BooleanLiteral True)
          e'
          (Type Boolean)
    )
desugar p (Do e e') =
  Term
    p
    ( TermRuntime $
        Alias e (TermBound (TermPattern p $ RuntimePatternTuple []) e')
    )
desugar p (If eb et ef σ) =
  Term
    p
    ( TermRuntime $
        Case
          eb
          (Type $ Boolean)
          [TermBound (TermPattern p $ RuntimePatternBoolean True) et, TermBound (TermPattern p $ RuntimePatternBoolean False) ef]
          σ
    )

instance TermAlgebra Term where
  freeVariablesTerm (Term _ (TermRuntime (Variable x _))) = TermVariables (Set.singleton x) Set.empty
  freeVariablesTerm (Term _ (GlobalVariable x _)) = TermVariables Set.empty (Set.singleton x)
  freeVariablesTerm (Term _ e) = foldTermF mempty mempty mempty mempty go go go go e
    where
      go = freeVariablesTerm
  substituteTerms (TermSubstitution locals _ _) (Term _ (TermRuntime (Variable x θ)))
    | Just e <- Map.lookup x locals = applyScheme e θ
  substituteTerms (TermSubstitution _ globals _) (Term _ (GlobalVariable x θ))
    | Just e <- Map.lookup x globals = applyScheme e θ
  substituteTerms (TermSubstitution _ _ alpha) (Term p (TermRuntime (Variable x θ)))
    | Just x' <- Map.lookup x alpha = Term p (TermRuntime (Variable x' θ))
  substituteTerms θ (Term p e) = Term p $ mapTermF id id id id go go go go e
    where
      go = substituteTerms θ

  reduce (Term _ (Bind e (TermMetaBound pm ex))) =
    let λ = TermMetaBound pm (reduce ex) in applyTerm e λ
  reduce (Term _ (InlineApplication e1 e)) | (Term _ (InlineAbstraction λ)) <- reduce e1 = applyTerm e λ
  reduce (Term _ (PolyElimination e θ)) | Term _ (PolyIntroduction e) <- reduce e = reduce $ applyScheme e θ
  reduce (Term p (TermSugar e)) = reduce (desugar p e)
  reduce (Term p e) = Term p (mapTermF id id id id go go go go e)
    where
      go = reduce

instance TermAlgebra TermScheme where
  freeVariablesTerm (TermScheme _ (MonoTerm e)) = freeVariablesTerm e
  freeVariablesTerm (TermScheme _ (TypeAbstraction _ e)) = freeVariablesTerm e
  substituteTerms θ (TermScheme p (MonoTerm e)) = TermScheme p (MonoTerm $ substituteTerms θ e)
  substituteTerms θ (TermScheme p (TypeAbstraction (TypePattern x κ) e)) =
    TermScheme p (TypeAbstraction (TypePattern x' κ) (go e'))
    where
      variables = termSubstitutionLocalTypeVariables θ
      x' = fresh variables x
      e' = convertType x' x e
      go = substituteTerms θ
  reduce (TermScheme p (MonoTerm e)) = TermScheme p (MonoTerm (reduce e))
  reduce (TermScheme p (TypeAbstraction pm e)) = TermScheme p $ TypeAbstraction pm (reduce e)

substituteBound θ (pm, e) =
  let binders = Set.toList $ bindings pm
      θ' = foldr termSubstitutionMask θ binders
      illegal = termSubstitutionLocalVariables θ'
      target = filter (flip Set.member illegal) binders
      alphaPattern x pm = let x' = fresh illegal x in rename x' x pm
      alphaTerm x e = let x' = fresh illegal x in convertTerm x' x e
      pm' = foldr alphaPattern pm target
      e' = foldr alphaTerm e target
      go = substituteTerms θ
   in (pm', go e')

instance TermAlgebra TermMetaBound where
  freeVariablesTerm (TermMetaBound pm e) = foldr variablesRemoveLocal (freeVariablesTerm e) (bindings pm)
  substituteTerms θ (TermMetaBound pm e) =
    let (pm', e') = substituteBound θ (pm, e)
     in TermMetaBound pm' e'
  reduce (TermMetaBound pm e) = TermMetaBound pm (reduce e)

instance TermAlgebra TermBound where
  freeVariablesTerm (TermBound pm e) = foldr variablesRemoveLocal (freeVariablesTerm e) (bindings pm)
  substituteTerms θ (TermBound pm e) =
    let (pm', e') = substituteBound θ (pm, e)
     in TermBound pm' e'
  reduce (TermBound pm e) = TermBound pm (reduce e)

instance TypeAlgebra (Term p) where
  freeLocalVariablesType (Term _ e) = foldTermF mempty go go go go go go go e
    where
      go = freeLocalVariablesType
  substituteTypes θ (Term p e) = Term p (mapTermF id go go go go go go go e)
    where
      go = substituteTypes θ
  zonkType f (Term p e) = Term p <$> traverseTermF pure go go go go go go go e
    where
      go = zonkType f
  simplify (Term p e) = Term p (mapTermF id go go go go go go go e)
    where
      go = simplify

instance TypeAlgebra (TermScheme p) where
  freeLocalVariablesType (TermScheme _ (MonoTerm e)) = freeLocalVariablesType e
  freeLocalVariablesType (TermScheme _ (TypeAbstraction (TypePattern x κ) e)) =
    go κ <> Set.delete x (go e)
    where
      go = freeLocalVariablesType
  substituteTypes θ (TermScheme p (MonoTerm e)) = TermScheme p (MonoTerm (substituteTypes θ e))
  substituteTypes θ (TermScheme p (TypeAbstraction (TypePattern x κ) e))
    | Set.member x (typeSubstitutionShadow θ) = TermScheme p (TypeAbstraction (TypePattern x κ) e)
    | otherwise = TermScheme p (TypeAbstraction (TypePattern x' (go κ)) (go e'))
    where
      variables = typeSubstitutionLocalVariables θ
      x' = fresh variables x
      e' = convertType x' x e
      go = substituteTypes θ
  zonkType f (TermScheme p (MonoTerm e)) = TermScheme p <$> (MonoTerm <$> zonkType f e)
  zonkType f (TermScheme p (TypeAbstraction (TypePattern x κ) e)) =
    TermScheme p <$> (TypeAbstraction <$> (TypePattern x <$> go κ) <*> go e)
    where
      go = zonkType f
  simplify (TermScheme p (MonoTerm e)) = TermScheme p (MonoTerm (simplify e))
  simplify (TermScheme p (TypeAbstraction (TypePattern x κ) e)) = TermScheme p (TypeAbstraction (TypePattern x (simplify κ)) (simplify e))

instance TypeAlgebra (TermMetaBound p) where
  freeLocalVariablesType (TermMetaBound pm e) = go pm <> go e
    where
      go = freeLocalVariablesType
  substituteTypes θ (TermMetaBound pm e) = TermMetaBound (go pm) (go e)
    where
      go = substituteTypes θ
  zonkType f (TermMetaBound pm e) = TermMetaBound <$> go pm <*> go e
    where
      go = zonkType f
  simplify (TermMetaBound pm e) = TermMetaBound (go pm) (go e)
    where
      go = simplify

instance TypeAlgebra (TermBound p) where
  freeLocalVariablesType (TermBound pm e) = go pm <> go e
    where
      go = freeLocalVariablesType
  substituteTypes θ (TermBound pm e) = TermBound (go pm) (go e)
    where
      go = substituteTypes θ
  zonkType f (TermBound pm e) = TermBound <$> go pm <*> go e
    where
      go = zonkType f
  simplify (TermBound pm e) = TermBound (go pm) (go e)
    where
      go = simplify

instance TypeAlgebra (TermMetaPattern p) where
  freeLocalVariablesType (TermMetaPattern _ pm) = foldTermMetaPatternF go go pm
    where
      go = freeLocalVariablesType
  substituteTypes θ (TermMetaPattern p pm) = TermMetaPattern p (mapTermMetaPatternF go go pm)
    where
      go = substituteTypes θ
  zonkType f (TermMetaPattern p pm) = TermMetaPattern p <$> traverseTermMetaPatternF go go pm
    where
      go = zonkType f
  simplify (TermMetaPattern p pm) = TermMetaPattern p (mapTermMetaPatternF go go pm)
    where
      go = simplify

instance TypeAlgebra (TermPattern p) where
  freeLocalVariablesType (TermPattern _ pm) = foldTermPatternF go go pm
    where
      go = freeLocalVariablesType
  substituteTypes θ (TermPattern p pm) = TermPattern p (mapTermPatternF go go pm)
    where
      go = substituteTypes θ
  zonkType f (TermPattern p pm) = TermPattern p <$> traverseTermPatternF go go pm
    where
      go = zonkType f
  simplify (TermPattern p pm) = TermPattern p (mapTermPatternF go go pm)
    where
      go = simplify

instance Binder (TermMetaPattern p u) where
  bindings (TermMetaPattern _ (PatternVariable x _ _)) = Set.singleton x
  rename ux x (TermMetaPattern p (PatternVariable x' σ τ))
    | x == x' = TermMetaPattern p (PatternVariable ux σ τ)
    | otherwise = TermMetaPattern p (PatternVariable x' σ τ)

instance Binder (TermPattern p u) where
  bindings (TermPattern _ (RuntimePatternVariable x _)) = Set.singleton x
  bindings (TermPattern _ pm) = foldTermPatternF mempty go pm
    where
      go = bindings
  rename ux x (TermPattern p (RuntimePatternVariable x' σ))
    | x == x' = TermPattern p (RuntimePatternVariable ux σ)
    | otherwise = TermPattern p (RuntimePatternVariable x' σ)
  rename ux x (TermPattern p pm) = TermPattern p $ mapTermPatternF id go pm
    where
      go = rename ux x
