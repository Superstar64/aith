module Ast.Term.Convert where

import Ast.Term.Algebra
import qualified Ast.Term.Core as Core
import Ast.Term.Runtime
import qualified Ast.Term.Surface as Surface
import Ast.Type.Algebra
import Ast.Type.Convert
import qualified Ast.Type.Core as Core
import qualified Ast.Type.Surface as Surface
import Data.Void (absurd)

sourceTermScheme :: Core.TermSchemeInfer p -> Surface.TermScheme ()
sourceTermScheme (Core.TermScheme _ e) =
  Surface.TermScheme () $
    ( case e of
        Core.MonoTerm e -> Surface.MonoTerm (sourceTerm e)
        Core.TypeAbstraction pm e -> Surface.TypeAbstraction (sourceTypePattern pm) (sourceTermScheme e)
    )

sourceTermAnnotate annotate e σ =
  Surface.Term () $
    Annotation $ annotate (sourceTerm e) (sourceType σ)

sourceTerm :: Core.TermInfer p -> Surface.Term ()
sourceTerm (Core.Term _ (TermRuntime (NumberLiteral n σ))) =
  Surface.Term () $ Annotation $ Surface.PretypeAnnotation (Surface.Term () $ TermRuntime $ NumberLiteral n Surface.NoType) (sourceType σ)
sourceTerm (Core.Term _ (TermRuntime (Extern sym σ π τ))) =
  Surface.Term () $
    Annotation $ Surface.PretypeAnnotation (Surface.Term () $ TermRuntime $ Extern sym Surface.NoType Surface.NoType Surface.NoType) (Surface.Type () (FunctionPointer (sourceType σ) (sourceType π) (sourceType τ)))
sourceTerm (Core.Term _ (TermRuntime (Continue e σ))) =
  Surface.Term () $ Annotation $ Surface.PretypeAnnotation (Surface.Term () $ TermRuntime $ Continue (sourceTerm e) Surface.NoType) (sourceType σ)
sourceTerm (Core.Term _ (TermRuntime (Break e σ))) =
  Surface.Term () $ Annotation $ Surface.PretypeAnnotation (Surface.Term () $ TermRuntime $ Break (sourceTerm e) Surface.NoType) (sourceType σ)
sourceTerm (Core.Term _ (TermRuntime (Case e _ [] σ))) =
  Surface.Term () $ Annotation $ Surface.PretypeAnnotation (Surface.Term () $ TermRuntime $ Case (sourceTerm e) Surface.NoType [] Surface.NoType) (sourceType σ)
sourceTerm (Core.Term _ (TermErasure (Cast e σ))) =
  Surface.Term () $ Annotation $ Surface.TypeAnnotation (Surface.Term () $ TermErasure $ Cast (sourceTerm e) Surface.NoType) (sourceType σ)
sourceTerm (Core.Term _ e) =
  Surface.Term () $ case e of
    TermRuntime e -> TermRuntime $ case e of
      Variable x Core.InstantiateEmpty -> Variable x (Surface.InstantiationInfer)
      Variable x θ -> Variable x (sourceInstanciation θ)
      Alias e (Core.TermBound pm ex) -> Alias (sourceTerm e) (Surface.TermBound (sourceTermPattern False pm) (sourceTerm ex))
      Case e _ λs _ ->
        Case (sourceTerm e) Surface.NoType (map (\(Core.TermBound pm ex) -> Surface.TermBound (sourceTermPattern False pm) (sourceTerm ex)) λs) Surface.NoType
      FunctionApplication e e' _ -> FunctionApplication (sourceTerm e) (sourceTerm e') ann
      TupleIntroduction es -> TupleIntroduction (map sourceTerm es)
      ReadReference e -> ReadReference (sourceTerm e)
      WriteReference e e' _ -> WriteReference (sourceTerm e) (sourceTerm e') ann
      Arithmatic o e e' _ -> Arithmatic o (sourceTerm e) (sourceTerm e') ann
      Relational o e e' _ _ -> Relational o (sourceTerm e) (sourceTerm e') ann ann
      BooleanLiteral b -> BooleanLiteral b
      PointerIncrement e e' _ -> PointerIncrement (sourceTerm e) (sourceTerm e') ann
      Loop e (Core.TermBound pm ex) -> Loop (sourceTerm e) (Surface.TermBound (sourceTermPattern False pm) (sourceTerm ex))
    TermSugar e -> TermSugar (mapTermSugar (const $ Surface.NoType) sourceTerm e)
    GlobalVariable x Core.InstantiateEmpty -> GlobalVariable x (Surface.InstantiationInfer)
    GlobalVariable x θ -> GlobalVariable x (sourceInstanciation θ)
    FunctionLiteral (Core.TermBound pm ex) τ π -> FunctionLiteral (Surface.TermBound (sourceTermPattern True pm) (sourceTerm ex)) (sourceType τ) (sourceType π)
    TermErasure (IsolatePointer e) -> TermErasure $ IsolatePointer (sourceTerm e)
    InlineAbstraction (Core.TermMetaBound pm ex) -> InlineAbstraction (Surface.TermMetaBound (sourceTermMetaPattern True pm) (sourceTerm ex))
    InlineApplication e e' -> InlineApplication (sourceTerm e) (sourceTerm e')
    Bind e (Core.TermMetaBound pm ex) -> Bind (sourceTerm e) (Surface.TermMetaBound (sourceTermMetaPattern True pm) (sourceTerm ex))
    PolyIntroduction λ -> PolyIntroduction (sourceTermScheme λ)
    PolyElimination e θ -> PolyElimination (sourceTerm e) (sourceInstanciation θ)
    Annotation invalid -> absurd invalid
  where
    ann = Surface.NoType

sourceTermMetaPattern :: Bool -> Core.TermMetaPatternInfer p -> Surface.TermMetaPattern ()
sourceTermMetaPattern emitAnnotation (Core.TermMetaPattern _ pm) =
  Surface.TermMetaPattern () $
    mapTermMetaPatternF annotate (sourceTermMetaPattern emitAnnotation) pm
  where
    annotate =
      if emitAnnotation
        then sourceType
        else const $ Surface.Type () $ Hole $ ()

sourceTermPattern :: Bool -> Core.TermPatternInfer p -> Surface.TermPattern ()
sourceTermPattern emitAnnotation (Core.TermPattern _ pm) =
  Surface.TermPattern () $
    mapTermPatternF annotate (sourceTermPattern emitAnnotation) pm
  where
    annotate =
      if emitAnnotation
        then sourceType
        else const $ Surface.Type () $ Hole $ ()
