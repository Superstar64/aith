module Language.TypeCheck.Unify where

import Control.Monad.Trans (lift)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Data.Maybe (fromJust)
import Language.Ast.Common
import Language.Ast.Kind
import Language.Ast.Sort
import Language.Ast.Type
import Language.TypeCheck.Core
import Language.TypeCheck.Variable

matchType p σ σ' = insertTypeEquation (TypeEquation p σ σ')

matchKind p κ κ' = insertKindEquation (KindEquation p κ κ')

matchSort _ Kind Kind = pure ()
matchSort _ Stage Stage = pure ()
matchSort _ Impact Impact = pure ()
matchSort _ Existance Existance = pure ()
matchSort _ Representation Representation = pure ()
matchSort _ Size Size = pure ()
matchSort _ Signedness Signedness = pure ()
matchSort p μ μ' = quit $ SortMismatch p μ μ'

-- todo this is ugly, find a better way to do this

reconstructType indexVariable indexLogical augment = reconstruct
  where
    reconstruct (CoreType _ (TypeVariable x)) = do
      indexVariable x
    reconstruct (CoreType _ (TypeLogical v)) = do
      indexLogical v
    reconstruct (CoreType _ (Macro _ _)) = do
      pure $ CoreKind Internal $ Type $ CoreKind Internal Meta
    reconstruct (CoreType _ (ExplicitForall (Bound pm σ))) = do
      augment pm $ reconstruct σ
    reconstruct (CoreType _ (Implied _ σ)) = do
      reconstruct σ
    reconstruct (CoreType _ (OfCourse _)) = do
      pure $ CoreKind Internal $ Type $ CoreKind Internal Meta
    reconstruct (CoreType _ (FunctionPointer _ _)) = do
      pure $ CoreKind Internal $ Type $ CoreKind Internal $ Runtime (CoreKind Internal Data) (CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime PointerRep)
    reconstruct (CoreType _ (FunctionLiteralType _ _)) = do
      pure $ CoreKind Internal $ Type $ CoreKind Internal $ Text
    reconstruct (CoreType _ (Copy _)) = do
      pure $ CoreKind Internal $ Type $ CoreKind Internal $ Evidence
    reconstruct (CoreType _ (RuntimePair σ σ')) = do
      κ <- reconstruct σ
      κ' <- reconstruct σ'
      case (κ, κ') of
        ( CoreKind _ (Type (CoreKind _ (Runtime _ (CoreKind Internal (Real κ))))),
          CoreKind _ (Type (CoreKind _ (Runtime _ (CoreKind Internal (Real κ')))))
          ) -> do
            pure $
              CoreKind Internal $
                Type $ CoreKind Internal $ Runtime (CoreKind Internal Data) $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ StructRep [κ, κ']
        _ -> error "internal error: reconstruction of pair didn't return runtime kind"
    reconstruct (CoreType _ (RegionTransformer _ σ)) = do
      κ <- reconstruct σ
      case κ of
        (CoreKind _ (Type (CoreKind _ (Runtime _ κ)))) -> pure $ CoreKind Internal $ Type $ CoreKind Internal $ Runtime (CoreKind Internal Code) κ
        _ -> error "internal error: reconstruction of region transformer didn't return runtime kind"
    reconstruct (CoreType _ (Number _ ρ)) = do
      pure $ CoreKind Internal $ Type $ CoreKind Internal $ Runtime (CoreKind Internal Data) (CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ WordRep ρ)
    reconstruct (CoreType _ (RegionReference _ σ)) = reconstruct σ

reconstructKind indexVariable indexLogical = reconstruct
  where
    reconstruct (CoreKind _ (KindVariable x)) = do
      indexVariable x
    reconstruct (CoreKind _ (KindLogical v)) = do
      indexLogical v
    reconstruct (CoreKind _ (Type _)) = pure $ Kind
    reconstruct (CoreKind _ Evidence) = pure $ Stage
    reconstruct (CoreKind _ Region) = pure $ Kind
    reconstruct (CoreKind _ Meta) = pure $ Stage
    reconstruct (CoreKind _ Text) = pure $ Stage
    reconstruct (CoreKind _ (Runtime _ _)) = pure $ Stage
    reconstruct (CoreKind _ Code) = pure $ Impact
    reconstruct (CoreKind _ Data) = pure $ Impact
    reconstruct (CoreKind _ Imaginary) = pure $ Existance
    reconstruct (CoreKind _ (Real _)) = pure $ Existance
    reconstruct (CoreKind _ (KindRuntime _)) = pure $ Representation
    reconstruct (CoreKind _ (KindSize _)) = pure $ Size
    reconstruct (CoreKind _ (KindSignedness _)) = pure $ Signedness

effectless :: Core Internal e -> Core p e
effectless e = do
  env <- askEnvironment
  state <- getState
  case runCore e (Internal <$ env) (Internal <$ state) of
    Right (e, _) -> pure e
    Left _ -> error "error in effectless"

-- also changes logic type variable levels and check for escaping skolem variables
typeOccursCheck :: TypeUnify -> p -> TypeLogicalRaw -> TypeUnify -> Core p ()
typeOccursCheck σ' p x (CoreType _ σ) =
  let recurse = typeOccursCheck σ' p x
   in case σ of
        TypeVariable x' -> do
          (_, _, lev) <- indexTypeVariableMap x
          (_, _, lev') <- fromJust <$> lookupKindEnvironment x'
          if lev' > lev
            then quit $ EscapingSkolemType p x' σ'
            else pure ()
        TypeLogical x' | x == x' -> quit $ TypeOccursCheck p x σ'
        TypeLogical x' -> do
          (_, _, lev) <- indexTypeVariableMap x
          (_, _, lev') <- indexTypeVariableMap x'
          if lev' > lev
            then updateTypeLevel x' lev
            else pure ()
        Macro σ τ -> do
          recurse σ
          recurse τ
        ExplicitForall (Bound (Pattern _ α κ) σ) -> do
          augmentKindEnvironment α p κ minBound $ recurse σ
        OfCourse σ -> recurse σ
        Implied σ τ -> do
          recurse σ
          recurse τ
        FunctionPointer σ τ -> do
          recurse σ
          recurse τ
        FunctionLiteralType σ τ -> do
          recurse σ
          recurse τ
        Copy σ -> recurse σ
        RuntimePair σ τ -> do
          recurse σ
          recurse τ
        RegionTransformer σ τ -> do
          recurse σ
          recurse τ
        RegionReference σ τ -> do
          recurse σ
          recurse τ
        Number _ _ -> pure ()

kindOccursCheck :: KindUnify -> p -> KindLogicalRaw -> KindUnify -> Core p ()
kindOccursCheck κ' p x (CoreKind _ κ) =
  let recurse = kindOccursCheck κ' p x
   in case κ of
        KindVariable x' -> do
          (_, _, lev) <- indexKindVariableMap x
          (_, _, lev') <- fromJust <$> lookupSortEnvironment x'
          if lev' > lev
            then quit $ EscapingSkolemKind p x' κ'
            else pure ()
        KindLogical x' | x == x' -> quit $ KindOccursCheck p x κ'
        KindLogical x' -> do
          (_, _, lev) <- indexKindVariableMap x
          (_, _, lev') <- indexKindVariableMap x'
          if lev' > lev
            then updateKindLevel x' lev
            else pure ()
        Type κ -> recurse κ
        Evidence -> pure ()
        Region -> pure ()
        (Runtime κ κ') -> do
          recurse κ
          recurse κ'
        Code -> pure ()
        Data -> pure ()
        Imaginary -> pure ()
        (Real κ) -> recurse κ
        Meta -> pure ()
        Text -> pure ()
        (KindRuntime PointerRep) -> pure ()
        (KindRuntime (StructRep κs)) -> traverse recurse κs >> pure ()
        (KindRuntime (WordRep κ)) -> recurse κ
        (KindSize _) -> pure ()
        (KindSignedness _) -> pure ()

unifyTypeVariable ::
  p ->
  TypeLogicalRaw ->
  TypeUnify ->
  Core p (Substitution TypeLogicalRaw TypeUnify)
unifyTypeVariable p x σ = do
  typeOccursCheck σ p x σ
  κ <- effectless $ reconstructType indexKindEnvironment indexVariableMap augment σ
  (_, κ', _) <- indexTypeVariableMap x
  matchKind p κ κ'
  apply σ x
  pure $ singleSubstitution x σ
  where
    apply σ x = do
      modifyTypeEquations (substitute σ x)
    indexKindEnvironment x = mid <$> fromJust <$> lookupKindEnvironment x
      where
        mid (_, x, _) = x
    augment (Pattern p x κ) = augmentKindEnvironment x p κ (error "level usage during kind checking")
    mid (_, x, _) = x
    indexVariableMap x = mid <$> indexTypeVariableMap x

unifyKindVariable p x κ = do
  kindOccursCheck κ p x κ
  μ <- effectless $ reconstructKind indexSortEnvironment indexVariableMap κ
  (_, μ', _) <- indexKindVariableMap x
  matchSort p μ μ'
  apply κ x
  pure $ singleSubstitution x κ
  where
    apply κ x = do
      modifyKindEquations (substitute κ x)
      modifyTypeVariableMap (fmap $ middle $ substitute κ x)
      where
        middle f (a, b, c) = (a, f b, c)
    indexSortEnvironment x = mid <$> fromJust <$> lookupSortEnvironment x
    mid (_, x, _) = x
    indexVariableMap x = mid <$> indexKindVariableMap x

unifyType :: p -> TypeUnify -> TypeUnify -> WriterT (Substitution TypeLogicalRaw TypeUnify) (Core p) ()
unifyType = unify
  where
    match p σ σ' = lift $ matchType p σ σ'
    unify _ (CoreType _ (TypeLogical x)) (CoreType _ (TypeLogical x')) | x == x' = pure ()
    unify p (CoreType _ (TypeLogical x)) σ = do
      θ <- lift $ unifyTypeVariable p x σ
      tell θ
    unify p σ σ'@(CoreType _ (TypeLogical _)) = unify p σ' σ
    unify _ (CoreType _ (TypeVariable x)) (CoreType _ (TypeVariable x')) | x == x' = pure ()
    unify p (CoreType _ (Macro σ τ)) (CoreType _ (Macro σ' τ')) = do
      match p σ σ'
      match p τ τ'
    unify p (CoreType _ (ExplicitForall (Bound pm@(Pattern _ α κ) σ))) (CoreType _ (ExplicitForall (Bound (Pattern _ α' κ') σ'))) = do
      lift $ matchKind p κ κ'
      let σ'' = substitute @TypeUnify (CoreType Internal $ TypeVariable α) α' σ'
      lift $ insertTypeEquation (TypeSkolemBound p (Bound pm [TypeEquation p σ σ'']))
    unify p (CoreType _ (Implied σ τ)) (CoreType _ (Implied σ' τ')) = do
      match p σ σ'
      match p τ τ'
    unify p (CoreType _ (OfCourse σ)) (CoreType _ (OfCourse σ')) = do
      match p σ σ'
    unify p (CoreType _ (FunctionPointer σ τ)) (CoreType _ (FunctionPointer σ' τ')) = do
      match p σ σ'
      match p τ τ'
    unify p (CoreType _ (FunctionLiteralType σ τ)) (CoreType _ (FunctionLiteralType σ' τ')) = do
      match p σ σ'
      match p τ τ'
    unify p (CoreType _ (Copy σ)) (CoreType _ (Copy σ')) = do
      match p σ σ'
    unify p (CoreType _ (RuntimePair σ τ)) (CoreType _ (RuntimePair σ' τ')) = do
      match p σ σ'
      match p τ τ'
    unify p (CoreType _ (RegionTransformer π σ)) (CoreType _ (RegionTransformer π' σ')) = do
      match p π π'
      match p σ σ'
    unify p (CoreType _ (RegionReference π σ)) (CoreType _ (RegionReference π' σ')) = do
      match p π π'
      match p σ σ'
    unify p (CoreType _ (Number ρ1 ρ2)) (CoreType _ (Number ρ1' ρ2')) = do
      lift $ matchKind p ρ1 ρ1'
      lift $ matchKind p ρ2 ρ2'
    unify p σ σ' = lift $ quit $ TypeMismatch p σ σ'

solveType = do
  equations <- getTypeEquations
  case equations of
    [] -> pure mempty
    (TypeEquation p σ σ' : remaining) -> do
      modifyTypeEquations (const remaining)
      ((), θ) <- runWriterT $ unifyType p σ σ'
      θ' <- solveType
      pure $ θ <> θ'
    (TypeSkolemBound p (Bound (Pattern _ x κ) eqs) : remaining) -> do
      θ <- augmentKindEnvironment x p κ maxBound $ do
        modifyTypeEquations (const eqs)
        solveType
      modifyTypeEquations (const (applySubstitution θ remaining))
      θ' <- solveType
      pure $ θ <> θ'

unifyKind :: p -> KindUnify -> KindUnify -> WriterT (Substitution KindLogicalRaw KindUnify) (Core p) ()
unifyKind = unify
  where
    match p κ κ' = lift $ matchKind p κ κ'
    unify _ (CoreKind _ (KindLogical x)) (CoreKind _ (KindLogical x')) | x == x' = pure ()
    unify p (CoreKind _ (KindLogical x)) κ = do
      θ <- lift $ unifyKindVariable p x κ
      tell θ
    unify p κ κ'@(CoreKind _ (KindLogical _)) = unify p κ' κ
    unify _ (CoreKind _ (KindVariable x)) (CoreKind _ (KindVariable x')) | x == x' = pure ()
    unify p (CoreKind _ (Type κ)) (CoreKind _ (Type κ')) = do
      match p κ κ'
    unify _ (CoreKind _ Evidence) (CoreKind _ Evidence) = pure ()
    unify _ (CoreKind _ Region) (CoreKind _ Region) = pure ()
    unify p (CoreKind _ (Runtime κ1 κ2)) (CoreKind _ (Runtime κ1' κ2')) = do
      match p κ1 κ1'
      match p κ2 κ2'
    unify _ (CoreKind _ Code) (CoreKind _ Code) = pure ()
    unify _ (CoreKind _ Data) (CoreKind _ Data) = pure ()
    unify _ (CoreKind _ Imaginary) (CoreKind _ Imaginary) = pure ()
    unify p (CoreKind _ (Real κ)) (CoreKind _ (Real κ')) = do
      match p κ κ'
    unify _ (CoreKind _ Meta) (CoreKind _ Meta) = pure ()
    unify _ (CoreKind _ Text) (CoreKind _ Text) = pure ()
    unify _ (CoreKind _ (KindRuntime PointerRep)) (CoreKind _ (KindRuntime PointerRep)) = pure ()
    unify p (CoreKind _ (KindRuntime (StructRep κs))) (CoreKind _ (KindRuntime (StructRep κs'))) | length κs == length κs' = do
      sequence_ $ zipWith (match p) κs κs'
    unify p (CoreKind _ (KindRuntime (WordRep κ))) (CoreKind _ (KindRuntime (WordRep κ'))) = match p κ κ'
    unify _ (CoreKind _ (KindSize Byte)) (CoreKind _ (KindSize Byte)) = pure ()
    unify _ (CoreKind _ (KindSize Short)) (CoreKind _ (KindSize Short)) = pure ()
    unify _ (CoreKind _ (KindSize Int)) (CoreKind _ (KindSize Int)) = pure ()
    unify _ (CoreKind _ (KindSize Long)) (CoreKind _ (KindSize Long)) = pure ()
    unify _ (CoreKind _ (KindSignedness Signed)) (CoreKind _ (KindSignedness Signed)) = pure ()
    unify _ (CoreKind _ (KindSignedness Unsigned)) (CoreKind _ (KindSignedness Unsigned)) = pure ()
    unify p κ κ' = lift $ quit $ KindMismatch p κ κ'

solveKind = do
  equations <- getKindEquations
  case equations of
    [] -> pure mempty
    (KindEquation p κ κ' : remaining) -> do
      modifyKindEquations (const remaining)
      ((), θ) <- runWriterT $ unifyKind p κ κ'
      θ' <- solveKind
      pure $ θ <> θ'
