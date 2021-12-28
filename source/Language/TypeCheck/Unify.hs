module Language.TypeCheck.Unify where

import Control.Monad.Trans (lift)
import Control.Monad.Writer (WriterT, runWriterT, tell)
import Data.Maybe (fromJust)
import Language.Ast.Common
import Language.Ast.Kind
import Language.Ast.Sort
import Language.Ast.Type
import Language.TypeCheck.Core
import Language.TypeCheck.Substitute

matchType p σ σ' = insertEquation (TypeEquation p σ σ')

matchKind p κ κ' = insertEquation (KindEquation p κ κ')

kindIsMember p σ κ = insertEquation (KindMember p σ κ)

matchSort _ Kind Kind = pure ()
matchSort _ Stage Stage = pure ()
matchSort _ Existance Existance = pure ()
matchSort _ Representation Representation = pure ()
matchSort _ Size Size = pure ()
matchSort _ Signedness Signedness = pure ()
matchSort p μ μ' = quit $ SortMismatch p μ μ'

sortIsMember p κ μ' = do
  μ <- effectless $ reconstructKind indexSortEnvironment indexVariableMap κ
  matchSort p μ μ'
  where
    indexSortEnvironment x = mid <$> fromJust <$> lookupSortEnvironment x
    mid (_, x, _) = x
    indexVariableMap x = mid <$> indexKindVariableMap x

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
    reconstruct (CoreType _ (FunctionPointer _ _ _)) = do
      pure $ CoreKind Internal $ Pretype $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime PointerRep
    reconstruct (CoreType _ (FunctionLiteralType _ _ _)) = do
      pure $ CoreKind Internal $ Type $ CoreKind Internal $ Text
    reconstruct (CoreType _ (Copy _)) = do
      pure $ CoreKind Internal $ Type $ CoreKind Internal $ Evidence
    reconstruct (CoreType _ (Pair σ σ')) = do
      κ <- reconstruct σ
      κ' <- reconstruct σ'
      case (κ, κ') of
        ( CoreKind _ (Pretype (CoreKind _ (Real κ))),
          CoreKind _ (Pretype (CoreKind _ (Real κ')))
          ) -> do
            pure $
              CoreKind Internal $ Pretype $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ StructRep [κ, κ']
        _ -> error $ "reconstruction of pair didn't return pretype" ++ show (σ, σ', κ, κ')
    reconstruct (CoreType _ (Effect _ _)) = pure $ CoreKind Internal $ Type $ CoreKind Internal $ Runtime
    reconstruct (CoreType _ (Number _ ρ)) = do
      pure $ CoreKind Internal $ Pretype $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ WordRep ρ
    reconstruct (CoreType _ (Reference _ _)) =
      pure $ CoreKind Internal $ Pretype $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ PointerRep

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
    reconstruct (CoreKind _ Runtime) = pure $ Stage
    reconstruct (CoreKind _ (Pretype _)) = pure $ Kind
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
        FunctionPointer σ π τ -> do
          recurse σ
          recurse π
          recurse τ
        FunctionLiteralType σ π τ -> do
          recurse σ
          recurse π
          recurse τ
        Copy σ -> recurse σ
        Pair σ τ -> do
          recurse σ
          recurse τ
        Effect σ τ -> do
          recurse σ
          recurse τ
        Reference σ τ -> do
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
        Runtime -> pure ()
        Pretype κ -> recurse κ
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
  Core p Substitution
unifyTypeVariable p x σ = do
  typeOccursCheck σ p x σ
  (_, κ, _) <- indexTypeVariableMap x
  kindIsMember p σ κ
  apply σ x
  pure $ singleTypeSubstitution x σ
  where
    apply σ x = do
      modifyEquations (substitute σ x)

unifyKindVariable p x κ = do
  kindOccursCheck κ p x κ
  (_, μ, _) <- indexKindVariableMap x
  sortIsMember p κ μ
  apply κ x
  pure $ singleKindSubstitution x κ
  where
    apply κ x = do
      modifyEquations (substitute κ x)
      modifyTypeVariableMap (fmap $ middle $ substitute κ x)
      where
        middle f (a, b, c) = (a, f b, c)

unifyType :: p -> TypeUnify -> TypeUnify -> WriterT Substitution (Core p) ()
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
      lift $ insertEquation (TypeSkolemBound p (Bound pm [TypeEquation p σ σ'']))
    unify p (CoreType _ (Implied σ τ)) (CoreType _ (Implied σ' τ')) = do
      match p σ σ'
      match p τ τ'
    unify p (CoreType _ (OfCourse σ)) (CoreType _ (OfCourse σ')) = do
      match p σ σ'
    unify p (CoreType _ (FunctionPointer σ π τ)) (CoreType _ (FunctionPointer σ' π' τ')) = do
      match p σ σ'
      match p π π'
      match p τ τ'
    unify p (CoreType _ (FunctionLiteralType σ π τ)) (CoreType _ (FunctionLiteralType σ' π' τ')) = do
      match p σ σ'
      match p π π'
      match p τ τ'
    unify p (CoreType _ (Copy σ)) (CoreType _ (Copy σ')) = do
      match p σ σ'
    unify p (CoreType _ (Pair σ τ)) (CoreType _ (Pair σ' τ')) = do
      match p σ σ'
      match p τ τ'
    unify p (CoreType _ (Effect σ π)) (CoreType _ (Effect σ' π')) = do
      match p σ σ'
      match p π π'
    unify p (CoreType _ (Reference π σ)) (CoreType _ (Reference π' σ')) = do
      match p π π'
      match p σ σ'
    unify p (CoreType _ (Number ρ1 ρ2)) (CoreType _ (Number ρ1' ρ2')) = do
      lift $ matchKind p ρ1 ρ1'
      lift $ matchKind p ρ2 ρ2'
    unify p σ σ' = lift $ quit $ TypeMismatch p σ σ'

solve = do
  equations <- getEquations
  case equations of
    [] -> pure mempty
    ((TypeEquation p σ σ') : remaining) -> do
      modifyEquations (const remaining)
      ((), θ) <- runWriterT $ unifyType p σ σ'
      θ' <- solve
      pure $ θ <> θ'
    (TypeSkolemBound p (Bound (Pattern _ x κ) eqs) : remaining) -> do
      θ <- augmentKindEnvironment x p κ maxBound $ do
        modifyEquations (const eqs)
        solve
      modifyEquations (const (applySubstitution θ remaining))
      θ' <- solve
      pure $ θ <> θ'
    (KindEquation p κ κ' : remaining) -> do
      modifyEquations (const remaining)
      ((), θ) <- runWriterT $ unifyKind p κ κ'
      θ' <- solve
      pure $ θ <> θ'
    -- todo figure out how to remove corner case
    (KindMember p (CoreType Internal (Pair σ σ')) κ : remaining) -> do
      modifyEquations (const remaining)
      α <- (CoreKind Internal . KindLogical) <$> freshKindVariableRaw p Representation maxBound
      α' <- (CoreKind Internal . KindLogical) <$> freshKindVariableRaw p Representation maxBound
      kindIsMember p σ (CoreKind Internal $ Pretype $ CoreKind Internal $ Real α)
      kindIsMember p σ' (CoreKind Internal $ Pretype $ CoreKind Internal $ Real α')
      matchKind p κ (CoreKind Internal $ Pretype $ CoreKind Internal $ Real $ CoreKind Internal $ KindRuntime $ StructRep [α, α'])
      solve
    (KindMember p σ κ : remaining) -> do
      modifyEquations (const remaining)
      κ' <- effectless $ reconstructType indexKindEnvironment indexVariableMap augment σ
      matchKind p κ κ'
      solve
      where
        indexKindEnvironment x = mid <$> fromJust <$> lookupKindEnvironment x
          where
            mid (_, x, _) = x
        indexVariableMap x = mid <$> indexTypeVariableMap x
        augment (Pattern p x κ) = augmentKindEnvironment x p κ (error "level usage during kind checking")
        mid (_, x, _) = x

unifyKind :: p -> KindUnify -> KindUnify -> WriterT Substitution (Core p) ()
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
    unify _ (CoreKind _ Runtime) (CoreKind _ Runtime) = pure ()
    unify p (CoreKind _ (Pretype κ)) (CoreKind _ (Pretype κ')) = do
      match p κ κ'
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
