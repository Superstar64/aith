module TypeCheck.Unify where

import Ast.Common
import Ast.Type
import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable
import TypeCheck.Core

reconstructF indexVariable indexGlobalVariable indexLogical poly checkRuntime reconstruct = \case
  TypeSub (TypeVariable x) -> do
    indexVariable x
  TypeSub (TypeGlobalVariable x) -> do
    indexGlobalVariable x
  TypeLogical v -> do
    indexLogical v
  Inline _ _ _ -> do
    pure $ TypeCore $ Type
  Poly ς -> do
    poly ς
  FunctionPointer _ _ _ -> do
    pure $ TypeCore $ Pretype (TypeCore $ KindRuntime PointerRep) (TypeCore $ TypeSub Unrestricted)
  FunctionLiteralType _ _ _ -> do
    pure $ TypeCore $ Type
  Tuple σs τ -> do
    σs <- go σs []
    pure $ TypeCore $ Pretype (TypeCore $ KindRuntime $ StructRep σs) τ
    where
      go [] κs = pure κs
      go (σ : σs) κs = do
        κ <- reconstruct σ
        checkRuntime κ $ \κ -> go σs (κs ++ [κ])
  Effect _ _ -> pure $ TypeCore $ Type
  Unique _ ->
    pure $ TypeCore $ Pretype (TypeCore $ KindRuntime $ PointerRep) (TypeCore $ TypeSub Linear)
  Shared _ _ ->
    pure $ TypeCore $ Pretype (TypeCore $ KindRuntime $ PointerRep) (TypeCore $ TypeSub Unrestricted)
  Number _ ρ -> do
    pure $ TypeCore $ Pretype (TypeCore $ KindRuntime $ WordRep ρ) (TypeCore $ TypeSub Unrestricted)
  Pointer _ -> pure $ TypeCore $ Boxed
  Array _ -> pure $ TypeCore $ Boxed
  Boolean -> pure $ TypeCore $ Pretype (TypeCore $ KindRuntime $ WordRep $ TypeCore $ KindSize $ Byte) (TypeCore $ TypeSub Unrestricted)
  TypeSub World -> pure $ TypeCore $ Region
  TypeSub Linear -> pure $ TypeCore $ Multiplicity
  TypeSub Unrestricted -> pure $ TypeCore $ Multiplicity
  Type -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Transparent)
  Region -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Subtypable) (TypeCore $ Top Transparent)
  Pretype _ _ -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Transparent)
  Boxed -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Transparent)
  Multiplicity -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Subtypable) (TypeCore $ Top Transparent)
  KindRuntime _ -> pure $ TypeCore $ Representation
  KindSize _ -> pure $ TypeCore $ Size
  KindSignedness _ -> pure $ TypeCore $ Signedness
  Representation -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Opaque)
  Size -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Opaque)
  Signedness -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Opaque)
  Top _ -> error "reconstruct top"

-- also changes logic type variable levels and check for escaping skolem variables
typeOccursCheck :: forall p. p -> TypeLogical -> Level -> TypeUnify -> Core p ()
typeOccursCheck p x lev σ' = go σ'
  where
    recurse = go
    go :: TypeUnify -> Core p ()
    go (TypeCore σ) = do
      case σ of
        TypeSub (TypeVariable x') -> do
          indexKindEnvironment x' >>= \case
            TypeBinding _ _ _ lev' ->
              if lev' > lev
                then quit $ EscapingSkolemType p x' σ'
                else pure ()
            LinkTypeBinding _ -> pure ()
        TypeSub (TypeGlobalVariable x') -> do
          indexKindGlobalEnvironment x' >>= \case
            TypeBinding _ _ _ lev' ->
              if lev' > lev
                then quit $ EscapingSkolemTypeGlobal p x' σ'
                else pure ()
            LinkTypeBinding _ -> pure ()
        TypeLogical x' | x == x' -> quit $ TypeOccursCheck p x σ'
        TypeLogical x' ->
          indexTypeLogicalMap x' >>= \case
            (UnboundTypeLogical p' κ lower upper lev') ->
              if lev' > lev
                then do
                  modifyState $ \state -> state {typeLogicalMap = Map.insert x' (UnboundTypeLogical p' κ lower upper lev) $ typeLogicalMap state}
                else pure ()
            (LinkTypeLogical σ) -> recurse σ
        Inline σ π τ -> do
          recurse σ
          recurse π
          recurse τ
        Poly ς -> occursPoly ς
        FunctionPointer σ π τ -> do
          recurse σ
          recurse π
          recurse τ
        FunctionLiteralType σ π τ -> do
          recurse σ
          recurse π
          recurse τ
        Tuple σs τ -> do
          traverse recurse σs
          recurse τ
          pure ()
        Effect σ τ -> do
          recurse σ
          recurse τ
        Unique σ -> do
          recurse σ
        Shared σ π -> do
          recurse σ
          recurse π
        Pointer σ -> recurse σ
        Array σ -> recurse σ
        Number _ _ -> pure ()
        Boolean -> pure ()
        TypeSub World -> pure ()
        TypeSub Linear -> pure ()
        TypeSub Unrestricted -> pure ()
        Type -> pure ()
        Region -> pure ()
        Pretype κ τ -> do
          recurse κ
          recurse τ
        Boxed -> pure ()
        Multiplicity -> pure ()
        (KindRuntime PointerRep) -> pure ()
        (KindRuntime (StructRep κs)) -> traverse recurse κs >> pure ()
        (KindRuntime (WordRep κ)) -> recurse κ
        (KindSize _) -> pure ()
        (KindSignedness _) -> pure ()
        Representation -> pure ()
        Size -> pure ()
        Signedness -> pure ()
        Top (Kind σ τ) -> do
          recurse σ
          recurse τ
        Top Invariant -> pure ()
        Top Subtypable -> pure ()
        Top Transparent -> pure ()
        Top Opaque -> pure ()
    occursPoly (TypeSchemeCore ς) = case ς of
      MonoType σ -> recurse σ
      TypeForall (Bound (TypePattern x κ π) ς) -> do
        augmentKindUnify True p x $ occursPoly ς
        traverse recurse π
        recurse κ
        pure ()

matchType :: p -> TypeUnify -> TypeUnify -> Core p ()
matchType p σ σ' = unify σ σ'
  where
    reunifyBounds p (TypeCore (TypeLogical x)) =
      indexTypeLogicalMap x >>= \case
        LinkTypeLogical σ -> reunifyBounds p σ
        UnboundTypeLogical p' κ lower upper lev -> do
          modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundTypeLogical p' κ [] upper lev) $ typeLogicalMap state}
          for lower $ \π -> lessThen p π (TypeCore (TypeLogical x))
          pure ()
    reunifyBounds _ _ = pure ()
    unify (TypeCore (TypeLogical x)) (TypeCore (TypeLogical x')) | x == x' = pure ()
    -- Big rule: Unifing a logic type variable does not avoid captures
    -- Rigid type variable scopes cannot shadow other rigid type variables
    unify (TypeCore (TypeLogical x)) σ
      | (TypeCore (TypeLogical x')) <- σ =
        indexTypeLogicalMap x' >>= \case
          LinkTypeLogical σ -> unify (TypeCore $ TypeLogical x) σ
          _ -> unifyVariable
      | otherwise = unifyVariable
      where
        unifyVariable =
          indexTypeLogicalMap x >>= \case
            (UnboundTypeLogical _ κ lower upper lev) -> do
              typeOccursCheck p x lev σ
              kindIsMember p σ κ
              modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkTypeLogical σ) $ typeLogicalMap state}
              -- state modification above may have created a cycle
              -- and if a cycle was created, then it must contain σ
              -- so convert e's solutions back to problems
              -- and let induction take care of it
              reunifyBounds p σ
              for lower (\π -> lessThen p π σ)
              for upper (\π -> lessThen p σ (TypeCore $ TypeSub π))
              pure ()
            (LinkTypeLogical σ') -> unify σ' σ
    unify σ σ'@(TypeCore (TypeLogical _)) = unify σ' σ
    unify (TypeCore (TypeSub σ)) (TypeCore (TypeSub σ')) | σ == σ' = pure ()
    unify σ@(TypeCore (TypeSub (TypeVariable x))) σ' =
      indexKindEnvironment x >>= \case
        TypeBinding _ _ _ _ -> quit $ TypeMismatch p σ σ'
        LinkTypeBinding σ -> unify (flexible σ) σ'
    unify σ@(TypeCore (TypeSub (TypeGlobalVariable x))) σ' =
      indexKindGlobalEnvironment x >>= \case
        TypeBinding _ _ _ _ -> quit $ TypeMismatch p σ σ'
        LinkTypeBinding σ -> unify (flexible σ) σ'
    unify σ σ'@(TypeCore (TypeSub (TypeVariable _))) = unify σ' σ
    unify σ σ'@(TypeCore (TypeSub (TypeGlobalVariable _))) = unify σ' σ
    unify (TypeCore (Inline σ π τ)) (TypeCore (Inline σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (TypeCore (Poly ς)) (TypeCore (Poly ς')) = unifyPoly ς ς'
    unify (TypeCore (FunctionPointer σ π τ)) (TypeCore (FunctionPointer σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (TypeCore (FunctionLiteralType σ π τ)) (TypeCore (FunctionLiteralType σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (TypeCore (Tuple σs τ)) (TypeCore (Tuple σs' τ')) | length σs == length σs' = do
      sequence $ zipWith (unify) σs σs'
      unify τ τ'
      pure ()
    unify (TypeCore (Effect σ π)) (TypeCore (Effect σ' π')) = do
      unify σ σ'
      unify π π'
    unify (TypeCore (Unique σ)) (TypeCore (Unique σ')) = do
      unify σ σ'
    unify (TypeCore (Shared σ π)) (TypeCore (Shared σ' π')) = do
      unify σ σ'
      unify π π'
    unify (TypeCore (Pointer σ)) (TypeCore (Pointer σ')) = do
      unify σ σ'
    unify (TypeCore (Array σ)) (TypeCore (Array σ')) = do
      unify σ σ'
    unify (TypeCore (Number ρ1 ρ2)) (TypeCore (Number ρ1' ρ2')) = do
      unify ρ1 ρ1'
      unify ρ2 ρ2'
    unify (TypeCore Boolean) (TypeCore Boolean) = pure ()
    unify (TypeCore Type) (TypeCore Type) = pure ()
    unify (TypeCore Region) (TypeCore Region) = pure ()
    unify (TypeCore (Pretype κ τ)) (TypeCore (Pretype κ' τ')) = do
      unify κ κ'
      unify τ τ'
    unify (TypeCore Boxed) (TypeCore Boxed) = pure ()
    unify (TypeCore Multiplicity) (TypeCore Multiplicity) = pure ()
    unify (TypeCore (KindRuntime PointerRep)) (TypeCore (KindRuntime PointerRep)) = pure ()
    unify (TypeCore (KindRuntime (StructRep κs))) (TypeCore (KindRuntime (StructRep κs'))) | length κs == length κs' = do
      sequence_ $ zipWith (unify) κs κs'
    unify (TypeCore (KindRuntime (WordRep κ))) (TypeCore (KindRuntime (WordRep κ'))) = unify κ κ'
    unify (TypeCore (KindSize Byte)) (TypeCore (KindSize Byte)) = pure ()
    unify (TypeCore (KindSize Short)) (TypeCore (KindSize Short)) = pure ()
    unify (TypeCore (KindSize Int)) (TypeCore (KindSize Int)) = pure ()
    unify (TypeCore (KindSize Long)) (TypeCore (KindSize Long)) = pure ()
    unify (TypeCore (KindSize Native)) (TypeCore (KindSize Native)) = pure ()
    unify (TypeCore (KindSignedness Signed)) (TypeCore (KindSignedness Signed)) = pure ()
    unify (TypeCore (KindSignedness Unsigned)) (TypeCore (KindSignedness Unsigned)) = pure ()
    unify (TypeCore Representation) (TypeCore Representation) = pure ()
    unify (TypeCore Size) (TypeCore Size) = pure ()
    unify (TypeCore Signedness) (TypeCore Signedness) = pure ()
    unify (TypeCore (Top (Kind σ τ))) (TypeCore (Top (Kind σ' τ'))) = do
      unify σ σ'
      unify τ τ'
    unify (TypeCore (Top Invariant)) (TypeCore (Top Invariant)) = pure ()
    unify (TypeCore (Top Subtypable)) (TypeCore (Top Subtypable)) = pure ()
    unify (TypeCore (Top Transparent)) (TypeCore (Top Transparent)) = pure ()
    unify (TypeCore (Top Opaque)) (TypeCore (Top Opaque)) = pure ()
    unify σ σ' = quit $ TypeMismatch p σ σ'

    unifyPoly
      (TypeSchemeCore (TypeForall (Bound (TypePattern α κ π) ς)))
      (TypeSchemeCore (TypeForall (Bound (TypePattern α' κ' π') ς')))
        | length π == length π' = do
          unify κ κ'
          -- A logical variable inside of this forall may have been equated with a type that contains this forall's binding.
          -- To prevent a capture, this forall is alpha converted to  new rigid variable that doesn't exist in the current environment.
          -- This alpha renaming does not convert under logic variables.
          vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
          let αf = fresh vars α
          let ς2 = convertType αf α ς
          let ς'2 = convertType αf α' ς'
          augmentKindUnify False p αf $ unifyPoly ς2 ς'2
          sequence $ zipWith (unify) π π'
          pure ()
    unifyPoly
      (TypeSchemeCore (MonoType σ))
      (TypeSchemeCore (MonoType σ')) =
        unify σ σ'
    unifyPoly ς ς' = quit $ TypeMismatch p (TypeCore $ Poly ς) (TypeCore $ Poly ς')

reachLogical x (TypeCore (TypeLogical x')) | x == x' = pure True
reachLogical x (TypeCore (TypeLogical x')) =
  indexTypeLogicalMap x' >>= \case
    (UnboundTypeLogical _ _ lower _ _) -> do
      or <$> traverse (reachLogical x) lower
    (LinkTypeLogical σ) -> reachLogical x σ
reachLogical _ _ = pure False

maximal _ _ [] [max] = pure max
maximal p base (π : πs) candidates = do
  candidates <- flip filterM candidates $ \π' -> do
    lower <- lowerTypeBounds π'
    pure (π `Set.member` lower)
  maximal p base πs candidates
maximal p (π, π') _ _ = quit $ NoCommonMeet p π π'

meet p π π' = do
  lower1 <- lowerTypeBounds π
  lower2 <- lowerTypeBounds π'
  maximal p (π, π') (Set.toList $ Set.intersection lower1 lower2) (Set.toList $ Set.intersection lower1 lower2)

-- type that is subtypable
plainType :: p -> Type v -> Core p TypeSub
plainType p (TypeCore (TypeSub σ@(TypeVariable x))) =
  indexKindEnvironment x >>= \case
    TypeBinding _ _ _ _ -> pure σ
    LinkTypeBinding σ -> plainType p σ
plainType _ (TypeCore (TypeSub σ)) = pure σ
plainType p _ = quit $ ExpectedPlainType p

plainType' p σ@(TypeCore (TypeLogical x)) =
  indexTypeLogicalMap x >>= \case
    LinkTypeLogical σ -> plainType' p σ
    _ -> pure σ
plainType' p σ = TypeCore <$> TypeSub <$> plainType p σ

-- todo switch to greater then
lessThen :: p -> TypeUnify -> TypeUnify -> Core p ()
lessThen p σ (TypeCore (TypeLogical x)) = do
  σ <- plainType' p σ
  indexTypeLogicalMap x >>= \case
    (LinkTypeLogical σ') -> lessThen p σ σ'
    (UnboundTypeLogical p' κ lower upper lev) ->
      reachLogical x σ >>= \case
        True -> matchType p (TypeCore (TypeLogical x)) σ
        False -> do
          -- todo occurance here maybe?
          modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundTypeLogical p' κ (σ : lower) upper lev) $ typeLogicalMap state}
          for upper $ \π -> lessThen p σ (TypeCore $ TypeSub $ π)
          pure ()
lessThen p (TypeCore (TypeLogical x)) σ' = do
  σ' <- plainType p σ'
  indexTypeLogicalMap x >>= \case
    (LinkTypeLogical σ) -> lessThen p σ (TypeCore $ TypeSub σ')
    (UnboundTypeLogical p' κ lower upper lev) -> do
      bound <- case upper of
        Nothing -> pure σ'
        Just σ'' -> meet p σ' σ''
      modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundTypeLogical p' κ lower (Just bound) lev) $ typeLogicalMap state}
      for lower $ \σ -> lessThen p σ (TypeCore $ TypeSub σ')
      pure ()
lessThen p σ σ' = do
  σ <- plainType p σ
  σ' <- plainType p σ'
  lower <- lowerTypeBounds σ'
  if σ `Set.notMember` lower
    then quit $ TypeMisrelation p σ σ'
    else pure ()

kindIsMember :: forall p. p -> TypeUnify -> TypeUnify -> Core p ()
kindIsMember p (TypeCore (Top _)) _ = quit $ NotTypable p
kindIsMember p σ κ = do
  κ' <- reconstruct p σ
  matchType p κ κ'

reconstruct :: forall p. p -> TypeUnify -> Core p TypeUnify
reconstruct p (TypeCore σ) = go σ
  where
    go = reconstructF indexEnvironment indexGlobalEnvironment indexLogicalMap poly checkRuntime (reconstruct p)
    poly (TypeSchemeCore (TypeForall _)) = pure $ TypeCore $ Type
    poly (TypeSchemeCore (MonoType (TypeCore σ))) = go σ

    indexEnvironment x = indexKindEnvironment x >>= kind
      where
        kind (TypeBinding _ κ _ _) = pure $ flexible κ
        kind (LinkTypeBinding σ) = reconstruct p (flexible σ)
    indexGlobalEnvironment x = indexKindGlobalEnvironment x >>= kind
      where
        kind (TypeBinding _ κ _ _) = pure $ flexible κ
        kind (LinkTypeBinding σ) = reconstruct p (flexible σ)
    indexLogicalMap x = indexTypeLogicalMap x >>= index
    index (UnboundTypeLogical _ x _ _ _) = pure x
    index (LinkTypeLogical σ) = reconstruct p σ
    checkRuntime κ f = do
      α <- (TypeCore . TypeLogical) <$> freshKindVariableRaw p (TypeCore Representation) maxBound
      β <- (TypeCore . TypeLogical) <$> freshKindVariableRaw p (TypeCore Multiplicity) maxBound
      matchType p κ (TypeCore $ Pretype α β)
      f α
