module TypeCheck.Unify where

import Ast.Common
import Ast.Type
import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable
import TypeCheck.Core

reconstructF indexVariable indexLogical poly checkRuntime reconstruct = \case
  TypeSub (TypeVariable x) -> do
    indexVariable x
  TypeLogical v -> do
    indexLogical v
  Inline _ _ -> do
    pure $ TypeCore $ Type
  Poly ς -> do
    poly ς
  OfCourse _ -> do
    pure $ TypeCore $ Type
  FunctionPointer _ _ _ -> do
    pure $ TypeCore $ Pretype $ TypeCore $ KindRuntime PointerRep
  FunctionLiteralType _ _ _ -> do
    pure $ TypeCore $ Type
  Tuple σs -> go σs []
    where
      go [] κs = pure $ TypeCore $ Pretype $ TypeCore $ KindRuntime $ StructRep κs
      go (σ : σs) κs = do
        κ <- reconstruct σ
        checkRuntime κ $ \κ -> go σs (κs ++ [κ])
  Effect _ _ -> pure $ TypeCore $ Type
  Unique _ ->
    pure $ TypeCore $ Pretype $ TypeCore $ KindRuntime $ PointerRep
  Shared _ _ ->
    pure $ TypeCore $ Pretype $ TypeCore $ KindRuntime $ PointerRep
  Number _ ρ -> do
    pure $ TypeCore $ Pretype $ TypeCore $ KindRuntime $ WordRep ρ
  Pointer _ -> pure $ TypeCore $ Boxed
  Array _ -> pure $ TypeCore $ Boxed
  Boolean -> pure $ TypeCore $ Pretype $ TypeCore $ KindRuntime $ WordRep $ TypeCore $ KindSize $ Byte
  TypeSub World -> pure $ TypeCore $ Region
  Type -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Transparent)
  Region -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Subtypable) (TypeCore $ Top Transparent)
  Pretype _ -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Transparent)
  Boxed -> pure $ TypeCore $ Top $ Kind (TypeCore $ Top Invariant) (TypeCore $ Top Transparent)
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
          TypeBinding _ _ _ _ lev' <- indexKindEnvironment x'
          if lev' > lev
            then quit $ EscapingSkolemType p x' σ'
            else pure ()
        TypeLogical x' | x == x' -> quit $ TypeOccursCheck p x σ'
        TypeLogical x' ->
          indexTypeLogicalMap x' >>= \case
            (UnboundTypeLogical p' κ c lower upper lev') ->
              if lev' > lev
                then do
                  modifyState $ \state -> state {typeLogicalMap = Map.insert x' (UnboundTypeLogical p' κ c lower upper lev) $ typeLogicalMap state}
                else pure ()
            (LinkTypeLogical σ) -> recurse σ
        Inline σ τ -> do
          recurse σ
          recurse τ
        Poly ς -> occursPoly ς
        OfCourse σ -> recurse σ
        FunctionPointer σ π τ -> do
          recurse σ
          recurse π
          recurse τ
        FunctionLiteralType σ π τ -> do
          recurse σ
          recurse π
          recurse τ
        Tuple σs -> do
          traverse recurse σs
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
        Type -> pure ()
        Region -> pure ()
        Pretype κ -> recurse κ
        Boxed -> pure ()
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
      TypeForall (Bound (TypePattern x _ _ π) ς) -> do
        augmentKindUnify True p x $ occursPoly ς
        traverse recurse π
        pure ()

matchType :: p -> TypeUnify -> TypeUnify -> Core p ()
matchType p σ σ' = unify σ σ'
  where
    match p σ σ' = matchType p σ σ'
    reunifyBounds p (TypeCore (TypeLogical x)) =
      indexTypeLogicalMap x >>= \case
        LinkTypeLogical σ -> reunifyBounds p σ
        UnboundTypeLogical p' κ c lower upper lev -> do
          modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundTypeLogical p' κ c [] upper lev) $ typeLogicalMap state}
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
            (UnboundTypeLogical _ κ c lower upper lev) -> do
              typeOccursCheck p x lev σ
              kindIsMember p σ κ
              modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkTypeLogical σ) $ typeLogicalMap state}
              -- state modification above may have created a cycle
              -- and if a cycle was created, then it must contain σ
              -- so convert e's solutions back to problems
              -- and let induction take care of it
              reunifyBounds p σ
              for (Set.toList c) $ \c -> do
                constrain p c σ
              for lower (\π -> lessThen p π σ)
              for upper (\π -> lessThen p σ (TypeCore $ TypeSub π))
              pure ()
            (LinkTypeLogical σ') -> unify σ' σ
    unify σ σ'@(TypeCore (TypeLogical _)) = unify σ' σ
    unify (TypeCore (TypeSub (TypeVariable x))) (TypeCore (TypeSub (TypeVariable x'))) | x == x' = pure ()
    unify (TypeCore (Inline σ τ)) (TypeCore (Inline σ' τ')) = do
      match p σ σ'
      match p τ τ'
    unify (TypeCore (Poly ς)) (TypeCore (Poly ς')) = unifyPoly ς ς'
    unify (TypeCore (OfCourse σ)) (TypeCore (OfCourse σ')) = do
      match p σ σ'
    unify (TypeCore (FunctionPointer σ π τ)) (TypeCore (FunctionPointer σ' π' τ')) = do
      match p σ σ'
      match p π π'
      match p τ τ'
    unify (TypeCore (FunctionLiteralType σ π τ)) (TypeCore (FunctionLiteralType σ' π' τ')) = do
      match p σ σ'
      match p π π'
      match p τ τ'
    unify (TypeCore (Tuple σs)) (TypeCore (Tuple σs')) | length σs == length σs' = do
      sequence $ zipWith (match p) σs σs'
      pure ()
    unify (TypeCore (Effect σ π)) (TypeCore (Effect σ' π')) = do
      match p σ σ'
      match p π π'
    unify (TypeCore (Unique σ)) (TypeCore (Unique σ')) = do
      match p σ σ'
    unify (TypeCore (Shared σ π)) (TypeCore (Shared σ' π')) = do
      match p σ σ'
      match p π π'
    unify (TypeCore (Pointer σ)) (TypeCore (Pointer σ')) = do
      match p σ σ'
    unify (TypeCore (Array σ)) (TypeCore (Array σ')) = do
      match p σ σ'
    unify (TypeCore (Number ρ1 ρ2)) (TypeCore (Number ρ1' ρ2')) = do
      match p ρ1 ρ1'
      match p ρ2 ρ2'
    unify (TypeCore Boolean) (TypeCore Boolean) = pure ()
    unify (TypeCore (TypeSub World)) (TypeCore (TypeSub World)) = pure ()
    unify (TypeCore Type) (TypeCore Type) = pure ()
    unify (TypeCore Region) (TypeCore Region) = pure ()
    unify (TypeCore (Pretype κ)) (TypeCore (Pretype κ')) = do
      match p κ κ'
    unify (TypeCore Boxed) (TypeCore Boxed) = pure ()
    unify (TypeCore (KindRuntime PointerRep)) (TypeCore (KindRuntime PointerRep)) = pure ()
    unify (TypeCore (KindRuntime (StructRep κs))) (TypeCore (KindRuntime (StructRep κs'))) | length κs == length κs' = do
      sequence_ $ zipWith (match p) κs κs'
    unify (TypeCore (KindRuntime (WordRep κ))) (TypeCore (KindRuntime (WordRep κ'))) = match p κ κ'
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
      match p σ σ'
      match p τ τ'
    unify (TypeCore (Top Invariant)) (TypeCore (Top Invariant)) = pure ()
    unify (TypeCore (Top Subtypable)) (TypeCore (Top Subtypable)) = pure ()
    unify (TypeCore (Top Transparent)) (TypeCore (Top Transparent)) = pure ()
    unify (TypeCore (Top Opaque)) (TypeCore (Top Opaque)) = pure ()
    unify σ σ' = quit $ TypeMismatch p σ σ'

    unifyPoly
      (TypeSchemeCore (TypeForall (Bound (TypePattern α κ c π) ς)))
      (TypeSchemeCore (TypeForall (Bound (TypePattern α' κ' c' π') ς')))
        | c == c',
          length π == length π' = do
          match p κ κ'
          -- A logical variable inside of this forall may have been equated with a type that contains this forall's binding.
          -- To prevent a capture, this forall is alpha converted to  new rigid variable that doesn't exist in the current environment.
          -- This alpha renaming does not convert under logic variables.
          vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
          let αf = fresh vars α
          let ς2 = convertType αf α ς
          let ς'2 = convertType αf α' ς'
          augmentKindUnify False p αf $ unifyPoly ς2 ς'2
          sequence $ zipWith (match p) π π'
          pure ()
    unifyPoly
      (TypeSchemeCore (MonoType σ))
      (TypeSchemeCore (MonoType σ')) =
        unify σ σ'
    unifyPoly ς ς' = quit $ TypeMismatch p (TypeCore $ Poly ς) (TypeCore $ Poly ς')

predicateKindCheck :: p -> Constraint -> TypeUnify -> Core p ()
predicateKindCheck p Copy κ = do
  β <- TypeCore <$> TypeLogical <$> freshKindVariableRaw p (TypeCore Representation) maxBound
  matchType p κ (TypeCore $ Pretype $ β)

constrain :: p -> Constraint -> TypeUnify -> Core p ()
constrain p c σ = predicate c σ
  where
    predicate c (TypeCore (TypeLogical x)) =
      indexTypeLogicalMap x >>= \case
        LinkTypeLogical σ -> predicate c σ
        UnboundTypeLogical p' κ cs lower upper lev -> do
          predicateKindCheck p c κ
          case Set.member c cs of
            False -> do
              modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundTypeLogical p' κ (Set.insert c cs) lower upper lev) $ typeLogicalMap state}
            True -> pure ()
    predicate c σ@(TypeCore (TypeSub (TypeVariable x))) = do
      TypeBinding _ κ cs _ _ <- indexKindEnvironment x
      predicateKindCheck p c (flexible κ)
      case Set.member c cs of
        False -> quit $ ConstraintMismatch p c σ
        True -> pure ()
    predicate Copy (TypeCore (Number _ _)) = pure ()
    predicate Copy (TypeCore Boolean) = pure ()
    predicate Copy (TypeCore (FunctionPointer _ _ _)) = pure ()
    predicate Copy (TypeCore (Tuple σs)) = do
      traverse (constrain p Copy) σs
      pure ()
    predicate Copy (TypeCore (Shared _ _)) = pure ()
    predicate c σ = quit $ ConstraintMismatch p c σ

reachLogical x (TypeCore (TypeLogical x')) | x == x' = pure True
reachLogical x (TypeCore (TypeLogical x')) =
  indexTypeLogicalMap x' >>= \case
    (UnboundTypeLogical _ _ _ lower _ _) -> do
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
  maximal p (π, π') (Set.toList $ lower1 <> lower2) (Set.toList $ lower1 <> lower2)

-- type that is subtypable
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
    (UnboundTypeLogical p' κ c lower upper lev) ->
      reachLogical x σ >>= \case
        True -> matchType p (TypeCore (TypeLogical x)) σ
        False -> do
          -- todo occurance here maybe?
          modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundTypeLogical p' κ c (σ : lower) upper lev) $ typeLogicalMap state}
          for upper $ \π -> lessThen p σ (TypeCore $ TypeSub $ π)
          pure ()
lessThen p (TypeCore (TypeLogical x)) σ' = do
  σ' <- plainType p σ'
  indexTypeLogicalMap x >>= \case
    (LinkTypeLogical σ) -> lessThen p σ (TypeCore $ TypeSub σ')
    (UnboundTypeLogical p' κ c lower upper lev) -> do
      bound <- case upper of
        Nothing -> pure σ'
        Just σ'' -> meet p σ' σ''
      modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundTypeLogical p' κ c lower (Just bound) lev) $ typeLogicalMap state}
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
    go = reconstructF indexEnvironment indexLogicalMap poly checkRuntime (reconstruct p)
    poly (TypeSchemeCore (TypeForall _)) = pure $ TypeCore $ Type
    poly (TypeSchemeCore (MonoType (TypeCore σ))) = go σ

    indexEnvironment x = kind <$> indexKindEnvironment x
      where
        kind (TypeBinding _ κ _ _ _) = flexible κ
    indexLogicalMap x = indexTypeLogicalMap x >>= index
    index (UnboundTypeLogical _ x _ _ _ _) = pure x
    index (LinkTypeLogical σ) = reconstruct p σ
    checkRuntime :: TypeUnify -> (TypeUnify -> Core p TypeUnify) -> Core p TypeUnify
    checkRuntime κ f = do
      α <- (TypeCore . TypeLogical) <$> freshKindVariableRaw p (TypeCore Representation) maxBound
      matchType p κ (TypeCore $ Pretype $ α)
      f α
