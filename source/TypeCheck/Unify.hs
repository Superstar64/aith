module TypeCheck.Unify where

import Ast.Common
import Ast.Kind
import Ast.Sort
import Ast.Type
import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable
import TypeCheck.Core

matchSort _ Kind Kind = pure ()
matchSort _ Representation Representation = pure ()
matchSort _ Size Size = pure ()
matchSort _ Signedness Signedness = pure ()
matchSort p μ μ' = quit $ SortMismatch p μ μ'

sortIsMember p κ μ' = do
  μ <- effectless $ reconstructKind κ
  matchSort p μ μ'

reconstructTypeF indexVariable indexLogical augment make checkRuntime reconstruct = \case
  TypeVariable x -> do
    indexVariable x
  TypeLogical v -> do
    indexLogical v
  Inline _ _ -> do
    pure $ make $ Type
  Forall (Bound pm σ) _ _ -> do
    augment pm $ reconstruct σ
  OfCourse _ -> do
    pure $ make $ Type
  FunctionPointer _ _ _ -> do
    pure $ make $ Pretype $ make $ KindRuntime PointerRep
  FunctionLiteralType _ _ _ -> do
    pure $ make $ Type
  Tuple σs -> go σs []
    where
      go [] κs = pure $ make $ Pretype $ make $ KindRuntime $ StructRep κs
      go (σ : σs) κs = do
        κ <- reconstruct σ
        checkRuntime κ $ \κ -> go σs (κs ++ [κ])
  Effect _ _ -> pure $ make $ Type
  Shared _ _ ->
    pure $ make $ Pretype $ make $ KindRuntime $ PointerRep
  Number _ ρ -> do
    pure $ make $ Pretype $ make $ KindRuntime $ WordRep ρ
  Pointer _ _ ->
    pure $ make $ Boxed
  Boolean -> pure $ make $ Pretype $ make $ KindRuntime $ WordRep $ make $ KindSize $ Byte
  World -> pure $ make $ Region
  Wildcard -> pure $ make $ Length

reconstructKindF indexVariable indexLogical = \case
  KindVariable x -> do
    indexVariable x
  KindLogical v -> do
    indexLogical v
  Type -> pure $ Kind
  Region -> pure $ Kind
  Pretype _ -> pure $ Kind
  Boxed -> pure $ Kind
  Length -> pure $ Kind
  KindRuntime _ -> pure $ Representation
  KindSize _ -> pure $ Size
  KindSignedness _ -> pure $ Signedness

reconstructKind :: KindUnify -> Core Internal Sort
reconstructKind (KindCore κ) = reconstructKindF indexEnvironment indexLogicalMap κ
  where
    indexEnvironment x = mid <$> indexSortEnvironment x
    mid (_, x, _) = x
    index (UnboundKindLogical _ x _) = pure x
    index (LinkKindLogical κ) = reconstructKind κ
    indexLogicalMap x = indexKindLogicalMap x >>= index

effectless :: Core Internal e -> Core p e
effectless e = do
  env <- askEnvironment
  state <- getState
  case runCore e (Internal <$ env) (Internal <$ state) of
    Right e -> pure e
    Left _ -> error "error in effectless"

-- also changes logic type variable levels and check for escaping skolem variables
typeOccursCheck :: forall p. p -> TypeLogical -> Level -> TypeUnify -> Core p ()
typeOccursCheck p x lev σ' = go σ'
  where
    recurse = go
    go :: TypeUnify -> Core p ()
    go (TypeCore σ) = do
      case σ of
        TypeVariable x' -> do
          (_, _, _, _, lev') <- indexKindEnvironment x'
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
        Forall (Bound (TypePatternCore x κ) σ) _ π -> do
          augmentKindOccurs p x κ $ recurse σ
          traverse recurse π
          pure ()
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
        Shared σ π -> do
          recurse σ
          recurse π
        Pointer σ τ -> do
          recurse σ
          recurse τ
        Number _ _ -> pure ()
        Boolean -> pure ()
        World -> pure ()
        Wildcard -> pure ()

kindOccursCheck :: forall p. p -> KindLogical -> Level -> KindUnify -> Core p ()
kindOccursCheck p x lev κ' = go κ'
  where
    recurse = go
    go :: KindUnify -> Core p ()
    go (KindCore κ) =
      case κ of
        KindVariable x' -> do
          (_, _, lev') <- indexSortEnvironment x'
          if lev' > lev
            then quit $ EscapingSkolemKind p x' κ'
            else pure ()
        KindLogical x' | x == x' -> quit $ KindOccursCheck p x κ'
        KindLogical x' ->
          indexKindLogicalMap x' >>= \case
            (UnboundKindLogical p' μ lev') ->
              if lev' > lev
                then do
                  modifyState $ \state -> state {kindLogicalMap = Map.insert x' (UnboundKindLogical p' μ lev) $ kindLogicalMap state}
                else pure ()
            (LinkKindLogical κ) -> recurse κ
        Type -> pure ()
        Region -> pure ()
        Pretype κ -> recurse κ
        Boxed -> pure ()
        Length -> pure ()
        (KindRuntime PointerRep) -> pure ()
        (KindRuntime (StructRep κs)) -> traverse recurse κs >> pure ()
        (KindRuntime (WordRep κ)) -> recurse κ
        (KindSize _) -> pure ()
        (KindSignedness _) -> pure ()

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
              modifyState $ \state -> state {typeLogicalMap = Map.insert x (LinkTypeLogical σ) $ typeLogicalMap state}
              typeOccursCheck p x lev σ
              kindIsMember p σ κ
              -- state modification above may have created a cycle
              -- and if a cycle was created, then it must contain σ
              -- so convert e's solutions back to problems
              -- and let induction take care of it
              reunifyBounds p σ
              for (Set.toList c) $ \c -> do
                constrain p c σ
              for lower (\π -> lessThen p π σ)
              for upper (\π -> lessThen p σ (flexible π))
              pure ()
            (LinkTypeLogical σ') -> unify σ' σ
    unify σ σ'@(TypeCore (TypeLogical _)) = unify σ' σ
    unify (TypeCore (TypeVariable x)) (TypeCore (TypeVariable x')) | x == x' = pure ()
    unify (TypeCore (Inline σ τ)) (TypeCore (Inline σ' τ')) = do
      match p σ σ'
      match p τ τ'
    unify (TypeCore (Forall (Bound (TypePatternCore α κ) σ) c π)) (TypeCore (Forall (Bound (TypePatternCore α' κ') σ') c' π'))
      | c == c',
        length π == length π' = do
        matchKind p κ κ'
        -- A logical variable inside of this forall may have been equated with a type that contains this forall's binding.
        -- To prevent a capture, this forall is alpha converted to  new rigid variable that doesn't exist in the current environment.
        -- This alpha renaming does not convert under logic variables.
        vars <- Map.keysSet <$> kindEnvironment <$> askEnvironment
        let αf = fresh vars α
        let σ2 = convertType αf α σ
        let σ'2 = convertType αf α' σ'
        augmentKindSkolem p αf κ $ match p σ2 σ'2
        sequence $ zipWith (match p) π π'
        pure ()
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
    unify (TypeCore (Shared σ π)) (TypeCore (Shared σ' π')) = do
      match p σ σ'
      match p π π'
    unify (TypeCore (Pointer σ τ)) (TypeCore (Pointer σ' τ')) = do
      match p σ σ'
      match p τ τ'
    unify (TypeCore (Number ρ1 ρ2)) (TypeCore (Number ρ1' ρ2')) = do
      matchKind p ρ1 ρ1'
      matchKind p ρ2 ρ2'
    unify (TypeCore Boolean) (TypeCore Boolean) = pure ()
    unify (TypeCore World) (TypeCore World) = pure ()
    unify (TypeCore Wildcard) (TypeCore Wildcard) = pure ()
    unify σ σ' = quit $ TypeMismatch p σ σ'

matchKind :: p -> KindUnify -> KindUnify -> Core p ()
matchKind p κ κ' = unify κ κ'
  where
    match p κ κ' = matchKind p κ κ'
    -- todo substitute variable if exist first
    unify (KindCore (KindLogical x)) (KindCore (KindLogical x')) | x == x' = pure ()
    unify (KindCore (KindLogical x)) κ =
      indexKindLogicalMap x >>= \case
        (UnboundKindLogical _ μ lev) -> do
          modifyState $ \state -> state {kindLogicalMap = Map.insert x (LinkKindLogical κ) $ kindLogicalMap state}
          kindOccursCheck p x lev κ
          sortIsMember p κ μ
        (LinkKindLogical κ') ->
          unify κ' κ
    unify κ κ'@(KindCore (KindLogical _)) = unify κ' κ
    unify (KindCore (KindVariable x)) (KindCore (KindVariable x')) | x == x' = pure ()
    unify (KindCore Type) (KindCore Type) = pure ()
    unify (KindCore Region) (KindCore Region) = pure ()
    unify (KindCore (Pretype κ)) (KindCore (Pretype κ')) = do
      match p κ κ'
    unify (KindCore Boxed) (KindCore Boxed) = pure ()
    unify (KindCore Length) (KindCore Length) = pure ()
    unify (KindCore (KindRuntime PointerRep)) (KindCore (KindRuntime PointerRep)) = pure ()
    unify (KindCore (KindRuntime (StructRep κs))) (KindCore (KindRuntime (StructRep κs'))) | length κs == length κs' = do
      sequence_ $ zipWith (match p) κs κs'
    unify (KindCore (KindRuntime (WordRep κ))) (KindCore (KindRuntime (WordRep κ'))) = match p κ κ'
    unify (KindCore (KindSize Byte)) (KindCore (KindSize Byte)) = pure ()
    unify (KindCore (KindSize Short)) (KindCore (KindSize Short)) = pure ()
    unify (KindCore (KindSize Int)) (KindCore (KindSize Int)) = pure ()
    unify (KindCore (KindSize Long)) (KindCore (KindSize Long)) = pure ()
    unify (KindCore (KindSize Native)) (KindCore (KindSize Native)) = pure ()
    unify (KindCore (KindSignedness Signed)) (KindCore (KindSignedness Signed)) = pure ()
    unify (KindCore (KindSignedness Unsigned)) (KindCore (KindSignedness Unsigned)) = pure ()
    unify κ κ' = quit $ KindMismatch p κ κ'

predicateKindCheck :: p -> Constraint -> KindUnify -> Core p ()
predicateKindCheck p Copy κ = do
  β <- KindCore <$> KindLogical <$> freshKindVariableRaw p Representation maxBound
  matchKind p κ (KindCore $ Pretype $ β)

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
    predicate c σ@(TypeCore (TypeVariable x)) = do
      (_, κ, cs, _, _) <- indexKindEnvironment x
      predicateKindCheck p c κ
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

-- type with no unification variables
plainType :: p -> TypeUnify -> Core p (Type vκ vσ)
plainType p σ = do
  σ <- zonkType (const $ quit $ ExpectedPlainType p) σ
  σ <- zonkKind (const $ quit $ ExpectedPlainType p) σ
  pure σ

-- type variable or type with no unification variables
plainType' p σ@(TypeCore (TypeLogical x)) =
  indexTypeLogicalMap x >>= \case
    LinkTypeLogical σ -> plainType' p σ
    _ -> pure σ
plainType' p σ = plainType p σ

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
          for upper $ \π -> lessThen p σ (flexible π)
          pure ()
lessThen p (TypeCore (TypeLogical x)) σ' = do
  σ' <- plainType p σ'
  indexTypeLogicalMap x >>= \case
    (LinkTypeLogical σ) -> lessThen p σ (flexible σ')
    (UnboundTypeLogical p' κ c lower upper lev) -> do
      bound <- case upper of
        Nothing -> pure σ'
        Just σ'' -> meet p σ' σ''
      modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundTypeLogical p' κ c lower (Just bound) lev) $ typeLogicalMap state}
      for lower $ \σ -> lessThen p σ (flexible σ')
      pure ()
lessThen p σ σ' = do
  σ <- plainType p σ
  σ' <- plainType p σ'
  lower <- lowerTypeBounds σ'
  if σ `Set.notMember` lower
    then quit $ TypeMisrelation p (flexible σ) (flexible σ')
    else pure ()

kindIsMember :: forall p. p -> TypeUnify -> KindUnify -> Core p ()
kindIsMember p σ κ = do
  κ' <- reconstructType σ
  matchKind p κ κ'
  where
    reconstructType :: TypeUnify -> Core p KindUnify
    reconstructType (TypeCore σ) = reconstructTypeF indexEnvironment indexLogicalMap augment KindCore checkRuntime reconstructType σ
      where
        -- todo use augmentTypePatternBottom
        augment (TypePatternCore x κ) = augmentKindOccurs p x κ
        indexEnvironment x = snd' <$> indexKindEnvironment x
        indexLogicalMap x = indexTypeLogicalMap x >>= index
        index (UnboundTypeLogical _ x _ _ _ _) = pure x
        index (LinkTypeLogical σ) = reconstructType σ
        snd' (_, x, _, _, _) = x
        checkRuntime :: KindUnify -> (KindUnify -> Core p KindUnify) -> Core p KindUnify
        checkRuntime κ f = do
          α <- (KindCore . KindLogical) <$> freshKindVariableRaw p Representation maxBound
          matchKind p κ (KindCore $ Pretype $ α)
          f α
