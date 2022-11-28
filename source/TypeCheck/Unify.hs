module TypeCheck.Unify where

import Ast.Common
import Ast.Type
import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable
import TypeCheck.Core

uni1 = TypeAst () Base

uni2 = TypeAst () (Higher uni1)

reconstructF indexVariable indexGlobalVariable indexLogical poly reconstructRuntime reconstructMultiplicities (TypeAst () σ) = case σ of
  TypeSub (TypeVariable x) -> do
    indexVariable x
  TypeSub (TypeGlobalVariable x) -> do
    indexGlobalVariable x
  TypeLogical v -> do
    indexLogical v
  Inline _ _ _ -> do
    pure $ TypeAst () $ Type
  Poly ς -> do
    poly ς
  FunctionPointer _ _ _ -> do
    pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime PointerRep) (TypeAst () $ TypeSub Unrestricted)
  FunctionLiteralType _ _ _ -> do
    pure $ TypeAst () $ Type
  Tuple σs -> do
    ρs <- traverse reconstructRuntime σs
    τ <- reconstructMultiplicities σs
    pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime $ StructRep ρs) τ
  Step σ τ -> do
    κ <- reconstructRuntime σ
    μ <- reconstructRuntime τ
    let union = TypeAst () $ KindRuntime $ UnionRep $ [κ, μ]
    let wrap = TypeAst () $ KindRuntime $ StructRep $ [TypeAst () $ KindRuntime $ WordRep $ TypeAst () $ KindSize $ Byte, union]
    pure (TypeAst () $ Pretype wrap $ TypeAst () $ TypeSub $ Linear)
  Effect _ _ -> pure $ TypeAst () $ Type
  Unique _ ->
    pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) (TypeAst () $ TypeSub Linear)
  Shared _ _ ->
    pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime $ PointerRep) (TypeAst () $ TypeSub Unrestricted)
  Number _ ρ -> do
    pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime $ WordRep ρ) (TypeAst () $ TypeSub Unrestricted)
  Pointer _ -> pure $ TypeAst () $ Boxed
  Array _ -> pure $ TypeAst () $ Boxed
  Boolean -> pure $ TypeAst () $ Pretype (TypeAst () $ KindRuntime $ WordRep $ TypeAst () $ KindSize $ Byte) (TypeAst () $ TypeSub Unrestricted)
  TypeSub World -> pure $ TypeAst () $ Region
  TypeSub Linear -> pure $ TypeAst () $ Multiplicity
  TypeSub Unrestricted -> pure $ TypeAst () $ Multiplicity
  Type -> pure $ TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Transparent) uni1
  Region -> pure $ TypeAst () $ Kind (TypeAst () Subtypable) (TypeAst () Transparent) uni1
  Pretype _ _ -> pure $ TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Transparent) uni1
  Boxed -> pure $ TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Transparent) uni1
  Multiplicity -> pure $ TypeAst () $ Kind (TypeAst () Subtypable) (TypeAst () Transparent) uni2
  KindRuntime _ -> pure $ TypeAst () $ Representation
  KindSize _ -> pure $ TypeAst () $ Size
  KindSignedness _ -> pure $ TypeAst () $ Signedness
  Representation -> pure $ TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Opaque) uni2
  Size -> pure $ TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Opaque) uni2
  Signedness -> pure $ TypeAst () $ Kind (TypeAst () Invariant) (TypeAst () Opaque) uni1
  Invariant -> pure (TypeAst () Orderability)
  Subtypable -> pure (TypeAst () Orderability)
  Transparent -> pure (TypeAst () Transparency)
  Opaque -> pure (TypeAst () Transparency)
  Transparency -> pure (TypeAst () Top)
  Orderability -> pure (TypeAst () Top)
  Base -> pure (TypeAst () Universe)
  Higher _ -> pure (TypeAst () Universe)
  Universe -> pure (TypeAst () Top)
  Kind σ _ _ -> do
    pure (TypeAst () $ Kind (TypeAst () $ Higher σ) (TypeAst () Invariant) (TypeAst () Transparent))
  Top -> error "reconstruct top"

-- also changes logic type variable levels and check for escaping skolem variables
typeOccursCheck :: forall p. p -> TypeLogical -> Level -> TypeUnify -> Check p ()
typeOccursCheck p x lev σ' = go σ'
  where
    recurse = go
    go :: TypeUnify -> Check p ()
    go (TypeAst () σ) = do
      case σ of
        TypeSub (TypeVariable x') -> do
          indexKindEnvironment x' >>= \case
            TypeBinding _ _ _ lev' _ ->
              if lev' > lev
                then quit $ EscapingSkolemType p x' σ'
                else pure ()
            LinkTypeBinding _ -> pure ()
        TypeSub (TypeGlobalVariable x') -> do
          indexKindGlobalEnvironment x' >>= \case
            TypeBinding _ _ _ lev' _ ->
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
        Step σ τ -> do
          recurse σ
          recurse τ
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
        (KindRuntime (UnionRep κs)) -> traverse recurse κs >> pure ()
        (KindRuntime (WordRep κ)) -> recurse κ
        (KindSize _) -> pure ()
        (KindSignedness _) -> pure ()
        Representation -> pure ()
        Size -> pure ()
        Signedness -> pure ()
        Kind σ τ π -> do
          recurse σ
          recurse τ
          recurse π
        Invariant -> pure ()
        Subtypable -> pure ()
        Transparent -> pure ()
        Opaque -> pure ()
        Top -> pure ()
        Orderability -> pure ()
        Transparency -> pure ()
        Base -> pure ()
        Higher κ -> recurse κ
        Universe -> pure ()
    occursPoly (TypeScheme () ς) = case ς of
      MonoType σ -> recurse σ
      TypeForall (Bound (TypePattern () x κ π) ς) -> do
        augmentKindUnify True p x $ occursPoly ς
        traverse recurse π
        recurse κ
        pure ()

-- if two types unify, that imply that they're kinds are exactly the same
-- the type ast has enough information to uniquely determine a type's kind
matchType :: p -> TypeUnify -> TypeUnify -> Check p ()
matchType p σ σ' = unify σ σ'
  where
    reunifyBounds p (TypeAst () (TypeLogical x)) =
      indexTypeLogicalMap x >>= \case
        LinkTypeLogical σ -> reunifyBounds p σ
        UnboundTypeLogical p' κ lower upper lev -> do
          modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundTypeLogical p' κ [] upper lev) $ typeLogicalMap state}
          for lower $ \π -> lessThen p π (TypeAst () (TypeLogical x))
          pure ()
    reunifyBounds _ _ = pure ()
    unify (TypeAst () (TypeLogical x)) (TypeAst () (TypeLogical x')) | x == x' = pure ()
    -- Big rule: Unifing a logic type variable does not avoid captures
    -- Rigid type variable scopes cannot shadow other rigid type variables
    unify (TypeAst () (TypeLogical x)) σ
      | (TypeAst () (TypeLogical x')) <- σ =
        indexTypeLogicalMap x' >>= \case
          LinkTypeLogical σ -> unify (TypeAst () $ TypeLogical x) σ
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
              for upper (\π -> lessThen p σ (TypeAst () $ TypeSub π))
              pure ()
            (LinkTypeLogical σ') -> unify σ' σ
    unify σ σ'@(TypeAst () (TypeLogical _)) = unify σ' σ
    unify (TypeAst () (TypeSub σ)) (TypeAst () (TypeSub σ')) | σ == σ' = pure ()
    unify σ@(TypeAst () (TypeSub (TypeVariable x))) σ' =
      indexKindEnvironment x >>= \case
        TypeBinding _ _ _ _ _ -> quit $ TypeMismatch p σ σ'
        LinkTypeBinding σ -> unify (flexible σ) σ'
    unify σ@(TypeAst () (TypeSub (TypeGlobalVariable x))) σ' =
      indexKindGlobalEnvironment x >>= \case
        TypeBinding _ _ _ _ _ -> quit $ TypeMismatch p σ σ'
        LinkTypeBinding σ -> unify (flexible σ) σ'
    unify σ σ'@(TypeAst () (TypeSub (TypeVariable _))) = unify σ' σ
    unify σ σ'@(TypeAst () (TypeSub (TypeGlobalVariable _))) = unify σ' σ
    unify (TypeAst () (Inline σ π τ)) (TypeAst () (Inline σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (TypeAst () (Poly ς)) (TypeAst () (Poly ς')) = unifyPoly ς ς'
    unify (TypeAst () (FunctionPointer σ π τ)) (TypeAst () (FunctionPointer σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (TypeAst () (FunctionLiteralType σ π τ)) (TypeAst () (FunctionLiteralType σ' π' τ')) = do
      unify σ σ'
      unify π π'
      unify τ τ'
    unify (TypeAst () (Tuple σs)) (TypeAst () (Tuple σs')) | length σs == length σs' = do
      sequence $ zipWith (unify) σs σs'
      pure ()
    unify (TypeAst () (Effect σ π)) (TypeAst () (Effect σ' π')) = do
      unify σ σ'
      unify π π'
    unify (TypeAst () (Unique σ)) (TypeAst () (Unique σ')) = do
      unify σ σ'
    unify (TypeAst () (Shared σ π)) (TypeAst () (Shared σ' π')) = do
      unify σ σ'
      unify π π'
    unify (TypeAst () (Pointer σ)) (TypeAst () (Pointer σ')) = do
      unify σ σ'
    unify (TypeAst () (Array σ)) (TypeAst () (Array σ')) = do
      unify σ σ'
    unify (TypeAst () (Number ρ1 ρ2)) (TypeAst () (Number ρ1' ρ2')) = do
      unify ρ1 ρ1'
      unify ρ2 ρ2'
    unify (TypeAst () Boolean) (TypeAst () Boolean) = pure ()
    unify (TypeAst () (Step σ τ)) (TypeAst () (Step σ' τ')) = do
      unify σ σ'
      unify τ τ'
    unify (TypeAst () Type) (TypeAst () Type) = pure ()
    unify (TypeAst () Region) (TypeAst () Region) = pure ()
    unify (TypeAst () (Pretype κ τ)) (TypeAst () (Pretype κ' τ')) = do
      unify κ κ'
      unify τ τ'
    unify (TypeAst () Boxed) (TypeAst () Boxed) = pure ()
    unify (TypeAst () Multiplicity) (TypeAst () Multiplicity) = pure ()
    unify (TypeAst () (KindRuntime PointerRep)) (TypeAst () (KindRuntime PointerRep)) = pure ()
    unify (TypeAst () (KindRuntime (StructRep κs))) (TypeAst () (KindRuntime (StructRep κs'))) | length κs == length κs' = do
      sequence_ $ zipWith (unify) κs κs'
    unify (TypeAst () (KindRuntime (UnionRep κs))) (TypeAst () (KindRuntime (UnionRep κs'))) | length κs == length κs' = do
      sequence_ $ zipWith (unify) κs κs'
    unify (TypeAst () (KindRuntime (WordRep κ))) (TypeAst () (KindRuntime (WordRep κ'))) = unify κ κ'
    unify (TypeAst () (KindSize Byte)) (TypeAst () (KindSize Byte)) = pure ()
    unify (TypeAst () (KindSize Short)) (TypeAst () (KindSize Short)) = pure ()
    unify (TypeAst () (KindSize Int)) (TypeAst () (KindSize Int)) = pure ()
    unify (TypeAst () (KindSize Long)) (TypeAst () (KindSize Long)) = pure ()
    unify (TypeAst () (KindSize Native)) (TypeAst () (KindSize Native)) = pure ()
    unify (TypeAst () (KindSignedness Signed)) (TypeAst () (KindSignedness Signed)) = pure ()
    unify (TypeAst () (KindSignedness Unsigned)) (TypeAst () (KindSignedness Unsigned)) = pure ()
    unify (TypeAst () Representation) (TypeAst () Representation) = pure ()
    unify (TypeAst () Size) (TypeAst () Size) = pure ()
    unify (TypeAst () Signedness) (TypeAst () Signedness) = pure ()
    unify (TypeAst () (Kind σ τ π)) (TypeAst () (Kind σ' τ' π')) = do
      unify σ σ'
      unify τ τ'
      unify π π'
    unify (TypeAst () Invariant) (TypeAst () Invariant) = pure ()
    unify (TypeAst () Subtypable) (TypeAst () Subtypable) = pure ()
    unify (TypeAst () Transparent) (TypeAst () Transparent) = pure ()
    unify (TypeAst () Opaque) (TypeAst () Opaque) = pure ()
    unify (TypeAst () Base) (TypeAst () Base) = pure ()
    unify (TypeAst () (Higher κ)) (TypeAst () (Higher κ')) = do
      unify κ κ'
    unify (TypeAst () Transparency) (TypeAst () Transparency) = pure ()
    unify (TypeAst () Orderability) (TypeAst () Orderability) = pure ()
    unify (TypeAst () Universe) (TypeAst () Universe) = pure ()
    unify (TypeAst () Top) (TypeAst () Top) = pure ()
    unify σ σ' = quit $ TypeMismatch p σ σ'

    unifyPoly
      (TypeScheme () (TypeForall (Bound (TypePattern () α κ π) ς)))
      (TypeScheme () (TypeForall (Bound (TypePattern () α' κ' π') ς')))
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
      (TypeScheme () (MonoType σ))
      (TypeScheme () (MonoType σ')) =
        unify σ σ'
    unifyPoly ς ς' = quit $ TypeMismatch p (TypeAst () $ Poly ς) (TypeAst () $ Poly ς')

reachLogical x (TypeAst () (TypeLogical x')) | x == x' = pure True
reachLogical x (TypeAst () (TypeLogical x')) =
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
plainType :: p -> Type () v -> Check p TypeSub
plainType p (TypeAst () (TypeSub σ@(TypeVariable x))) =
  indexKindEnvironment x >>= \case
    TypeBinding _ _ _ _ _ -> pure σ
    LinkTypeBinding σ -> plainType p σ
plainType _ (TypeAst () (TypeSub σ)) = pure σ
plainType p _ = quit $ ExpectedPlainType p

plainType' p σ@(TypeAst () (TypeLogical x)) =
  indexTypeLogicalMap x >>= \case
    LinkTypeLogical σ -> plainType' p σ
    _ -> pure σ
plainType' p σ = TypeAst () <$> TypeSub <$> plainType p σ

-- todo switch to greater then

-- comparing two types implies that they're kinds are the same
-- similiar to matchType
lessThen :: p -> TypeUnify -> TypeUnify -> Check p ()
lessThen p σ (TypeAst () (TypeLogical x)) = do
  σ <- plainType' p σ
  indexTypeLogicalMap x >>= \case
    (LinkTypeLogical σ') -> lessThen p σ σ'
    (UnboundTypeLogical p' κ lower upper lev) ->
      reachLogical x σ >>= \case
        True -> matchType p (TypeAst () (TypeLogical x)) σ
        False -> do
          -- todo occurance here maybe?
          modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundTypeLogical p' κ (σ : lower) upper lev) $ typeLogicalMap state}
          for upper $ \π -> lessThen p σ (TypeAst () $ TypeSub $ π)
          pure ()
lessThen p (TypeAst () (TypeLogical x)) σ' = do
  σ' <- plainType p σ'
  indexTypeLogicalMap x >>= \case
    (LinkTypeLogical σ) -> lessThen p σ (TypeAst () $ TypeSub σ')
    (UnboundTypeLogical p' κ lower upper lev) -> do
      bound <- case upper of
        Nothing -> pure σ'
        Just σ'' -> meet p σ' σ''
      modifyState $ \state -> state {typeLogicalMap = Map.insert x (UnboundTypeLogical p' κ lower (Just bound) lev) $ typeLogicalMap state}
      for lower $ \σ -> lessThen p σ (TypeAst () $ TypeSub σ')
      pure ()
lessThen p σ σ' = do
  σ <- plainType p σ
  σ' <- plainType p σ'
  lower <- lowerTypeBounds σ'
  if σ `Set.notMember` lower
    then quit $ TypeMisrelation p σ σ'
    else pure ()

kindIsMember :: forall p. p -> TypeUnify -> TypeUnify -> Check p ()
kindIsMember p (TypeAst () Top) _ = quit $ NotTypable p
kindIsMember p σ κ = do
  κ' <- reconstruct p σ
  matchType p κ κ'

reconstruct :: forall p. p -> TypeUnify -> Check p TypeUnify
reconstruct p = reconstructF indexEnvironment indexGlobalEnvironment indexLogicalMap poly representation multiplicities
  where
    poly (TypeScheme () (TypeForall _)) = pure $ TypeAst () $ Type
    poly (TypeScheme () (MonoType σ)) = reconstruct p σ

    indexEnvironment x = indexKindEnvironment x >>= kind
      where
        kind (TypeBinding _ κ _ _ _) = pure $ κ
        kind (LinkTypeBinding σ) = reconstruct p (flexible σ)
    indexGlobalEnvironment x = indexKindGlobalEnvironment x >>= kind
      where
        kind (TypeBinding _ κ _ _ _) = pure $ κ
        kind (LinkTypeBinding σ) = reconstruct p (flexible σ)
    indexLogicalMap x = indexTypeLogicalMap x >>= index
    index (UnboundTypeLogical _ x _ _ _) = pure x
    index (LinkTypeLogical σ) = reconstruct p σ
    representation σ = do
      κ <- reconstruct p σ
      (α, _) <- checkPretype p κ
      pure α
    multiplicities σs = do
      π <- freshMultiplicityKindVariable p
      for σs $ \σ -> do
        κ <- reconstruct p σ
        (_, π') <- checkPretype p κ
        lessThen p π π'
      pure π

freshTypeVariable p κ = (TypeAst () . TypeLogical) <$> (Level <$> levelCounter <$> getState >>= freshTypeVariableRaw p κ [] Nothing)

freshRepresentationKindVariable p = freshTypeVariable p (TypeAst () Representation)

freshSizeKindVariable p = freshTypeVariable p (TypeAst () Size)

freshSignednessKindVariable p = freshTypeVariable p (TypeAst () Signedness)

freshOrderabilityVariable p = freshTypeVariable p (TypeAst () Orderability)

freshTransparencyVariable p = freshTypeVariable p (TypeAst () Transparency)

freshUniverseVariable p = freshTypeVariable p (TypeAst () Universe)

freshMetaTypeVariable p = do
  freshTypeVariable p (TypeAst () Type)

freshMultiplicityKindVariable p = do
  freshTypeVariable p (TypeAst () Multiplicity)

freshPretypeTypeVariable p = do
  s <- freshRepresentationKindVariable p
  τ <- freshMultiplicityKindVariable p
  freshTypeVariable p (TypeAst () $ Pretype s τ)

freshBoxedTypeVariable p = do
  freshTypeVariable p (TypeAst () Boxed)

freshRegionTypeVariable p = do
  freshTypeVariable p $ TypeAst () $ Region

checkKind p σt = do
  μ <- freshOrderabilityVariable p
  κ <- freshTransparencyVariable p
  ρ <- freshUniverseVariable p
  matchType p σt (TypeAst () (Kind μ κ ρ))
  pure (μ, κ, ρ)

checkRepresentation p σt = do
  matchType p σt (TypeAst () Representation)
  pure ()

checkMultiplicity p σt = do
  matchType p σt (TypeAst () Multiplicity)
  pure ()

checkSize p σt = do
  matchType p σt (TypeAst () Size)
  pure ()

checkSignedness p σt = do
  matchType p σt (TypeAst () Signedness)
  pure ()

checkType p σt = do
  matchType p σt (TypeAst () Type)
  pure ()

checkPretype p σ = do
  κ <- freshRepresentationKindVariable p
  τ <- freshMultiplicityKindVariable p
  matchType p σ (TypeAst () $ Pretype κ τ)
  pure (κ, τ)

checkBoxed p σt = do
  matchType p σt (TypeAst () Boxed)
  pure ()

checkRegion p σt = do
  matchType p σt (TypeAst () Region)
  pure ()

checkSubtypable p σt = do
  matchType p σt (TypeAst () Subtypable)
  pure ()

checkOrderability p σt = do
  matchType p σt (TypeAst () Orderability)
  pure ()

checkTransparency p σt = do
  matchType p σt (TypeAst () Transparency)
  pure ()

checkUniverse p σt = do
  matchType p σt (TypeAst () Universe)
  pure ()

checkInline p σt = do
  σ <- freshMetaTypeVariable p
  π <- freshMultiplicityKindVariable p
  τ <- freshMetaTypeVariable p
  matchType p σt (TypeAst () (Inline σ π τ))
  pure (σ, π, τ)

checkFunctionPointer p σt = do
  σ <- freshPretypeTypeVariable p
  π <- freshRegionTypeVariable p
  τ <- freshPretypeTypeVariable p
  matchType p σt (TypeAst () $ FunctionPointer σ π τ)
  pure (σ, π, τ)

checkFunctionLiteralType p σt = do
  σ <- freshPretypeTypeVariable p
  π <- freshRegionTypeVariable p
  τ <- freshPretypeTypeVariable p
  matchType p σt (TypeAst () $ FunctionLiteralType σ π τ)
  pure (σ, π, τ)

checkUnique p σt = do
  σ <- freshBoxedTypeVariable p
  matchType p σt (TypeAst () $ Unique σ)
  pure σ

checkPointer p σt = do
  σ <- freshPretypeTypeVariable p
  matchType p σt (TypeAst () $ Pointer σ)
  pure (σ)

checkArray p σt = do
  σ <- freshPretypeTypeVariable p
  matchType p σt (TypeAst () $ Array σ)
  pure (σ)

checkEffect p σt = do
  σ <- freshPretypeTypeVariable p
  π <- freshRegionTypeVariable p
  matchType p σt (TypeAst () $ Effect σ π)
  pure (σ, π)

checkShared p σt = do
  σ <- freshBoxedTypeVariable p
  π <- freshRegionTypeVariable p
  matchType p σt (TypeAst () $ Shared σ π)
  pure (σ, π)

checkNumber p σt = do
  ρ1 <- freshSignednessKindVariable p
  ρ2 <- freshSizeKindVariable p
  matchType p σt (TypeAst () $ Number ρ1 ρ2)
  pure (ρ1, ρ2)

checkBoolean p σt = do
  matchType p σt (TypeAst () $ Boolean)

checkStep p σt = do
  σ <- freshPretypeTypeVariable p
  τ <- freshPretypeTypeVariable p
  matchType p σt (TypeAst () $ Step σ τ)
  pure (σ, τ)
