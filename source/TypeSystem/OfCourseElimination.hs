module TypeSystem.OfCourseElimination where

import qualified Data.Set as Set
import Data.Type.Equality ((:~:) (..))
import Environment
import Misc.Identifier
import Misc.Util (Same, firstM, same)
import TypeSystem.Methods
import TypeSystem.OfCourse
import TypeSystem.OfCourseIntroduction
import TypeSystem.Unrestricted
import TypeSystem.Variable

data OfCourseElimination l e = OfCourseElimination Identifier e e deriving (Show, Functor, Foldable, Traversable)

class EmbedOfCourseElimination e where
  ofCourseElimination :: Identifier -> e -> e -> e

instance
  ( Monad m,
    CheckOfCourse m p σ,
    EmbedUnrestricted l,
    Usage lΓ,
    Positioned e p,
    AugmentEnvironmentLinear m p l σ lΓ,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (OfCourseElimination l e) σ lΓ
  where
  typeCheckLinearImpl p (OfCourseElimination x e1 e2) = do
    (OfCourse τ, lΓ1) <- firstM (checkOfCourse $ location e1) =<< typeCheckLinear e1
    (σ, lΓ2) <- augmentEnvironmentLinear p x (unrestricted @l) τ (typeCheckLinear e2)
    pure (σ, combine lΓ1 lΓ2)

instance
  ( Same u e,
    FreeVariables e u
  ) =>
  FreeVariables (OfCourseElimination l e) u
  where
  freeVariables' (OfCourseElimination x e1 e2) = case same @u @e of
    Just Refl -> freeVariables @u e1 <> Set.delete x (freeVariables @u e2)
    Nothing -> freeVariables @u e1 <> freeVariables @u e2

instance
  ( e ~ e',
    EmbedOfCourseElimination e,
    EmbedVariable e,
    FreeVariables u e,
    Substitute u e,
    Substitute e e'
  ) =>
  SubstituteImpl (OfCourseElimination l e) u e'
  where
  substituteImpl ux x1 (OfCourseElimination x2 e1 e2) = ofCourseElimination (x2') (substitute ux x1 e1) (substitute ux x1 e2')
    where
      (x2', e2') = avoidCapture @e (freeVariables @e ux) (x2, e2)

instance
  ( e ~ e',
    EmbedOfCourseElimination e,
    MatchOfCourseIntroduction e,
    Substitute e e',
    Reduce e
  ) =>
  ReduceImpl (OfCourseElimination l e) e'
  where
  reduceImpl (OfCourseElimination x e1 e2) = case matchOfCourseIntroduction (reduce e1) of
    Just (OfCourseIntroduction e) -> reduce (substitute e x (reduce e2))
    Nothing -> ofCourseElimination x (reduce e1) (reduce e2)
