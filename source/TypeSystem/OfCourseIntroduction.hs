module TypeSystem.OfCourseIntroduction where

import TypeSystem.Methods
import TypeSystem.OfCourse
import TypeSystem.Unrestricted

data OfCourseIntroduction l e = OfCourseIntroduction e deriving (Show, Functor, Foldable, Traversable)

class EmbedOfCourseIntroduction e where
  ofCourseIntroduction :: e -> e

class MatchOfCourseIntroduction e where
  matchOfCourseIntroduction :: e -> Maybe (OfCourseIntroduction l e)

instance
  ( Monad m,
    EmbedOfCourse σ,
    EmbedUnrestricted l,
    Capture m p l lΓ,
    TypeCheckLinear σ m e lΓ
  ) =>
  TypeCheckLinearImpl m p (OfCourseIntroduction l e) σ lΓ
  where
  typeCheckLinearImpl p (OfCourseIntroduction e) = do
    (σ, lΓ) <- typeCheckLinear e
    capture p (unrestricted @l) lΓ
    pure (ofCourse σ, lΓ)

instance FreeVariables e u => FreeVariables (OfCourseIntroduction l e) u where
  freeVariables' (OfCourseIntroduction e) = freeVariables @u e

instance (e ~ e', EmbedOfCourseIntroduction e, Substitute u e) => SubstituteImpl (OfCourseIntroduction l e) u e' where
  substituteImpl ux x (OfCourseIntroduction e) = ofCourseIntroduction (substitute ux x e)

instance (e ~ e', EmbedOfCourseIntroduction e, Reduce e) => ReduceImpl (OfCourseIntroduction l e) e' where
  reduceImpl (OfCourseIntroduction e) = ofCourseIntroduction $ reduce e
