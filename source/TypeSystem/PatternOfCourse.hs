module TypeSystem.PatternOfCourse where

import TypeSystem.Bind
import TypeSystem.Methods
import TypeSystem.OfCourse
import TypeSystem.OfCourseIntroduction
import TypeSystem.Unrestricted

data PatternOfCourse pm = PatternOfCourse pm

class EmbedPatternOfCourse pm where
  patternOfCourse :: pm -> pm

instance (TypeCheck pms m pm) => TypeCheckImpl m p (PatternOfCourse pm) pms where
  typeCheckImpl _ (PatternOfCourse pm) = typeCheck pm

instance (EmbedOfCourse σ, InternalType pm σ) => InternalType (PatternOfCourse pm) σ where
  internalType (PatternOfCourse pm) = ofCourse $ internalType pm

instance (EmbedUnrestricted l, AugmentEnvironmentPatternLinear m pm l lΓ) => AugmentEnvironmentPatternLinearImpl m p (PatternOfCourse pm) l lΓ where
  augmentEnvironmentPatternLinearImpl _ (PatternOfCourse pm) _ e = augmentEnvironmentPatternLinear pm (unrestricted @l) e

instance (FreeVariables pm u) => FreeVariables (PatternOfCourse pm) u where
  freeVariables' (PatternOfCourse pm) = freeVariables @u pm

instance (pm' ~ pm, EmbedPatternOfCourse pm, Substitute u pm) => SubstituteImpl (PatternOfCourse pm') u pm where
  substituteImpl ux x (PatternOfCourse pm) = patternOfCourse (substitute ux x pm)

instance RemoveBindings pm => RemoveBindings (PatternOfCourse pm) where
  removeBindings (PatternOfCourse pm) = removeBindings pm

instance (pm ~ pm', EmbedPatternOfCourse pm, AvoidCapturePattern u pm e) => AvoidCapturePatternImpl (PatternOfCourse pm) u pm' e where
  avoidCapturePatternImpl u (PatternOfCourse pm, e) = (patternOfCourse pm', e')
    where
      (pm', e') = avoidCapturePattern u (pm, e)

instance (pm ~ pm', EmbedPatternOfCourse pm, Reduce pm) => ReduceImpl (PatternOfCourse pm') pm where
  reduceImpl (PatternOfCourse pm) = patternOfCourse (reduce pm)

instance
  ( EmbedBind pm e,
    EmbedPatternOfCourse pm,
    MatchOfCourseIntroduction e,
    ReducePattern pm e
  ) =>
  ReducePattern (PatternOfCourse pm) e
  where
  reducePattern (PatternOfCourse pm) e1 e2 = case matchOfCourseIntroduction e1 of
    Just (OfCourseIntroduction e) -> reducePattern pm e e2
    Nothing -> bind (patternOfCourse pm) e1 e2
