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

instance (EmbedUnrestricted l, AugmentLinear m pm l lΓ) => AugmentLinearImpl m p (PatternOfCourse pm) l lΓ where
  augmentLinearImpl _ (PatternOfCourse pm) _ e = augmentLinear pm (unrestricted @l) e

instance (FreeVariables u p pm) => FreeVariablesImpl u p (PatternOfCourse pm) where
  freeVariablesImpl _ (PatternOfCourse pm) = freeVariables @u pm

instance Bindings pm => Bindings (PatternOfCourse pm) where
  bindings (PatternOfCourse pm) = bindings pm

instance (EmbedPatternOfCourse pm, Substitute u pm) => SubstituteImpl (PatternOfCourse pm) u pm where
  substituteImpl ux x (PatternOfCourse pm) = patternOfCourse (substitute ux x pm)

instance (EmbedPatternOfCourse pm, ConvertPattern pm pm) => ConvertPattern pm (PatternOfCourse pm) where
  convertPattern ix x (PatternOfCourse pm) = patternOfCourse (convertPattern ix x pm)

instance (EmbedPatternOfCourse pm, Reduce pm) => ReduceImpl (PatternOfCourse pm) pm where
  reduceImpl (PatternOfCourse pm) = patternOfCourse (reduce pm)

instance
  ( EmbedBind pm e,
    EmbedPatternOfCourse pm,
    MatchOfCourseIntroduction e,
    ReducePattern pm e e
  ) =>
  ReducePattern (PatternOfCourse pm) e e
  where
  reducePattern (PatternOfCourse pm) e1 e2 = case matchOfCourseIntroduction e1 of
    Just (OfCourseIntroduction e) -> reducePattern pm e e2
    Nothing -> bind (patternOfCourse pm) e1 e2
