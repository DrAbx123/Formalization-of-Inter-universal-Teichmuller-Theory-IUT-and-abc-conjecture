import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve

/-!
# ShehddPuncturedCurveConsumerActual — punctured elliptic curve map/baseChange consumer

STEP 0 prior-art (reuse only; A475 search: punctured curve carrier found):
* Foundations/Geometry/PuncturedEllipticCurve.lean: PuncturedEllipticCurve (curve,
  isElliptic, puncture), jInvariant + jInvariant_spec, projectivePointClassMap,
  projectiveNonsingularLift_map, projectivePointMap, map + map_curve/map_puncture,
  baseChange + baseChange_curve.

This file packages the map/base-change compatibility as one consumer for the Frey/Tate
curve carriers.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddPuncturedCurveConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.PuncturedEllipticCurve

universe u v

variable {F : Type u} [Field F]

/-- **PROVED consumer:** the j-invariant is the curve's j-invariant. -/
theorem punctured_curve_jInvariant_consumer (X : PuncturedEllipticCurve F) :
    X.jInvariant = X.curve.j :=
  PuncturedEllipticCurve.jInvariant_spec

/-- **PROVED consumer:** mapping along a field homomorphism acts on the curve and the
puncture as expected. -/
theorem punctured_curve_map_consumer {K : Type v} [Field K]
    (X : PuncturedEllipticCurve F) (f : F →+* K) :
    (X.map f).curve = X.curve.map f ∧
      (X.map f).puncture =
        PuncturedEllipticCurve.projectivePointMap f X.curve X.puncture :=
  ⟨PuncturedEllipticCurve.map_curve X f,
    PuncturedEllipticCurve.map_puncture X f⟩

/-- **PROVED consumer:** base change is the map along the algebra map and acts on the
underlying curve by Mathlib base change. -/
theorem punctured_curve_baseChange_consumer (X : PuncturedEllipticCurve F)
    (K : Type v) [Field K] [Algebra F K] :
    (X.baseChange K).curve = X.curve.baseChange K :=
  PuncturedEllipticCurve.baseChange_curve X K

/-- Row record: reused punctured-carrier assets vs the consumer interface. -/
def puncturedCurveRows : List (String × String × String) :=
  [ ("carrier (curve, ellipticity, puncture) + j", "REUSED DEF/PROVED", "PuncturedEllipticCurve / jInvariant / jInvariant_spec")
  , ("projective point class/nonsingular maps", "REUSED DEF/PROVED", "projectivePointClassMap / projectiveNonsingularLift_map / projectivePointMap")
  , ("map laws", "REUSED PROVED", "map_curve / map_puncture")
  , ("base change law", "REUSED PROVED", "baseChange / baseChange_curve")
  , ("consumer bundles", "COMPOSED PROVED", "punctured_curve_jInvariant_consumer, punctured_curve_map_consumer, punctured_curve_baseChange_consumer") ]

theorem puncturedCurveRows_length : puncturedCurveRows.length = 5 := rfl

#check punctured_curve_jInvariant_consumer
#check punctured_curve_map_consumer
#check punctured_curve_baseChange_consumer
#check puncturedCurveRows_length

end LeanFormal.IUT.XiFPaper.ShehddPuncturedCurveConsumerActual
end
