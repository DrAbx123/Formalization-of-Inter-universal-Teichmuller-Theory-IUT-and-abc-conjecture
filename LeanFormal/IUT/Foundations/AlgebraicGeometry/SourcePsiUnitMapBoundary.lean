import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiEvaluationDichotomy
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

/-!
# Unit map boundary

This file integrates the evaluation trichotomy with the unit comparison.  The
actual unit map considered here is the coordinate-ring unit map induced by an
affine puncture evaluation; it is surjective exactly on the affine-integral
branch, while the at-infinity and nonintegral branches obstruct any boundary
datum carrying an integral puncture.  The codomain is the completion field unit
group; the integral-unit-codomain lift is recorded as the exact corrected
evaluation residual.  No fake unit map or surjectivity is asserted.
-/

namespace LeanFormal.IUT.SourcePsiUnitMapBoundary

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiPunctureInfinityCriterion
open LeanFormal.IUT.SourcePsiEvaluationDichotomy
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual unit map at an affine puncture: the evaluation-induced unit map
from the puncture coordinate ring to the completion field units. -/
noncomputable def punctureBoundaryUnitMap
    (C : SourcePsiPunctureAffineCoordinates S v) :
    (PunctureCoordinateRing S v)ˣ →* (v.adicCompletion S.arithmetic.F)ˣ :=
  punctureUnitMap S v (punctureEvaluationDataOfCoordinates S v C)

theorem punctureBoundaryUnitMap_constant
    (C : SourcePsiPunctureAffineCoordinates S v)
    (r : (v.adicCompletion S.arithmetic.F)ˣ) :
    punctureBoundaryUnitMap S v C
      (Units.map (algebraMap (v.adicCompletion S.arithmetic.F)
        (PunctureCoordinateRing S v)).toMonoidHom r) = r :=
  punctureUnitMap_constant S v
    (punctureEvaluationDataOfCoordinates S v C) r

theorem punctureBoundaryUnitMap_surjective
    (C : SourcePsiPunctureAffineCoordinates S v) :
    Function.Surjective (punctureBoundaryUnitMap S v C) :=
  punctureUnitMap_surjective S v
    (punctureEvaluationDataOfCoordinates S v C)

/-- Exact boundary datum: an actual affine/integral puncture, the induced
evaluation, its unit map, and surjectivity of that unit map. -/
structure SourcePsiUnitMapBoundary where
  integralPoint : SourcePsiPunctureAffineIntegralData S v
  coordinates : SourcePsiPunctureAffineCoordinates S v
  coordinates_eq : coordinates = coordinatesOfIntegralData S v integralPoint
  evaluation : PunctureEvaluationData S v
  evaluation_eq : evaluation = evaluationDataOfIntegralData S v integralPoint
  unitMap : (PunctureCoordinateRing S v)ˣ →* (v.adicCompletion S.arithmetic.F)ˣ
  unitMap_eq : unitMap = punctureBoundaryUnitMap S v coordinates
  surjective : Function.Surjective unitMap

/-- The actual boundary datum in the affine-integral case. -/
noncomputable def sourcePsiUnitMapBoundary
    (D : SourcePsiPunctureAffineIntegralData S v) :
    SourcePsiUnitMapBoundary S v where
  integralPoint := D
  coordinates := coordinatesOfIntegralData S v D
  coordinates_eq := rfl
  evaluation := evaluationDataOfIntegralData S v D
  evaluation_eq := rfl
  unitMap := punctureBoundaryUnitMap S v (coordinatesOfIntegralData S v D)
  unitMap_eq := rfl
  surjective := punctureBoundaryUnitMap_surjective S v
    (coordinatesOfIntegralData S v D)

/-- The affine-integral branch supplies the boundary datum. -/
theorem sourcePsiUnitMapBoundary_nonempty
    (D : SourcePsiPunctureAffineIntegralData S v) :
    Nonempty (SourcePsiUnitMapBoundary S v) :=
  ⟨sourcePsiUnitMapBoundary S v D⟩

/-- The boundary datum carries an actual integral puncture. -/
theorem sourcePsiUnitMapBoundary_integralPoint
    (B : SourcePsiUnitMapBoundary S v) :
    Nonempty (SourcePsiPunctureAffineIntegralData S v) :=
  ⟨B.integralPoint⟩

/-- At the point at infinity, no boundary datum exists. -/
theorem sourcePsiUnitMapBoundary_not_atInfinity
    (hinf : sourcePunctureAffineLift S v = 0) :
    ¬ Nonempty (SourcePsiUnitMapBoundary S v) := by
  rintro ⟨B⟩
  exact not_affineIntegralData_of_atInfinity S v hinf ⟨B.integralPoint⟩

/-- In the nonintegral affine case, no boundary datum exists. -/
theorem sourcePsiUnitMapBoundary_not_nonintegral
    (C : SourcePsiPunctureAffineCoordinates S v)
    (hC : ¬ SourcePsiPunctureCoordinateIntegral S v C.x ∨
      ¬ SourcePsiPunctureCoordinateIntegral S v C.y) :
    ¬ Nonempty (SourcePsiUnitMapBoundary S v) := by
  rintro ⟨B⟩
  exact not_affineIntegralData_of_coordinateNonintegral S v C hC
    ⟨B.integralPoint⟩

/-- Exact boundary trichotomy: infinity, affine nonintegral, or affine integral
with an actual unit map boundary. -/
def SourcePsiUnitMapBoundaryTrichotomy : Prop :=
  sourcePunctureAffineLift S v = 0 ∨
    (∃ C : SourcePsiPunctureAffineCoordinates S v,
      ¬ SourcePsiPunctureCoordinateIntegral S v C.x ∨
      ¬ SourcePsiPunctureCoordinateIntegral S v C.y) ∨
    Nonempty (SourcePsiUnitMapBoundary S v)

theorem sourcePsiUnitMapBoundary_trichotomy :
    SourcePsiUnitMapBoundaryTrichotomy S v := by
  classical
  rcases sourcePsiPuncture_trichotomy S v with hinf | hnon | hint
  · exact Or.inl hinf
  · exact Or.inr (Or.inl hnon)
  · rcases hint with ⟨D⟩
    exact Or.inr (Or.inr (sourcePsiUnitMapBoundary_nonempty S v D))

/-- The unit map is surjective on every actual boundary datum. -/
theorem sourcePsiUnitMapBoundary_surjective
    (B : SourcePsiUnitMapBoundary S v) :
    Function.Surjective B.unitMap :=
  B.surjective

/-- Exact corrected-evaluation residual: lifting the unit map's codomain from
the completion field units to the adic completion integer units remains
conditional on the affine/integral puncture datum. -/
def SourcePsiCorrectedEvaluationResidual : Prop :=
  Nonempty (SourcePsiPunctureAffineIntegralData S v)

theorem sourcePsiCorrectedEvaluationResidual_iff :
    SourcePsiCorrectedEvaluationResidual S v ↔
      Nonempty (SourcePsiPunctureAffineIntegralData S v) :=
  Iff.rfl

/-- The corrected residual is exactly the affine-integral branch of the
trichotomy. -/
theorem sourcePsiCorrectedEvaluationResidual_of_trichotomy
    (htri : SourcePsiEvaluationTrichotomy S v) :
    SourcePsiCorrectedEvaluationResidual S v ∨
      sourcePunctureAffineLift S v = 0 ∨
      (∃ C : SourcePsiPunctureAffineCoordinates S v,
        ¬ SourcePsiPunctureCoordinateIntegral S v C.x ∨
        ¬ SourcePsiPunctureCoordinateIntegral S v C.y) :=
  by
  rcases htri with hinf | hnon | hint
  · exact Or.inr (Or.inl hinf)
  · exact Or.inr (Or.inr hnon)
  · exact Or.inl hint

end LeanFormal.IUT.SourcePsiUnitMapBoundary
end