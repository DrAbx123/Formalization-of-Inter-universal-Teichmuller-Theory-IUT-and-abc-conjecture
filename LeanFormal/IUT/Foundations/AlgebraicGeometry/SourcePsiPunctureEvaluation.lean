import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiEvaluationActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiEvaluationObstruction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralUnitMapSurjectivity
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

/-!
# Puncture evaluation

From the actual puncture of the source punctured elliptic curve, base change to
the completion, and construct an actual integral point/evaluation when the
puncture is affine with integral coordinates.  If the puncture is the point at
infinity or lacks integral coordinates, the obstruction is stated exactly.
No point or evaluation is fabricated.
-/

namespace LeanFormal.IUT.SourcePsiPunctureEvaluation

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelUnitMapExistence
open LeanFormal.IUT.SourcePsiEvaluationObstruction
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))
  (h : SourcePsiCoefficientsIntegral S v)

/-- The source punctured elliptic curve. -/
abbrev SourcePunctureCurve : PuncturedEllipticCurve S.arithmetic.F :=
  S.arithmetic.curve

/-- Its actual base change to the completion field. -/
noncomputable abbrev SourcePunctureBaseChange :
    PuncturedEllipticCurve (SourcePsiCompletionField S v) :=
  SourcePunctureCurve S |>.baseChange (SourcePsiCompletionField S v)

/-- The actual puncture after base change. -/
noncomputable def sourcePuncturePoint :
    (SourcePunctureBaseChange S v).curve.toProjective.Point :=
  (SourcePunctureBaseChange S v).puncture

/-- The actual affine lift of the base-changed puncture. -/
noncomputable def sourcePunctureAffineLift :
    (SourcePunctureBaseChange S v).curve.toAffine.Point :=
  (sourcePuncturePoint S v).toAffineLift

/-- Exact affine/integral puncture data: the puncture is affine with both
coordinates in the adic completion integers. -/
structure SourcePsiPunctureAffineIntegralData where
  x : SourcePsiCompletionIntegers S v
  y : SourcePsiCompletionIntegers S v
  nonsingular : (SourcePunctureBaseChange S v).curve.toAffine.Nonsingular
    (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) x)
    (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) y)
  affine_eq : sourcePunctureAffineLift S v =
    .some (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) x)
      (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) y)
      nonsingular

/-- An affine/integral puncture gives an actual integral point of the raw
coefficient model. -/
noncomputable def sourcePsiIntegralPointOfPuncture
    (D : SourcePsiPunctureAffineIntegralData S v) :
    SourcePsiIntegralPoint S v h where
  x := D.x
  y := D.y
  equation := by
    have hcurve : (sourcePsiIntegralModelOfIntegralCoefficients S v h).curve =
        S.arithmetic.curve.curve.baseChange (SourcePsiCompletionField S v) := by
      simpa [sourcePsiIntegralModelOfIntegralCoefficients,
        sourcePsiIntegralModelDataOfCoefficients, SourcePsiBaseChangedCurve] using
        sourcePsiIntegralModelOfCoefficients_baseChange S v h
    have heq := D.nonsingular.1
    simpa [hcurve, SourcePunctureBaseChange, SourcePunctureCurve,
      PuncturedEllipticCurve.baseChange, WeierstrassCurve.baseChange] using heq

/-- An affine/integral puncture gives the actual evaluation/retraction datum. -/
noncomputable def sourcePsiEvaluationDataOfPuncture
    (D : SourcePsiPunctureAffineIntegralData S v) :
    SourcePsiIntegralEvaluationData S v h :=
  sourcePsiIntegralEvaluationDataOfPoint S v h
    (sourcePsiIntegralPointOfPuncture S v h D)

/-- The induced unit map is surjective. -/
theorem sourcePsiPunctureUnitMap_surjective
    (D : SourcePsiPunctureAffineIntegralData S v) :
    Function.Surjective (SourcePsiIntegralUnitMap S v h
      (sourcePsiEvaluationDataOfPuncture S v h D)) :=
  SourcePsiIntegralUnitMap_surjective S v h
    (sourcePsiEvaluationDataOfPuncture S v h D)

/-- Exact obstruction `at infinity`: the affine lift of the puncture is the zero
point. -/
def SourcePsiPunctureAtInfinity : Prop :=
  sourcePunctureAffineLift S v = 0

theorem not_punctureAffineIntegralData_of_atInfinity
    (hinf : SourcePsiPunctureAtInfinity S v) :
    ¬ Nonempty (SourcePsiPunctureAffineIntegralData S v) := by
  rintro ⟨D⟩
  have hsome : sourcePunctureAffineLift S v =
      .some (algebraMap (SourcePsiCompletionIntegers S v)
        (SourcePsiCompletionField S v) D.x)
        (algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiCompletionField S v) D.y) D.nonsingular :=
    D.affine_eq
  rw [hinf] at hsome
  exact Option.noConfusion hsome

/-- Exact obstruction `nonintegral`: every affine representative of the
puncture has at least one coordinate with no integral representative. -/
def SourcePsiPunctureNonintegral : Prop :=
  ∀ x y : SourcePsiCompletionField S v,
    (∃ ns : (SourcePunctureBaseChange S).curve.toAffine.Nonsingular x y,
      sourcePunctureAffineLift S = .some x y ns) →
      (¬ ∃ x₀ : SourcePsiCompletionIntegers S v,
        algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiCompletionField S v) x₀ = x) ∨
      (¬ ∃ y₀ : SourcePsiCompletionIntegers S v,
        algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiCompletionField S v) y₀ = y)

theorem not_punctureAffineIntegralData_of_nonintegral
    (hni : SourcePsiPunctureNonintegral S v) :
    ¬ Nonempty (SourcePsiPunctureAffineIntegralData S v) := by
  rintro ⟨D⟩
  obtain ⟨ns, hsome⟩ := D.affine_eq
  have hbad := hni _ _ ⟨ns, hsome⟩
  rcases hbad with hx | hy
  · exact hx ⟨D.x, rfl⟩
  · exact hy ⟨D.y, rfl⟩
/-- Exact residual: an affine/integral puncture datum. -/
def SourcePsiPunctureAffineIntegralResidual : Prop :=
  Nonempty (SourcePsiPunctureAffineIntegralData S v)

theorem sourcePsiPunctureAffineIntegralResidual_iff :
    SourcePsiPunctureAffineIntegralResidual S v ↔
      Nonempty (SourcePsiPunctureAffineIntegralData S v) :=
  Iff.rfl

/-- Conditional evaluation from an actual affine/integral puncture. -/
theorem sourcePsiPuncture_evaluation_conditional
    (hD : SourcePsiPunctureAffineIntegralResidual S v) :
    Nonempty (SourcePsiIntegralEvaluationData S v h) := by
  rcases hD with ⟨D⟩
  exact ⟨sourcePsiEvaluationDataOfPuncture S v h D⟩

end LeanFormal.IUT.SourcePsiPunctureEvaluation
end