import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiPunctureEvaluation
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

/-!
# Torsion point evaluation

The Definition 3.1 source contract supplies an abstract torsion carrier with a
Galois representation, not an actual map from that carrier to projective points
of the base-changed curve.  This file records that exact map as missing data,
and constructs an actual affine/integral point and evaluation only when such a
selection is supplied with affine integral coordinates.  No point is fabricated.
-/

namespace LeanFormal.IUT.SourcePsiTorsionPointEvaluation

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiEvaluationObstruction
open LeanFormal.IUT.SourcePsiIntegralUnitMapSurjectivity
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))
  (h : SourcePsiCoefficientsIntegral S v)

/-- The abstract torsion carrier of Definition 3.1. -/
abbrev SourceTorsionCarrier : Type u :=
  S.torsion.torsionCarrier

/-- The source punctured curve base-changed to the completion field. -/
noncomputable abbrev SourceTorsionBaseCurve :
    PuncturedEllipticCurve (SourcePsiCompletionField S v) :=
  S.arithmetic.curve.baseChange (SourcePsiCompletionField S v)

/-- The exact missing selection: an actual map from the abstract torsion
carrier to projective points of the base-changed curve, satisfying the
six-torsion law. -/
structure SourcePsiTorsionPointSelection where
  point : SourceTorsionCarrier S →
    (SourceTorsionBaseCurve S v).curve.toProjective.Point
  six_torsion : ∀ g : SourceTorsionCarrier S,
    (6 : Nat) • point g = 0

/-- A selected torsion point that is affine and integral. -/
structure SourcePsiTorsionAffineIntegralPoint
    (T : SourcePsiTorsionPointSelection S v) where
  g : SourceTorsionCarrier S
  x : SourcePsiCompletionIntegers S v
  y : SourcePsiCompletionIntegers S v
  nonsingular : (SourceTorsionBaseCurve S v).curve.toAffine.Nonsingular
    (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) x)
    (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) y)
  affine_eq : (T.point g).toAffineLift =
    .some (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) x)
      (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) y)
      nonsingular

/-- An affine/integral selected torsion point gives an actual integral point of
the raw coefficient model. -/
noncomputable def sourcePsiIntegralPointOfTorsion
    {T : SourcePsiTorsionPointSelection S v}
    (D : SourcePsiTorsionAffineIntegralPoint S v T) :
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
    simpa [hcurve, SourceTorsionBaseCurve, PuncturedEllipticCurve.baseChange,
      WeierstrassCurve.baseChange] using heq

/-- An affine/integral torsion point gives the actual evaluation/retraction. -/
noncomputable def sourcePsiEvaluationDataOfTorsion
    {T : SourcePsiTorsionPointSelection S v}
    (D : SourcePsiTorsionAffineIntegralPoint S v T) :
    SourcePsiIntegralEvaluationData S v h :=
  sourcePsiIntegralEvaluationDataOfPoint S v h
    (sourcePsiIntegralPointOfTorsion S v h D)

theorem sourcePsiTorsionUnitMap_surjective
    {T : SourcePsiTorsionPointSelection S v}
    (D : SourcePsiTorsionAffineIntegralPoint S v T) :
    Function.Surjective (SourcePsiIntegralUnitMap S v h
      (sourcePsiEvaluationDataOfTorsion S v h D)) :=
  SourcePsiIntegralUnitMap_surjective S v h
    (sourcePsiEvaluationDataOfTorsion S v h D)

/-- Exact obstruction: a selected torsion point is the point at infinity. -/
def SourcePsiTorsionAtInfinity (T : SourcePsiTorsionPointSelection S v) : Prop :=
  ∃ g : SourceTorsionCarrier S, (T.point g).toAffineLift = 0

theorem not_torsionAffineIntegralPoint_of_atInfinity
    {T : SourcePsiTorsionPointSelection S v}
    (hinf : SourcePsiTorsionAtInfinity S v T) :
    ¬ Nonempty (SourcePsiTorsionAffineIntegralPoint S v T) := by
  rintro ⟨D⟩
  rcases hinf with ⟨g, hg⟩
  have hsome : (T.point D.g).toAffineLift =
      .some (algebraMap (SourcePsiCompletionIntegers S v)
        (SourcePsiCompletionField S v) D.x)
        (algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiCompletionField S v) D.y) D.nonsingular :=
    D.affine_eq
  rw [hg] at hsome
  exact Option.noConfusion hsome

/-- Exact obstruction: the selected affine point has no integral coordinates. -/
def SourcePsiTorsionNonintegral (T : SourcePsiTorsionPointSelection S v) : Prop :=
  ∀ (g : SourceTorsionCarrier S) (x y : SourcePsiCompletionField S v),
    (∃ ns : (SourceTorsionBaseCurve S v).curve.toAffine.Nonsingular x y,
      (T.point g).toAffineLift = .some x y ns) →
      (¬ ∃ x₀ : SourcePsiCompletionIntegers S v,
        algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiCompletionField S v) x₀ = x) ∨
      (¬ ∃ y₀ : SourcePsiCompletionIntegers S v,
        algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiCompletionField S v) y₀ = y)

theorem not_torsionAffineIntegralPoint_of_nonintegral
    {T : SourcePsiTorsionPointSelection S v}
    (hni : SourcePsiTorsionNonintegral S v T) :
    ¬ Nonempty (SourcePsiTorsionAffineIntegralPoint S v T) := by
  rintro ⟨D⟩
  obtain ⟨ns, hsome⟩ := D.affine_eq
  have hbad := hni D.g _ _ ⟨ns, hsome⟩
  rcases hbad with hx | hy
  · exact hx ⟨D.x, rfl⟩
  · exact hy ⟨D.y, rfl⟩

/-- Exact residual: an actual torsion point selection. -/
def SourcePsiTorsionPointSelectionResidual : Prop :=
  Nonempty (SourcePsiTorsionPointSelection S v)

theorem sourcePsiTorsionPointSelectionResidual_iff :
    SourcePsiTorsionPointSelectionResidual S v ↔
      Nonempty (SourcePsiTorsionPointSelection S v) :=
  Iff.rfl

/-- Exact residual: affine/integral selected torsion point. -/
def SourcePsiTorsionAffineIntegralResidual : Prop :=
  ∃ T : SourcePsiTorsionPointSelection S v,
    Nonempty (SourcePsiTorsionAffineIntegralPoint S v T)

theorem sourcePsiTorsionEvaluation_conditional
    (hD : SourcePsiTorsionAffineIntegralResidual S v) :
    Nonempty (SourcePsiIntegralEvaluationData S v h) := by
  rcases hD with ⟨T, ⟨D⟩⟩
  exact ⟨sourcePsiEvaluationDataOfTorsion S v h D⟩

/-- The source contract supplies the abstract torsion carrier. -/
theorem sourcePsiTorsionCarrier_nonempty :
    Nonempty (SourceTorsionCarrier S) :=
  S.torsion.torsionNonempty

/-- The exact missing selection residual, unchanged. -/
theorem sourcePsiTorsionPointSelection_boundary :
    SourcePsiTorsionPointSelectionResidual S v ↔
      Nonempty (SourcePsiTorsionPointSelection S v) :=
  Iff.rfl
end LeanFormal.IUT.SourcePsiTorsionPointEvaluation
end