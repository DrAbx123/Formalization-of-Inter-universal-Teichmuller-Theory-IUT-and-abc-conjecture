import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualMinimalModelInhabited
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

/-!
# Corrected reduction special fiber

From the corrected actual Mathlib minimal model (integral curve plus actual
Weierstrass change), this file constructs the reduced curve over the residue
field as the actual special fiber, proves the coefficient/discriminant laws,
the elliptic/singular comparisons, and the corrected reduction identification.
No raw trivial-change model is forced.
-/

namespace LeanFormal.IUT.SourcePsiCorrectedReductionSpecialFiber

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiActualMinimalModelInhabited
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual corrected special fiber: the reduced curve of the corrected
minimal model over the residue field. -/
noncomputable abbrev SourcePsiCorrectedSpecialFiber
    (A : SourcePsiActualMinimalModelCorrected S v) :
    WeierstrassCurve (IsLocalRing.ResidueField (SourcePsiCompletionIntegers S v)) :=
  correctedReducedCurve S v A

theorem SourcePsiCorrectedSpecialFiber_eq_map
    (A : SourcePsiActualMinimalModelCorrected S v) :
    SourcePsiCorrectedSpecialFiber S v A =
      A.curve.map (IsLocalRing.residue (SourcePsiCompletionIntegers S v)) :=
  rfl

theorem SourcePsiCorrectedSpecialFiber_eq_correctedReducedCurve
    (A : SourcePsiActualMinimalModelCorrected S v) :
    SourcePsiCorrectedSpecialFiber S v A = correctedReducedCurve S v A :=
  rfl

theorem SourcePsiCorrectedSpecialFiber_a₁
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).a₁ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.a₁ :=
  correctedReducedCurve_a₁ S v A

theorem SourcePsiCorrectedSpecialFiber_a₂
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).a₂ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.a₂ :=
  correctedReducedCurve_a₂ S v A

theorem SourcePsiCorrectedSpecialFiber_a₃
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).a₃ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.a₃ :=
  correctedReducedCurve_a₃ S v A

theorem SourcePsiCorrectedSpecialFiber_a₄
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).a₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.a₄ :=
  correctedReducedCurve_a₄ S v A

theorem SourcePsiCorrectedSpecialFiber_a₆
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).a₆ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.a₆ :=
  correctedReducedCurve_a₆ S v A

theorem SourcePsiCorrectedSpecialFiber_Δ
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).Δ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.Δ :=
  correctedReducedCurve_Δ S v A

theorem SourcePsiCorrectedSpecialFiber_c₄
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).c₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.c₄ :=
  correctedReducedCurve_c₄ S v A

theorem SourcePsiCorrectedSpecialFiber_b₂
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).b₂ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.b₂ :=
  correctedReducedCurve_b₂ S v A

theorem SourcePsiCorrectedSpecialFiber_b₄
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).b₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.b₄ :=
  correctedReducedCurve_b₄ S v A

theorem SourcePsiCorrectedSpecialFiber_b₆
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).b₆ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.b₆ :=
  correctedReducedCurve_b₆ S v A

theorem SourcePsiCorrectedSpecialFiber_b₈
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).b₈ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.b₈ :=
  correctedReducedCurve_b₈ S v A

/-- Elliptic/smooth criterion: the corrected special fiber is elliptic exactly
when its discriminant is nonzero. -/
theorem SourcePsiCorrectedSpecialFiber_isElliptic_iff_Δ_ne_zero
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).IsElliptic ↔
      (SourcePsiCorrectedSpecialFiber S v A).Δ ≠ 0 := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]

theorem SourcePsiCorrectedSpecialFiber_isElliptic_iff_residue_Δ_ne_zero
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).IsElliptic ↔
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) A.curve.Δ ≠ 0 := by
  rw [SourcePsiCorrectedSpecialFiber_isElliptic_iff_Δ_ne_zero,
    SourcePsiCorrectedSpecialFiber_Δ]

theorem SourcePsiCorrectedSpecialFiber_not_isElliptic_of_Δ_eq_zero
    (A : SourcePsiActualMinimalModelCorrected S v)
    (hΔ : (SourcePsiCorrectedSpecialFiber S v A).Δ = 0) :
    ¬ (SourcePsiCorrectedSpecialFiber S v A).IsElliptic :=
  fun hE =>
    (SourcePsiCorrectedSpecialFiber_isElliptic_iff_Δ_ne_zero S v A).mp hE hΔ

theorem SourcePsiCorrectedSpecialFiber_elliptic_or_Δ_zero
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (SourcePsiCorrectedSpecialFiber S v A).IsElliptic ∨
      (SourcePsiCorrectedSpecialFiber S v A).Δ = 0 := by
  by_cases hΔ : (SourcePsiCorrectedSpecialFiber S v A).Δ = 0
  · exact Or.inr hΔ
  · exact Or.inl ((SourcePsiCorrectedSpecialFiber_isElliptic_iff_Δ_ne_zero S v A).mpr hΔ)

/-- Affine nonsingularity of the corrected special fiber from nonzero
discriminant. -/
theorem SourcePsiCorrectedSpecialFiber_equation_nonsingular
    (A : SourcePsiActualMinimalModelCorrected S v)
    (hΔ : (SourcePsiCorrectedSpecialFiber S v A).Δ ≠ 0)
    {x y : IsLocalRing.ResidueField (SourcePsiCompletionIntegers S v)}
    (hxy : (SourcePsiCorrectedSpecialFiber S v A).Equation x y) :
    (SourcePsiCorrectedSpecialFiber S v A).Nonsingular x y := by
  letI : (SourcePsiCorrectedSpecialFiber S v A).IsElliptic :=
    (SourcePsiCorrectedSpecialFiber_isElliptic_iff_Δ_ne_zero S v A).mpr hΔ
  exact (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hxy

/-- The actual projective corrected special fiber. -/
noncomputable abbrev SourcePsiCorrectedSpecialFiberProjective
    (A : SourcePsiActualMinimalModelCorrected S v) :
    WeierstrassCurve.Projective :=
  (SourcePsiCorrectedSpecialFiber S v A).toProjective

theorem SourcePsiCorrectedSpecialFiberProjective_eq
    (A : SourcePsiActualMinimalModelCorrected S v) :
    SourcePsiCorrectedSpecialFiberProjective S v A =
      (SourcePsiCorrectedSpecialFiber S v A).toProjective :=
  rfl

/-- Corrected reduction identification: a claimed source special fiber together
with its equality to the actual corrected reduced curve. -/
structure SourcePsiCorrectedReductionIdentification
    (A : SourcePsiActualMinimalModelCorrected S v) where
  /-- The claimed special fiber. -/
  specialFiber : WeierstrassCurve (IsLocalRing.ResidueField (SourcePsiCompletionIntegers S v))
  /-- It is the actual corrected reduced curve. -/
  specialFiber_eq_reduced : specialFiber = SourcePsiCorrectedSpecialFiber S v A

/-- The canonical actual identification with the corrected reduced curve
itself; no raw trivial-change model is required. -/
noncomputable def sourcePsiCorrectedReductionIdentification
    (A : SourcePsiActualMinimalModelCorrected S v) :
    SourcePsiCorrectedReductionIdentification S v A where
  specialFiber := SourcePsiCorrectedSpecialFiber S v A
  specialFiber_eq_reduced := rfl

theorem sourcePsiCorrectedReductionIdentification_eq_reduced
    (A : SourcePsiActualMinimalModelCorrected S v) :
    (sourcePsiCorrectedReductionIdentification S v A).specialFiber =
      SourcePsiCorrectedSpecialFiber S v A :=
  rfl

/-- The corrected identification residual is inhabited by the canonical
identification; no trivial-change condition is imposed. -/
theorem sourcePsiCorrectedReductionIdentification_nonempty
    (A : SourcePsiActualMinimalModelCorrected S v) :
    Nonempty (SourcePsiCorrectedReductionIdentification S v A) :=
  ⟨sourcePsiCorrectedReductionIdentification S v A⟩

/-- The corrected special fiber does not require `A.change = 1`. -/
theorem sourcePsiCorrectedSpecialFiber_independent_of_trivial_change
    (A : SourcePsiActualMinimalModelCorrected S v) :
    SourcePsiCorrectedSpecialFiber S v A =
      correctedReducedCurve S v A :=
  rfl

end LeanFormal.IUT.SourcePsiCorrectedReductionSpecialFiber
end