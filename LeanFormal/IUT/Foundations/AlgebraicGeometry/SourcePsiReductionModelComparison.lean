/-
  Comparison of the reduced special fiber with an actual claimed source special
  fiber through the integral model.

  An actual integral model `M` gives the reduced curve `SourcePsiReducedCurve`.
  A source-special-fiber identification `D` is an actual Weierstrass curve over
  the residue field together with its equality to the reduced curve.  This file
  proves the object equality, all five coefficient comparisons, the invariant and
  discriminant comparisons, the elliptic/singular transfer, and the uniqueness of
  the identified source special fiber for a fixed model.  Proper/regular/component
  data remain the exact residual.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiReductionSpecialFiber

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiReductionModelComparison

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiReductionSpecialFiber
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))
  (M : SourcePsiIntegralModelData S v)
  (D : SourcePsiReductionIdentification S v M)

/-- Object comparison: the identified source special fiber is the actual reduced
curve of the integral model. -/
theorem sourceSpecialFiber_eq_reducedCurve :
    D.specialFiber_eq = SourcePsiReducedCurve S v M :=
  D.specialFiber_eq_reduced

/-- Coefficient comparison `a₁`. -/
theorem sourceSpecialFiber_a₁_eq_reduced :
    D.specialFiber_eq.a₁ = (SourcePsiReducedCurve S v M).a₁ :=
  congrArg WeierstrassCurve.a₁ (sourceSpecialFiber_eq_reducedCurve S v M D)

theorem sourceSpecialFiber_a₂_eq_reduced :
    D.specialFiber_eq.a₂ = (SourcePsiReducedCurve S v M).a₂ :=
  congrArg WeierstrassCurve.a₂ (sourceSpecialFiber_eq_reducedCurve S v M D)

theorem sourceSpecialFiber_a₃_eq_reduced :
    D.specialFiber_eq.a₃ = (SourcePsiReducedCurve S v M).a₃ :=
  congrArg WeierstrassCurve.a₃ (sourceSpecialFiber_eq_reducedCurve S v M D)

theorem sourceSpecialFiber_a₄_eq_reduced :
    D.specialFiber_eq.a₄ = (SourcePsiReducedCurve S v M).a₄ :=
  congrArg WeierstrassCurve.a₄ (sourceSpecialFiber_eq_reducedCurve S v M D)

theorem sourceSpecialFiber_a₆_eq_reduced :
    D.specialFiber_eq.a₆ = (SourcePsiReducedCurve S v M).a₆ :=
  congrArg WeierstrassCurve.a₆ (sourceSpecialFiber_eq_reducedCurve S v M D)

/-- Coefficient comparison against the integral-model coefficient reductions. -/
theorem sourceSpecialFiber_a₁_eq_residue :
    D.specialFiber_eq.a₁ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.a₁ :=
  (sourceSpecialFiber_a₁_eq_reduced S v M D).trans
    (SourcePsiReducedCurve_a₁_eq_residue S v M)

theorem sourceSpecialFiber_a₂_eq_residue :
    D.specialFiber_eq.a₂ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.a₂ :=
  (sourceSpecialFiber_a₂_eq_reduced S v M D).trans
    (SourcePsiReducedCurve_a₂_eq_residue S v M)

theorem sourceSpecialFiber_a₃_eq_residue :
    D.specialFiber_eq.a₃ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.a₃ :=
  (sourceSpecialFiber_a₃_eq_reduced S v M D).trans
    (SourcePsiReducedCurve_a₃_eq_residue S v M)

theorem sourceSpecialFiber_a₄_eq_residue :
    D.specialFiber_eq.a₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.a₄ :=
  (sourceSpecialFiber_a₄_eq_reduced S v M D).trans
    (SourcePsiReducedCurve_a₄_eq_residue S v M)

theorem sourceSpecialFiber_a₆_eq_residue :
    D.specialFiber_eq.a₆ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.a₆ :=
  (sourceSpecialFiber_a₆_eq_reduced S v M D).trans
    (SourcePsiReducedCurve_a₆_eq_residue S v M)

/-- Discriminant comparison. -/
theorem sourceSpecialFiber_Δ_eq_reduced :
    D.specialFiber_eq.Δ = (SourcePsiReducedCurve S v M).Δ :=
  congrArg WeierstrassCurve.Δ (sourceSpecialFiber_eq_reducedCurve S v M D)

theorem sourceSpecialFiber_Δ_eq_residue :
    D.specialFiber_eq.Δ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.Δ :=
  (sourceSpecialFiber_Δ_eq_reduced S v M D).trans
    (SourcePsiReducedCurve_Δ S v M)

/-- Elliptic/smooth structure transfers between the identified source special
fiber and the actual reduced curve. -/
theorem sourceSpecialFiber_isElliptic_iff_reduced :
    D.specialFiber_eq.IsElliptic ↔ (SourcePsiReducedCurve S v M).IsElliptic := by
  rw [sourceSpecialFiber_eq_reducedCurve S v M D]

/-- Zero reduced discriminant obstructs elliptic/smooth structure of the
identified source special fiber. -/
theorem sourceSpecialFiber_not_isElliptic_of_reduced_Δ_eq_zero
    (hΔ : (SourcePsiReducedCurve S v M).Δ = 0) :
    ¬ D.specialFiber_eq.IsElliptic :=
  fun hE => (SourcePsiReducedCurve_not_isElliptic_of_Δ_eq_zero S v M hΔ)
    ((sourceSpecialFiber_isElliptic_iff_reduced S v M D).mp hE)

/-- Uniqueness: for a fixed integral model, any two identified source special
fibers have the same underlying Weierstrass curve. -/
theorem sourceSpecialFiber_unique
    (E : SourcePsiReductionIdentification S v M) :
    D.specialFiber_eq = E.specialFiber_eq := by
  rw [sourceSpecialFiber_eq_reducedCurve S v M D,
    sourceSpecialFiber_eq_reducedCurve S v M E]

/-! ## Exact proper/regular/component residual

Compared here: the actual reduced curve of `M` and any identified source special
fiber agree as Weierstrass curves; all five coefficients, the discriminant, and
the elliptic/smooth structure agree with the actual coefficient reductions of
`M`.  For a fixed model the identified special fiber is unique.

Still missing:
1. an actual source special fiber that is not merely an equality datum equal to
   the reduced curve;
2. properness and regularity of the integral model and its special fiber;
3. the component/node graph of the special fiber;
4. the stable/split-multiplicative reduction type required by the source
   contract;
5. comparison of special fibers arising from different integral models (a
   model-change/component correspondence).

These are actual geometric residuals.  No model, point, or component is
fabricated.
-/


/-! ## Invariant comparisons

theorem sourceSpecialFiber_b₂_eq_residue :
    D.specialFiber_eq.b₂ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.b₂ := by
  rw [sourceSpecialFiber_eq_reducedCurve S v M D]
  exact SourcePsiReducedCurve_b₂ S v M

theorem sourceSpecialFiber_b₄_eq_residue :
    D.specialFiber_eq.b₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.b₄ := by
  rw [sourceSpecialFiber_eq_reducedCurve S v M D]
  exact SourcePsiReducedCurve_b₄ S v M

theorem sourceSpecialFiber_b₆_eq_residue :
    D.specialFiber_eq.b₆ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.b₆ := by
  rw [sourceSpecialFiber_eq_reducedCurve S v M D]
  exact SourcePsiReducedCurve_b₆ S v M

theorem sourceSpecialFiber_b₈_eq_residue :
    D.specialFiber_eq.b₈ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.b₈ := by
  rw [sourceSpecialFiber_eq_reducedCurve S v M D]
  exact SourcePsiReducedCurve_b₈ S v M

theorem sourceSpecialFiber_c₄_eq_residue :
    D.specialFiber_eq.c₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.c₄ := by
  rw [sourceSpecialFiber_eq_reducedCurve S v M D]
  exact SourcePsiReducedCurve_c₄ S v M

/-- Elliptic structure of the identified source special fiber is equivalent to
nonzero discriminant. -/
theorem sourceSpecialFiber_isElliptic_iff_Δ_ne_zero :
    D.specialFiber_eq.IsElliptic ↔ D.specialFiber_eq.Δ ≠ 0 := by
  rw [sourceSpecialFiber_eq_reducedCurve S v M D]
  exact SourcePsiReducedCurve_isElliptic_iff_Δ_ne_zero S v M

theorem sourceSpecialFiber_Δ_ne_zero_of_isElliptic
    (hE : D.specialFiber_eq.IsElliptic) : D.specialFiber_eq.Δ ≠ 0 :=
  (sourceSpecialFiber_isElliptic_iff_Δ_ne_zero S v M D).mp hE

theorem sourceSpecialFiber_not_isElliptic_of_Δ_eq_zero
    (hΔ : D.specialFiber_eq.Δ = 0) : ¬ D.specialFiber_eq.IsElliptic :=
  fun hE => (sourceSpecialFiber_Δ_ne_zero_of_isElliptic S v M D hE) hΔ


theorem sourceSpecialFiber_Δ_eq_zero_iff_maximalIdeal :
    D.specialFiber_eq.Δ = 0 ↔
      M.curve.Δ ∈ IsLocalRing.maximalIdeal (SourcePsiCompletionIntegers S v) := by
  rw [sourceSpecialFiber_Δ_eq_reduced S v M D,
    SourcePsiReducedCurve_Δ_eq_zero_iff_mem_maximalIdeal S v M]

end LeanFormal.IUT.SourcePsiReductionModelComparison

end