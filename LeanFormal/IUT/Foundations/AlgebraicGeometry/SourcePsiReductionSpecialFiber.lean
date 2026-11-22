/-
  Reduced curve and special fiber of an actual integral model.

  From `M : SourcePsiIntegralModelData`, the reduced curve is the actual reduction
  of the integral Weierstrass curve to the residue field of
  `v.adicCompletionIntegers`.  We prove its description as the actual
  `WeierstrassCurve.map` along `IsLocalRing.residue`, the discriminant reduction
  law, the elliptic/smooth criterion, and the singular obstruction.  The projective
  special fiber is the actual projective closure.  Identification with the actual
  source special fiber and formal properness/regularity of the integral model
  remain the exact residual.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModelReduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiReductionSpecialFiber

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))
  (M : SourcePsiIntegralModelData S v)

/-- The reduced curve is the actual map of the integral curve along the actual
residue map to the residue field. -/
theorem SourcePsiReducedCurve_eq_map :
    SourcePsiReducedCurve S v M =
      M.curve.map (IsLocalRing.residue (SourcePsiCompletionIntegers S v)) := by
  ext <;>
    simp [SourcePsiReducedCurve, sourcePsiIntegralCoefficientReduction,
      WeierstrassCurve.map]

/-- Coefficient law for the reduced curve, directly from the residue map. -/
theorem SourcePsiReducedCurve_a₁_eq_residue :
    (SourcePsiReducedCurve S v M).a₁ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.a₁ :=
  congrArg WeierstrassCurve.a₁ (SourcePsiReducedCurve_eq_map S v M)

theorem SourcePsiReducedCurve_a₂_eq_residue :
    (SourcePsiReducedCurve S v M).a₂ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.a₂ :=
  congrArg WeierstrassCurve.a₂ (SourcePsiReducedCurve_eq_map S v M)

theorem SourcePsiReducedCurve_a₃_eq_residue :
    (SourcePsiReducedCurve S v M).a₃ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.a₃ :=
  congrArg WeierstrassCurve.a₃ (SourcePsiReducedCurve_eq_map S v M)

theorem SourcePsiReducedCurve_a₄_eq_residue :
    (SourcePsiReducedCurve S v M).a₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.a₄ :=
  congrArg WeierstrassCurve.a₄ (SourcePsiReducedCurve_eq_map S v M)

theorem SourcePsiReducedCurve_a₆_eq_residue :
    (SourcePsiReducedCurve S v M).a₆ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.a₆ :=
  congrArg WeierstrassCurve.a₆ (SourcePsiReducedCurve_eq_map S v M)

/-- The discriminant of the reduced curve is the residue of the integral
discriminant. -/
theorem SourcePsiReducedCurve_Δ :
    (SourcePsiReducedCurve S v M).Δ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.Δ := by
  rw [SourcePsiReducedCurve_eq_map, WeierstrassCurve.map_Δ]

/-- The reduced curve is elliptic/smooth exactly when its discriminant is
nonzero. -/
theorem SourcePsiReducedCurve_isElliptic_iff_Δ_ne_zero :
    (SourcePsiReducedCurve S v M).IsElliptic ↔
      (SourcePsiReducedCurve S v M).Δ ≠ 0 := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]

/-- Nonzero reduced discriminant constructs the actual elliptic structure. -/
theorem SourcePsiReducedCurve_isElliptic_of_Δ_ne_zero
    (hΔ : (SourcePsiReducedCurve S v M).Δ ≠ 0) :
    (SourcePsiReducedCurve S v M).IsElliptic :=
  (SourcePsiReducedCurve_isElliptic_iff_Δ_ne_zero S v M).mpr hΔ

/-- Zero reduced discriminant obstructs the elliptic/smooth structure. -/
theorem SourcePsiReducedCurve_not_isElliptic_of_Δ_eq_zero
    (hΔ : (SourcePsiReducedCurve S v M).Δ = 0) :
    ¬ (SourcePsiReducedCurve S v M).IsElliptic :=
  fun h => (SourcePsiReducedCurve_isElliptic_iff_Δ_ne_zero S v M).mp h hΔ

/-- The actual projective reduced special fiber: the projective closure of the
reduced curve. -/
abbrev SourcePsiSpecialFiberProjective : WeierstrassCurve.Projective := by
  exact (SourcePsiReducedCurve S v M).toProjective

/-- The reducer's residue field is nontrivial, so the singular/elliptic dichotomy
is meaningful. -/
theorem SourcePsiResidueField_nontrivial : Nontrivial (SourcePsiResidueField S v) :=
  inferInstance

/-! ## Proper/regular obstruction statements

Constructed here:
* the actual reduced curve as `M.curve.map (IsLocalRing.residue ...)`;
* all five coefficient reduction laws;
* the discriminant reduction law;
* the exact elliptic/smooth iff nonzero discriminant statement;
* the singular obstruction from zero discriminant;
* the actual projective closure of the reduced curve.

NOT proved here:
1. that the integral model `M` is proper or regular;
2. that the reduced curve is regular at every point when its discriminant is
   nonzero (only the elliptic/smooth criterion is recorded);
3. that the reduced projective fiber is the actual source special fiber;
4. component/node data of the special fiber;
5. that the source reduction type (stable/split multiplicative) is realized.

These are actual geometric statements, not cards.  The zero-discriminant case is
the precise affine finite obstruction recorded above; properness/regularity and
source-fiber identification remain the exact residual.
-/


/-! ## Reduced Weierstrass invariants

theorem SourcePsiReducedCurve_b₂ :
    (SourcePsiReducedCurve S v M).b₂ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.b₂ := by
  rw [SourcePsiReducedCurve_eq_map, WeierstrassCurve.map_b₂]

theorem SourcePsiReducedCurve_b₄ :
    (SourcePsiReducedCurve S v M).b₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.b₄ := by
  rw [SourcePsiReducedCurve_eq_map, WeierstrassCurve.map_b₄]

theorem SourcePsiReducedCurve_b₆ :
    (SourcePsiReducedCurve S v M).b₆ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.b₆ := by
  rw [SourcePsiReducedCurve_eq_map, WeierstrassCurve.map_b₆]

theorem SourcePsiReducedCurve_b₈ :
    (SourcePsiReducedCurve S v M).b₈ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.b₈ := by
  rw [SourcePsiReducedCurve_eq_map, WeierstrassCurve.map_b₈]

theorem SourcePsiReducedCurve_c₄ :
    (SourcePsiReducedCurve S v M).c₄ =
      IsLocalRing.residue (SourcePsiCompletionIntegers S v) M.curve.c₄ := by
  rw [SourcePsiReducedCurve_eq_map, WeierstrassCurve.map_c₄]

/-- Reduced discriminant is zero exactly when the integral discriminant lies in
the maximal ideal. -/
theorem SourcePsiReducedCurve_Δ_eq_zero_iff_mem_maximalIdeal :
    (SourcePsiReducedCurve S v M).Δ = 0 ↔
      M.curve.Δ ∈ IsLocalRing.maximalIdeal (SourcePsiCompletionIntegers S v) := by
  rw [SourcePsiReducedCurve_Δ, IsLocalRing.residue_eq_zero_iff]

/-- Reduced discriminant is nonzero exactly when the integral discriminant is a
unit of the adic completion integers. -/
theorem SourcePsiReducedCurve_Δ_ne_zero_iff_isUnit :
    (SourcePsiReducedCurve S v M).Δ ≠ 0 ↔
      IsUnit M.curve.Δ :=
  by
    rw [SourcePsiReducedCurve_Δ]
    exact IsLocalRing.residue_ne_zero_iff_isUnit

/-! ## Affine regularity from the elliptic criterion

theorem SourcePsiReducedCurve_equation_nonsingular
    (hΔ : (SourcePsiReducedCurve S v M).Δ ≠ 0)
    {x y : SourcePsiResidueField S v}
    (hxy : (SourcePsiReducedCurve S v M).Equation x y) :
    (SourcePsiReducedCurve S v M).Nonsingular x y := by
  letI : (SourcePsiReducedCurve S v M).IsElliptic :=
    SourcePsiReducedCurve_isElliptic_of_Δ_ne_zero S v M hΔ
  exact (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hxy

/-- Zero reduced discriminant gives a nonsmooth/singular affine point in the
sense that the elliptic structure is absent. -/
theorem SourcePsiReducedCurve_no_elliptic_of_Δ_eq_zero
    (hΔ : (SourcePsiReducedCurve S v M).Δ = 0) :
    ¬ (SourcePsiReducedCurve S v M).IsElliptic :=
  SourcePsiReducedCurve_not_isElliptic_of_Δ_eq_zero S v M hΔ

/-! ## Exact proper/regular residual

The reduced curve is actual; its five coefficients, `b₂,b₄,b₆,b₈`, `c₄` and
`Δ` reduce correctly; nonzero `Δ` gives the elliptic structure and affine
nonsingularity; zero `Δ` gives the nonsmooth obstruction.  The actual projective
closure of the reduced curve is available.

Still not proved:
1. that the integral model is proper/regular;
2. that the projective special fiber is proper/regular as a scheme over the
   residue field;
3. that it is the actual source special fiber;
4. component/node structure and stable/split-multiplicative reduction type.

These are exact geometric residuals, not cards.


/-! ## Elliptic/singular dichotomy

theorem SourcePsiReducedCurve_Δ_ne_zero_of_isElliptic
    (hE : (SourcePsiReducedCurve S v M).IsElliptic) :
    (SourcePsiReducedCurve S v M).Δ ≠ 0 :=
  (SourcePsiReducedCurve_isElliptic_iff_Δ_ne_zero S v M).mp hE

theorem SourcePsiReducedCurve_Δ_eq_zero_of_not_isElliptic
    (hE : ¬ (SourcePsiReducedCurve S v M).IsElliptic) :
    (SourcePsiReducedCurve S v M).Δ = 0 := by
  by_contra hΔ
  exact hE (SourcePsiReducedCurve_isElliptic_of_Δ_ne_zero S v M hΔ)

/-- The reduced special fiber is either elliptic (nonzero discriminant) or has
zero discriminant (the singular obstruction). -/
theorem SourcePsiSpecialFiber_elliptic_or_Δ_zero :
    (SourcePsiReducedCurve S v M).IsElliptic ∨
      (SourcePsiReducedCurve S v M).Δ = 0 := by
  by_cases hΔ : (SourcePsiReducedCurve S v M).Δ = 0
  · exact Or.inr hΔ
  · exact Or.inl (SourcePsiReducedCurve_isElliptic_of_Δ_ne_zero S v M hΔ)

/-- Exact projective special-fiber point type: actual projective points of the
reduced curve. -/
abbrev SourcePsiSpecialFiberProjectivePoint : Type u :=
  (SourcePsiSpecialFiberProjective S v M).Point

/-- Actual nonsingular projective points of the reduced curve. -/
abbrev SourcePsiSpecialFiberNonsingularProjectivePoint : Type u :=
  (SourcePsiSpecialFiberProjective S v M).NonsingularPoint

/-! ## Final exact residual

Actual: reduced curve, coefficient/invariant reduction laws, discriminant
criterion, affine nonsingularity under nonzero discriminant, singular obstruction
at zero discriminant, projective point/nonsingular-point types, and the
elliptic/singular dichotomy.

Missing: proper/regular integral model, proper/regular projective special fiber,
source-fiber identification, component/node data, stable/split-multiplicative
reduction type.  No model/point is fabricated.

end LeanFormal.IUT.SourcePsiReductionSpecialFiber

end