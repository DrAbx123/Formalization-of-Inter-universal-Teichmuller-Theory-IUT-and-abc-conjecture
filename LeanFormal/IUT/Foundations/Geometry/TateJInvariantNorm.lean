/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Geometry.TateCurveDiscriminantEstimates

/-!
# The p-adic norm of the Tate q-series j-invariant

For a prime label `l` with `l.value ≥ 5`, the canonical q-series equation
`canonicalCurve l` over `Q_l` is the actual Tate equation at the parameter
`q = l.value`.  The preceding estimate modules prove that its invariant `c₄`
is a unit of norm `1`, and that its discriminant `Δ` is nonzero with norm
`‖q l‖`.

This module defines the Weierstrass j-invariant of that equation,

`tateJInvariant l = c₄ ^ 3 / Δ`,

and proves the exact norm identity

`‖tateJInvariant l‖ = (‖q l‖)⁻¹`.

Equivalently `‖tateJInvariant l‖ = l.value`, so `1 < ‖tateJInvariant l‖`; in
particular the j-invariant is not an integral p-adic element: there is no
`z : Z_l` whose image in `Q_l` equals `tateJInvariant l`.

The statements here are about the norm of the j-invariant of the canonical
q-series equation.  They do not identify `q` with `j⁻¹`, do not assert Tate
analytic uniformization, and do not compare with a separately supplied
elliptic curve over a number field.
-/

namespace LeanFormal.IUT

noncomputable section

namespace TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

section GeneralJNorm

/-- If `W` is a Weierstrass curve over `Q_l` whose `c₄` has norm one and whose
discriminant has norm `‖q l‖`, then its Weierstrass j-invariant `c₄ ^ 3 / Δ`
has norm `(‖q l‖)⁻¹`.  This is the reusable form of the estimate; the
canonical Tate equation below supplies the two hypotheses from the earlier
estimate modules. -/
theorem norm_c4_cube_div_delta_of_norm_c4_eq_one
    (W : WeierstrassCurve ℚ_[l.value])
    (hc4 : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ = ‖q l‖) :
    ‖W.c₄ ^ 3 / W.Δ‖ = (‖q l‖)⁻¹ := by
  rw [norm_div, norm_pow, hc4, hΔ, one_pow, one_div]

end GeneralJNorm

section TateJInvariant

/-- The j-invariant `c₄ ^ 3 / Δ` of the canonical Tate q-series equation over
`Q_l`.  This is the actual Weierstrass j-invariant of the canonical equation,
not an inverse of `q`. -/
def tateJInvariant : ℚ_[l.value] :=
  (canonicalCurve l).c₄ ^ 3 / (canonicalCurve l).Δ

@[simp] theorem tateJInvariant_eq :
    tateJInvariant l =
      (canonicalCurve l).c₄ ^ 3 / (canonicalCurve l).Δ := rfl

/-- The `c₄`-norm hypothesis for the canonical equation, in the exact form
required by the general j-norm lemma. -/
theorem canonicalCurve_c4_norm_for_j :
    ‖(canonicalCurve l).c₄‖ = 1 := by
  simpa [canonicalCurve] using c4_norm_eq_one l

theorem canonicalCurve_c4_cube_div_delta_norm :
    ‖(canonicalCurve l).c₄ ^ 3 / (canonicalCurve l).Δ‖ =
      (‖q l‖)⁻¹ :=
  norm_c4_cube_div_delta_of_norm_c4_eq_one l (canonicalCurve l)
    (canonicalCurve_c4_norm_for_j l)
    (canonicalCurve_delta_norm_eq_q l)

/-- The exact norm of the Tate q-series j-invariant. -/
theorem tateJInvariant_norm : ‖tateJInvariant l‖ = (‖q l‖)⁻¹ := by
  rw [tateJInvariant]
  exact canonicalCurve_c4_cube_div_delta_norm l

/-- The j-invariant norm read off from the discriminant. -/
theorem tateJInvariant_norm_eq_inv_delta_norm :
    ‖tateJInvariant l‖ = (‖(canonicalCurve l).Δ‖)⁻¹ := by
  rw [tateJInvariant_norm, canonicalCurve_delta_norm_eq_q]

/-- Since `‖q l‖ = l.value⁻¹`, the j-invariant has norm exactly `l.value`. -/
theorem tateJInvariant_norm_eq_prime :
    ‖tateJInvariant l‖ = (l.value : ℝ) := by
  rw [tateJInvariant_norm, q_norm_eq, inv_inv]

/-- The j-invariant is not p-adically integral: its norm exceeds one. -/
theorem tateJInvariant_norm_gt_one : 1 < ‖tateJInvariant l‖ := by
  rw [tateJInvariant_norm_eq_prime]
  have h : (5 : ℝ) ≤ (l.value : ℝ) := by exact_mod_cast l.ge_five
  linarith

theorem tateJInvariant_norm_pos : 0 < ‖tateJInvariant l‖ :=
  lt_trans zero_lt_one (tateJInvariant_norm_gt_one l)

/-- The norm of the j-invariant is the reciprocal of the norm of `q`: the
product `‖j‖ * ‖q‖` equals one. -/
theorem tateJInvariant_norm_mul_q_norm :
    ‖tateJInvariant l‖ * ‖q l‖ = 1 := by
  rw [tateJInvariant_norm, inv_mul_cancel₀ (ne_of_gt (q_norm_pos l))]

theorem tateJInvariant_ne_zero : tateJInvariant l ≠ 0 := by
  intro h
  have hp := tateJInvariant_norm_pos l
  rw [h, norm_zero] at hp
  exact lt_irrefl (0 : ℝ) hp

/-- The defining relation `j * Δ = c₄ ^ 3`. -/
theorem tateJInvariant_mul_delta :
    tateJInvariant l * (canonicalCurve l).Δ =
      (canonicalCurve l).c₄ ^ 3 := by
  rw [tateJInvariant]
  exact div_mul_cancel₀ _ (canonicalCurve_delta_ne_zero l)

/-- The j-invariant is not the image of any integral p-adic element. -/
theorem tateJInvariant_not_integral_element :
    ¬ ∃ z : ℤ_[l.value], (z : ℚ_[l.value]) = tateJInvariant l := by
  rintro ⟨z, hz⟩
  have hzle : ‖(z : ℚ_[l.value])‖ ≤ 1 := PadicInt.norm_le_one z
  rw [hz] at hzle
  exact (not_le.mpr (tateJInvariant_norm_gt_one l)) hzle

/-- The j-invariant of the integral model `integralCurveMap l` is the same
element as `tateJInvariant l`. -/
theorem integralCurveMap_jInvariant_eq_tateJInvariant :
    (integralCurveMap l).c₄ ^ 3 / (integralCurveMap l).Δ =
      tateJInvariant l := by
  rw [integralCurveMap_eq_canonical]
  rfl

theorem integralCurveMap_jInvariant_norm :
    ‖(integralCurveMap l).c₄ ^ 3 / (integralCurveMap l).Δ‖ =
      (‖q l‖)⁻¹ := by
  rw [integralCurveMap_jInvariant_eq_tateJInvariant, tateJInvariant_norm]

end TateJInvariant

section JInvariantPacket

/-- Consumer-facing packet collecting the exact j-invariant data of the
canonical Tate q-series equation. -/
structure TateJInvariantNormPacket where
  j : ℚ_[l.value]
  j_eq : j = tateJInvariant l
  j_eq_c4_cube_div_delta : j = (canonicalCurve l).c₄ ^ 3 / (canonicalCurve l).Δ
  c4_norm : ‖(canonicalCurve l).c₄‖ = 1
  c4_unit : IsUnit (canonicalCurve l).c₄
  delta_norm : ‖(canonicalCurve l).Δ‖ = ‖q l‖
  delta_nonzero : (canonicalCurve l).Δ ≠ 0
  j_norm : ‖j‖ = (‖q l‖)⁻¹
  j_norm_eq_prime : ‖j‖ = (l.value : ℝ)
  j_norm_gt_one : 1 < ‖j‖
  j_norm_mul_q_norm : ‖j‖ * ‖q l‖ = 1
  j_nonzero : j ≠ 0

def tateJInvariantNormPacket : TateJInvariantNormPacket l where
  j := tateJInvariant l
  j_eq := rfl
  j_eq_c4_cube_div_delta := rfl
  c4_norm := canonicalCurve_c4_norm_for_j l
  c4_unit := canonicalCurve_c4_unit l
  delta_norm := canonicalCurve_delta_norm_eq_q l
  delta_nonzero := canonicalCurve_delta_ne_zero l
  j_norm := tateJInvariant_norm l
  j_norm_eq_prime := tateJInvariant_norm_eq_prime l
  j_norm_gt_one := tateJInvariant_norm_gt_one l
  j_norm_mul_q_norm := tateJInvariant_norm_mul_q_norm l
  j_nonzero := tateJInvariant_ne_zero l

theorem tateJInvariantNormPacket_j :
    (tateJInvariantNormPacket l).j = tateJInvariant l := rfl

theorem tateJInvariantNormPacket_c4_norm :
    ‖(canonicalCurve l).c₄‖ = 1 :=
  (tateJInvariantNormPacket l).c4_norm

theorem tateJInvariantNormPacket_c4_unit :
    IsUnit (canonicalCurve l).c₄ :=
  (tateJInvariantNormPacket l).c4_unit

theorem tateJInvariantNormPacket_delta_norm :
    ‖(canonicalCurve l).Δ‖ = ‖q l‖ :=
  (tateJInvariantNormPacket l).delta_norm

theorem tateJInvariantNormPacket_delta_nonzero :
    (canonicalCurve l).Δ ≠ 0 :=
  (tateJInvariantNormPacket l).delta_nonzero

theorem tateJInvariantNormPacket_j_norm :
    ‖(tateJInvariantNormPacket l).j‖ = (‖q l‖)⁻¹ :=
  (tateJInvariantNormPacket l).j_norm

theorem tateJInvariantNormPacket_j_norm_eq_prime :
    ‖(tateJInvariantNormPacket l).j‖ = (l.value : ℝ) :=
  (tateJInvariantNormPacket l).j_norm_eq_prime

theorem tateJInvariantNormPacket_j_norm_gt_one :
    1 < ‖(tateJInvariantNormPacket l).j‖ :=
  (tateJInvariantNormPacket l).j_norm_gt_one

theorem tateJInvariantNormPacket_j_norm_mul_q_norm :
    ‖(tateJInvariantNormPacket l).j‖ * ‖q l‖ = 1 :=
  (tateJInvariantNormPacket l).j_norm_mul_q_norm

theorem tateJInvariantNormPacket_j_nonzero :
    (tateJInvariantNormPacket l).j ≠ 0 :=
  (tateJInvariantNormPacket l).j_nonzero

/-- The complete norm-level output for the Tate j-invariant. -/
theorem tateJInvariantNormPacket_summary :
    ‖(tateJInvariantNormPacket l).j‖ = (‖q l‖)⁻¹ ∧
      ‖(tateJInvariantNormPacket l).j‖ = (l.value : ℝ) ∧
      1 < ‖(tateJInvariantNormPacket l).j‖ ∧
      ‖(tateJInvariantNormPacket l).j‖ * ‖q l‖ = 1 :=
  ⟨tateJInvariantNormPacket_j_norm l,
    tateJInvariantNormPacket_j_norm_eq_prime l,
    tateJInvariantNormPacket_j_norm_gt_one l,
    tateJInvariantNormPacket_j_norm_mul_q_norm l⟩

end JInvariantPacket

end TateCurvePadic

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def tateJInvariantNorm : Obligation :=
  { id := "Foundations.Geometry.tate-j-invariant-norm"
    source := "IUT I, Definition 3.1(c); Weierstrass j-invariant of the canonical q-series equation"
    status := VerificationStatus.proved
    note :=
      "For q equal to p in Q_p, p >= 5, the Weierstrass j-invariant " ++
        "j = c4^3 / Delta of the canonical q-series equation has norm exactly " ++
        "||q||^{-1} = p, because the proved estimates give ||c4|| = 1, " ++
        "IsUnit c4, Delta nonzero and ||Delta|| = ||q||. Consequently j is " ++
        "nonzero and is not an integral p-adic element. The definition is the " ++
        "actual Weierstrass j-invariant; q is not replaced by an arbitrary " ++
        "inverse of j, and no Tate uniformization is asserted."
    dependsOn :=
      [ "Foundations.Geometry.tate-curve-discriminant-estimates" ] }

end LeanFormal.IUT.Audit
