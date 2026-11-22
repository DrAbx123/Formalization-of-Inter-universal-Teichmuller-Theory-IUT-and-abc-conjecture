/-
# The additive-case value card at `2` for the displayed ABC Frey model

On an `IsABCTriple a b (a + b)`, conditional on the displayed model
`freyPadicCurve 2 a b` being already minimal over `ℤ_[2]` (the `k = 0` rows),
this file records the additive-case card:

* additive reduction at `2`;
* `v₂(Δ_min) = 4 + 2 * v₂(a * b * (a + b))`;
* `v₂(c₄) = 4`.

The conditionality is explicit: minimality of the displayed model itself is
not proved here; it is the target of the criterion file `FreyTwoAdicMinimalityCriterion`.

Literature freeze (statement-level): Silverman, *Advanced Topics in the
Arithmetic of Elliptic Curves*, IV.9 (invariants of a minimal model) and
IV.10 (Tate's algorithm); Saito 1988 (conductor-discriminant exponents,
cited only).  The `m₂` and `swan₂` exponents remain open in this project:
no value, formula, or compatibility claim about them is stated or endorsed in
this file.
-/

import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicMinimalDiscriminantValuation

noncomputable section

open scoped WeierstrassCurve WithZero

namespace LeanFormal.IUT

/-! ## Displayed-model formulas and additive value card -/

/-- The displayed model's discriminant as a natural-number cast. -/
theorem freyPadicCurve_two_discriminant_eq_natCast (a b : ℕ) :
    (freyPadicCurve 2 a b).Δ =
      ((16 * a ^ 2 * b ^ 2 * (a + b) ^ 2 : ℕ) : ℚ_[2]) := by
  rw [freyPadicCurve_discriminant (p := 2) (c := a + b) rfl]
  have hshape : 16 * a ^ 2 * b ^ 2 * (a + b) ^ 2 =
      16 * (a * b * (a + b)) ^ 2 := by ring
  rw [hshape]

/-- The displayed model's `c₄` as a natural-number cast. -/
theorem freyPadicCurve_two_c4_eq_natCast (a b : ℕ) :
    (freyPadicCurve 2 a b).c₄ =
      ((16 * abcInvariantPolynomial a b : ℕ) : ℚ_[2]) := by
  rw [freyPadicCurve_c4_eq_map_integral, freyPadicIntegralModel_two_c4_eq_natCast]
  exact map_natCast (algebraMap ℤ_[2] ℚ_[2]) _

/-- On ABC triples the displayed `c₄` has 2-adic valuation exactly 4. -/
theorem freyPadicCurve_two_c4_valuation_eq_exp_neg_four {a b : ℕ}
    (h : IsABCTriple a b (a + b)) :
    freyPadicValuation 2 (freyPadicCurve 2 a b).c₄ = WithZero.exp (-4) := by
  have hne : 16 * abcInvariantPolynomial a b ≠ 0 :=
    Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt h.abcInvariantPolynomial_pos)
  rw [freyPadicCurve_two_c4_eq_natCast,
    freyPadicValuation_two_natCast_eq_exp_neg_padicValNat hne,
    IsABCTriple.padicValNat_two_sixteen_abcInvariantPolynomial h]
  norm_num

/-- On ABC triples the displayed discriminant has 2-adic valuation
`4 + 2 * v₂(a * b * (a + b))`. -/
theorem freyPadicCurve_two_discriminant_valuation_eq_exp_neg {a b : ℕ}
    (h : IsABCTriple a b (a + b)) :
    freyPadicValuation 2 (freyPadicCurve 2 a b).Δ =
      WithZero.exp (-((4 + 2 * padicValNat 2 (a * b * (a + b)) : ℕ) : ℤ)) := by
  have hne' : a * b * (a + b) ≠ 0 := Nat.ne_of_gt h.abcInvariant_product_pos
  have hne : 16 * a ^ 2 * b ^ 2 * (a + b) ^ 2 ≠ 0 := by
    have hshape : 16 * a ^ 2 * b ^ 2 * (a + b) ^ 2 =
        16 * (a * b * (a + b)) ^ 2 := by ring
    rw [hshape]
    exact Nat.mul_ne_zero (by norm_num) (pow_ne_zero 2 hne')
  rw [freyPadicCurve_two_discriminant_eq_natCast,
    freyPadicValuation_two_natCast_eq_exp_neg_padicValNat hne,
    IsABCTriple.padicValNat_two_freyDiscriminant h]

/-- **The additive value card at `2`** (conditional on the displayed model
being minimal, i.e. on the `k = 0` rows): the reduction is additive, the
minimal discriminant has `v₂ = 4 + 2 * v₂(a * b * (a + b))`, and the
displayed `c₄` has `v₂ = 4`. -/
theorem freyTwoAdicAdditiveCaseValueCard (a b : ℕ) (h : IsABCTriple a b (a + b))
    [hmin : WeierstrassCurve.IsMinimal ℤ_[2] (freyPadicCurve 2 a b)] :
    WeierstrassCurve.HasAdditiveReduction ℤ_[2] (freyPadicCurve 2 a b) ∧
      freyTwoAdicMinimalDiscriminantValuation a b =
        WithZero.exp (-((4 + 2 * padicValNat 2 (a * b * (a + b)) : ℕ) : ℤ)) ∧
      freyPadicValuation 2 (freyPadicCurve 2 a b).c₄ = WithZero.exp (-4) := by
  refine ⟨?_, ?_, ?_⟩
  · exact freyPadicCurve_two_hasAdditiveReduction_of_isMinimal a b
  · rw [freyTwoAdicMinimalDiscriminantValuation_eq_of_isMinimal a b]
    exact freyPadicCurve_two_discriminant_valuation_eq_exp_neg h
  · exact freyPadicCurve_two_c4_valuation_eq_exp_neg_four h

end LeanFormal.IUT
