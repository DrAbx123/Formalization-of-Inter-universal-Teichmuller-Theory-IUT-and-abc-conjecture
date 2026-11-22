/-
# 2-adic minimal model of the ABC Frey curve in case C, `k = 1`

Case C rows: `a ≡ 1 (mod 4)`, `16 ∣ a + b` (so `a`, `b` are odd).  The card
`FreyTwoAdicCaseCK1MinimalModelStatement` (`FreyTwoAdicK1RowAnalysis.lean:219`) was parked
because the witness change was not constructed.  Here it is constructed and the card is
proved.

Idea: the shift `x ↦ x + a` moves the root `a` of `y² = x (x - a) (x + b)` to the origin,
giving `y² = x (x + a) (x + c)` with `c = a + b ≡ 0 (mod 16)` and `-a ≡ 3 (mod 4)`, which is
the halving shape of `FreyTwoAdicMinimalReduction`.  The combined change is Mathlib's
`VariableChange ⟨2, a, 1, 0⟩`, i.e. `(x, y) ↦ (4x + a, 8y + 4x)`; the resulting model is the
integral `(1, (c + a - 1)/4, 0, a c / 16, 0)`, its `c₄ = a² + ab + b²` is odd (unit), so it is
minimal, and `Δ = (a b c / 16)²` gives `v₂(Δ_min) = 2 v₂(a + b) - 8`.

(The REPORT §3.2 witness `(2, 1, 1, t)` differs from `(2, a, 1, 0)` by an integral change;
the card is existential in the change, so the shifted witness suffices.)
-/

import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicK1RowAnalysis

noncomputable section

open scoped WeierstrassCurve

namespace LeanFormal.IUT

/-- The case C witness change `(u, r, s, t) = (2, a, 1, 0)`: `(x, y) ↦ (4x + a, 8y + 4x)`. -/
def freyTwoAdicCaseCShiftedHalvingChange (a : ℕ) : WeierstrassCurve.VariableChange ℚ_[2] :=
  ⟨Units.mk0 (2 : ℚ_[2]) (by norm_num), (a : ℚ_[2]), 1, 0⟩

/-- The case C model of the ABC Frey curve at `2`. -/
def freyTwoAdicCaseCShiftedHalvingModel (a b : ℕ) : WeierstrassCurve ℚ_[2] :=
  freyTwoAdicCaseCShiftedHalvingChange a • freyPadicCurve 2 a b

/-- Integrality from the congruences `2a + b - 1 = 4m`, `a (a + b) = 16 n`; the integral
model is `(1, m, 0, n, 0)`. -/
theorem freyTwoAdicCaseCShiftedHalvingModel_isIntegral_of_congruences {a b m n : ℕ}
    (hm : 2 * a + b = 4 * m + 1) (hn : a * (a + b) = 16 * n) :
    WeierstrassCurve.IsIntegral ℤ_[2] (freyTwoAdicCaseCShiftedHalvingModel a b) := by
  refine ⟨⟨⟨1, (m : ℤ_[2]), 0, (n : ℤ_[2]), 0⟩, ?_⟩⟩
  rw [WeierstrassCurve.baseChange]
  have hm' : 2 * (a : ℚ_[2]) + b = 4 * (m : ℚ_[2]) + 1 := by
    have h := congrArg (fun z : ℕ => (z : ℚ_[2])) hm
    push_cast at h
    exact h
  have hn' : (a : ℚ_[2]) * (a + b) = 16 * (n : ℚ_[2]) := by
    have h := congrArg (fun z : ℕ => (z : ℚ_[2])) hn
    push_cast at h
    exact h
  ext
  · simp [WeierstrassCurve.map_a₁, WeierstrassCurve.variableChange_a₁,
      freyTwoAdicCaseCShiftedHalvingModel, freyTwoAdicCaseCShiftedHalvingChange,
      freyPadicCurve]
  · simp [WeierstrassCurve.map_a₂, WeierstrassCurve.variableChange_a₂,
      freyTwoAdicCaseCShiftedHalvingModel, freyTwoAdicCaseCShiftedHalvingChange,
      freyPadicCurve]
    linear_combination (1 / 4 : ℚ_[2]) * hm'
  · simp [WeierstrassCurve.map_a₃, WeierstrassCurve.variableChange_a₃,
      freyTwoAdicCaseCShiftedHalvingModel, freyTwoAdicCaseCShiftedHalvingChange,
      freyPadicCurve]
  · simp [WeierstrassCurve.map_a₄, WeierstrassCurve.variableChange_a₄,
      freyTwoAdicCaseCShiftedHalvingModel, freyTwoAdicCaseCShiftedHalvingChange,
      freyPadicCurve]
    linear_combination (1 / 16 : ℚ_[2]) * hn'
  · simp [WeierstrassCurve.map_a₆, WeierstrassCurve.variableChange_a₆,
      freyTwoAdicCaseCShiftedHalvingModel, freyTwoAdicCaseCShiftedHalvingChange,
      freyPadicCurve]
    ring

/-- `c₄` of the case C model is `a² + ab + b²` (translation invariance, `u⁴ = 16`). -/
theorem freyTwoAdicCaseCShiftedHalvingModel_c₄ (a b : ℕ) :
    (freyTwoAdicCaseCShiftedHalvingModel a b).c₄ =
      ((abcInvariantPolynomial a b : ℕ) : ℚ_[2]) := by
  rw [freyTwoAdicCaseCShiftedHalvingModel, WeierstrassCurve.variableChange_c₄,
    freyPadicCurve_c4_eq_map_integral, freyPadicIntegralModel_two_c4_eq_natCast]
  simp only [abcInvariantPolynomial, map_natCast]
  simp [freyTwoAdicCaseCShiftedHalvingChange]
  ring_nf

/-- Discriminant of the case C model: `Δ = (a b c₁)²` when `a + b = 16 c₁`. -/
theorem freyTwoAdicCaseCShiftedHalvingModel_discriminant {a b c₁ : ℕ}
    (hc : a + b = 16 * c₁) :
    (freyTwoAdicCaseCShiftedHalvingModel a b).Δ = (((a * b * c₁) ^ 2 : ℕ) : ℚ_[2]) := by
  rw [freyTwoAdicCaseCShiftedHalvingModel, WeierstrassCurve.variableChange_Δ,
    freyPadicCurve_discriminant hc]
  simp [freyTwoAdicCaseCShiftedHalvingChange]
  ring_nf

/-- In case C, `a² + ab + b²` is odd. -/
theorem odd_abcInvariantPolynomial_of_odd_odd {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    Odd (abcInvariantPolynomial a b) := by
  rw [abcInvariantPolynomial, Nat.odd_iff]
  simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, ha, hb]

/-- **The case C `k = 1` card is proved.** -/
theorem freyTwoAdicCaseCK1MinimalModelStatement_proved :
    FreyTwoAdicCaseCK1MinimalModelStatement := by
  intro a b htri ha4 h16
  obtain ⟨c₁, hc₁⟩ := h16
  have ha2 : a % 2 = 1 := by omega
  have hb2 : b % 2 = 1 := by omega
  have hc₁0 : c₁ ≠ 0 := by
    have := htri.1
    omega
  refine ⟨freyTwoAdicCaseCShiftedHalvingChange a, ?_⟩
  have hint : WeierstrassCurve.IsIntegral ℤ_[2] (freyTwoAdicCaseCShiftedHalvingModel a b) :=
    freyTwoAdicCaseCShiftedHalvingModel_isIntegral_of_congruences
      (m := (2 * a + b) / 4) (n := a * c₁) (by omega) (by rw [hc₁]; ring)
  have hmin : WeierstrassCurve.IsMinimal ℤ_[2] (freyTwoAdicCaseCShiftedHalvingModel a b) := by
    refine padicWeierstrass_isMinimal_of_c4_valuation_one _ ?_
    rw [freyTwoAdicCaseCShiftedHalvingModel_c₄]
    exact (freyPadicValuation_two_natCast_eq_one_iff _).mpr
      (two_not_dvd_of_odd (odd_abcInvariantPolynomial_of_odd_odd ha2 hb2))
  refine ⟨hint, hmin, ?_⟩
  change freyPadicValuation 2 (freyTwoAdicCaseCShiftedHalvingModel a b).Δ = _
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  rw [freyTwoAdicCaseCShiftedHalvingModel_discriminant hc₁,
    freyPadicValuation_two_natCast_eq_exp_neg_padicValNat
      (pow_ne_zero 2 (Nat.mul_ne_zero (Nat.mul_ne_zero ha0 hb0) hc₁0)), padicValNat.pow]
  have hva : padicValNat 2 a = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  have hvb : padicValNat 2 b = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  have hv16 : padicValNat 2 16 = 4 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]
  have hvabc : padicValNat 2 (a * b * c₁) = padicValNat 2 c₁ := by
    rw [padicValNat.mul (Nat.mul_ne_zero ha0 hb0) hc₁0, padicValNat.mul ha0 hb0, hva, hvb]
    simp
  have hvc : padicValNat 2 (a + b) = 4 + padicValNat 2 c₁ := by
    rw [hc₁, padicValNat.mul (by norm_num) hc₁0, hv16]
  rw [hvabc, hvc]
  congr 3
  omega

end LeanFormal.IUT
