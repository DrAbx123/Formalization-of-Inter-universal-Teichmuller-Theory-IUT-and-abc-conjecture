/-
# A minimality criterion at `2` beyond the two unit criteria, and the parked residual

If an integral Weierstrass model over `ℤ_[p]` satisfies `v₂(c₄) = 4` and no
integral variable change to an integral model has `u` of valuation `exp (-1)`,
then it is minimal (proved for arbitrary prime `p`).  Proof outline: the
`c₄`-formula plus integrality of the changed model forces `log v(u) ≥ -1`;
the hypothesis excludes `log v(u) = -1`; then `log v(u) ≥ 0`, so the
`Δ`-change formula gives `v((C • W).Δ) ≤ v(W.Δ)`.

The `k = 0` residual — no integral change of the displayed abc-Frey model at
`2` has `u` of valuation `exp (-1)` — is PARKED as
`FreyTwoAdicDisplayedModelNoUniformizerChangeStatement`: it is a definition,
not a proof.  The last theorem shows that the parked statement together with
the criterion implies the existing `FreyTwoAdicDisplayedModelMinimalStatement`;
the parked statement is not used as a proved input anywhere.

Literature freeze (statement-level): Silverman, *Advanced Topics in the
Arithmetic of Elliptic Curves*, IV.9 and IV.10; Saito 1988 (cited only).
The `m₂` and `swan₂` exponents are not treated in this file.
-/

import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicMinimalDiscriminantValuation
import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicAdditiveCaseValueCard

noncomputable section

open scoped WeierstrassCurve WithZero

namespace LeanFormal.IUT

/-! ## Partial general criterion and the parked residual -/

/-- A minimality criterion beyond the two unit criteria: if an integral
model has `c₄` of 2-adic valuation `4`, and no integral variable change has
`u` of valuation one, then the model is minimal. -/
theorem padicWeierstrass_isMinimal_of_c4_valuation_exp_neg_four_and_no_uniformizer_change
    {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℚ_[p])
    [hint : WeierstrassCurve.IsIntegral ℤ_[p] W]
    (hc4 : freyPadicValuation p W.c₄ = WithZero.exp (-4))
    (hno : ∀ C : WeierstrassCurve.VariableChange ℚ_[p],
      WeierstrassCurve.IsIntegral ℤ_[p] (C • W) →
      freyPadicValuation p (C.u : ℚ_[p]) ≠ WithZero.exp (-1)) :
    WeierstrassCurve.IsMinimal ℤ_[p] W := by
  constructor
  constructor
  · simpa only [one_smul] using hint
  · intro C hC _
    letI : WeierstrassCurve.IsIntegral ℤ_[p] (C • W) := hC
    have hu_ne : freyPadicValuation p (C.u : ℚ_[p]) ≠ 0 :=
      (Valuation.ne_zero_iff (freyPadicValuation p)).mpr (Units.ne_zero C.u)
    set a : ℤ := WithZero.log (freyPadicValuation p (C.u : ℚ_[p]))
    have hu : freyPadicValuation p (C.u : ℚ_[p]) = WithZero.exp a :=
      (WithZero.exp_log hu_ne).symm
    have hc4change : freyPadicValuation p (C • W).c₄ =
        (freyPadicValuation p (C.u : ℚ_[p]))⁻¹ ^ 4 * WithZero.exp (-4) := by
      rw [WeierstrassCurve.variableChange_c₄, map_mul, map_pow,
        Units.val_inv_eq_inv_val, Valuation.map_inv, hc4]
    have hc4le : freyPadicValuation p (C • W).c₄ ≤ 1 :=
      padicWeierstrass_c4_valuation_le_one (C • W)
    have hc4eq : freyPadicValuation p (C • W).c₄ =
        WithZero.exp (-4 * a - 4) := by
      rw [hc4change, hu]
      rw [← WithZero.exp_neg, ← WithZero.exp_nsmul, ← WithZero.exp_add]
      congr 1
      simp only [nsmul_eq_mul]
      ring
    have ha_ge : -1 ≤ a := by
      have h1 : WithZero.exp (-4 * a - 4) ≤ WithZero.exp (0 : ℤ) := by
        rw [← hc4eq]
        simpa using hc4le
      have h2 := WithZero.exp_le_exp.mp h1
      linarith
    have ha_ne : a ≠ -1 := by
      intro hae
      exact hno C hC (by rw [hu, hae])
    have ha_ge0 : 0 ≤ a := by
      rcases lt_or_eq_of_le ha_ge with hlt | heq
      · omega
      · exact absurd heq.symm ha_ne
    have hinv : (freyPadicValuation p (C.u : ℚ_[p]))⁻¹ ^ 12 ≤ 1 := by
      rw [hu]
      rw [← WithZero.exp_neg, ← WithZero.exp_nsmul]
      rw [← WithZero.exp_zero]
      rw [WithZero.exp_le_exp]
      simp only [nsmul_eq_mul]
      have hneg : -a ≤ 0 := neg_nonpos.mpr ha_ge0
      exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hneg
    have hcomparison : freyPadicValuation p (C • W).Δ ≤
        freyPadicValuation p W.Δ := by
      rw [freyPadicValuation_delta_variableChange p]
      simpa only [one_mul] using mul_le_mul' hinv le_rfl
    change (WeierstrassCurve.valuation_Δ_aux ℤ_[p] (C • W) : ℤᵐ⁰) ≤
      (WeierstrassCurve.valuation_Δ_aux ℤ_[p]
        ((1 : WeierstrassCurve.VariableChange ℚ_[p]) • W) : ℤᵐ⁰)
    simpa only [one_smul, WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral]
      using hcomparison

/-- The precise residual statement (PARK): in the `k = 0` rows of the
displayed Frey family no integral variable change with `u` of valuation one
exists.  This is not proved here. -/
def FreyTwoAdicDisplayedModelNoUniformizerChangeStatement : Prop :=
  ∀ a b : ℕ, IsABCTriple a b (a + b) →
    ¬ ((4 : ℤ) ∣ (b : ℤ) - (a : ℤ) - 1 ∧ (16 : ℤ) ∣ (a : ℤ) * b) →
    ¬ (a % 4 = 1 ∧ 16 ∣ a + b) →
    ∀ C : WeierstrassCurve.VariableChange ℚ_[2],
      WeierstrassCurve.IsIntegral ℤ_[2] (C • freyPadicCurve 2 a b) →
      freyPadicValuation 2 (C.u : ℚ_[2]) ≠ WithZero.exp (-1)

/-- The parked statement, together with the partial criterion, closes the
minimality of the displayed model in the `k = 0` rows. -/
theorem freyTwoAdicDisplayedModelMinimal_of_noUniformizerChange
    (h : FreyTwoAdicDisplayedModelNoUniformizerChangeStatement) :
    FreyTwoAdicDisplayedModelMinimalStatement := by
  intro a b htri hhalving hcaseC
  exact padicWeierstrass_isMinimal_of_c4_valuation_exp_neg_four_and_no_uniformizer_change
    (W := freyPadicCurve 2 a b) (hint := freyPadicCurve_isIntegral 2 a b)
    (freyPadicCurve_two_c4_valuation_eq_exp_neg_four htri)
    (h a b htri hhalving hcaseC)

end LeanFormal.IUT
