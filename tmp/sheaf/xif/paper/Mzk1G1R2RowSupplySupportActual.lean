/- R2 support (corrected): actual exceptional-slot bound and the arithmetic bridge from the
Step (v) paperBound to `collectionChoiceBound`. REUSE (DONE):
- `LeanFormal.IUT.IUTIV.StepVProcessionAverage.exceptionalSum_le_r4`
  (`∑ i∈Istar (3+log e_i) ≤ 4|I|·(if p≤el then log el else 0)`),
- `Mzk1G1F2R2PerRowSupplyActual.lambdaFromQ_ge_slot` shape: `(j²/(2l))·oq ≤ λ`.
CORRECTION vs `Mzk1G1F2R2PerRowBoundArithActual`: the needed hypothesis direction for
`(-lam+dsum+1)logp+exc ≤ (-(j²/(2l))oqj+dsum'+1)logp+4(j+1)iota` is
`-lam ≤ -((j²/(2l))·oqj)` (i.e. `lam ≥ (j²/(2l))oqj`, exactly what the q-generator supplies),
NOT `-((j²/(2l))oqj) ≤ -lam`. The latter is the wrong direction (that file's `linarith` failure).
`dsum` identification: the `d`-sum comparison `dsum ≤ dsum'` (row d-vector vs the d of the
collection choice) stays an explicit hypothesis (the actual instantiation from local different
is the remaining source-data input). No fake. -/
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R2RowSupplySupportActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage

/-- The paper's `iotaL = iota * l*_mod` as `(if p ≤ e_mod then log e_mod else 0)`. -/
noncomputable def iotaLOf (p el : ℝ) : ℝ := if p ≤ el then Real.log el else 0

theorem iotaLOf_nonneg {p el : ℝ} (hel : 1 ≤ el) : 0 ≤ iotaLOf p el := by
  unfold iotaLOf
  split_ifs with h
  · exact Real.log_nonneg hel
  · exact le_rfl

/-- **Exceptional-term bound** from the DONE `exceptionalSum_le_r4`. -/
theorem exceptionalSum_le_four_mul
    {α : Type*} [Fintype α] (Istar : Finset α) (e : α → ℝ) (p el : ℝ) (j : ℕ)
    (hel : 1 ≤ el)
    (hR4 : ∀ i ∈ Istar, p ≤ el ∧ Real.log (e i) ≤ -3 + 4 * Real.log el)
    (hcard : (Fintype.card α : ℝ) ≤ (j : ℝ) + 1) :
    (∑ i ∈ Istar, (3 + Real.log (e i))) ≤ 4 * ((j : ℝ) + 1) * iotaLOf p el := by
  have h := exceptionalSum_le_r4 (Finset.univ : Finset α) Istar (Finset.subset_univ Istar) e p el hel hR4
  have hcard' : (Istar.card : ℝ) ≤ (Fintype.card α : ℝ) := by
    exact_mod_cast Finset.card_le_univ Istar
  have hiota := iotaLOf_nonneg (p := p) hel
  have hif : (if p ≤ el then Real.log el else 0) = iotaLOf p el := rfl
  rw [hif] at h
  calc (∑ i ∈ Istar, (3 + Real.log (e i)))
      ≤ 4 * (Fintype.card α : ℝ) * iotaLOf p el := by
          simpa [Finset.card_univ] using h
    _ ≤ 4 * ((j : ℝ) + 1) * iotaLOf p el := by
        have hc : (Istar.card : ℝ) ≤ (j : ℝ) + 1 := le_trans hcard' hcard
        nlinarith [hiota, hc]

/-- **Arithmetic bridge with the corrected slot direction**: from the Step (v) paperBound
shape to the collectionChoiceBound shape. -/
theorem paperBound_le_collectionChoiceBound
    (l logp iotaL lam dsum exc oqj dsum' : ℝ) (j : ℕ)
    (hlogp : 0 ≤ logp)
    (hlam : -lam ≤ -(((j : ℝ) ^ 2 / (2 * l)) * oqj))
    (hD : dsum ≤ dsum')
    (hexc : exc ≤ 4 * ((j : ℝ) + 1) * iotaL) :
    (-lam + dsum + 1) * logp + exc ≤
      (-(((j : ℝ) ^ 2 / (2 * l)) * oqj) + dsum' + 1) * logp + 4 * ((j : ℝ) + 1) * iotaL := by
  have h1 : -lam + dsum + 1 ≤ -(((j : ℝ) ^ 2 / (2 * l)) * oqj) + dsum' + 1 := by
    linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hlogp
  linarith

/-- Row-volume form. -/
theorem rowV_le_collectionChoiceBound
    (V l logp iotaL lam dsum exc oqj dsum' : ℝ) (j : ℕ)
    (hlogp : 0 ≤ logp)
    (hV : V ≤ (-lam + dsum + 1) * logp + exc)
    (hlam : -lam ≤ -(((j : ℝ) ^ 2 / (2 * l)) * oqj))
    (hD : dsum ≤ dsum')
    (hexc : exc ≤ 4 * ((j : ℝ) + 1) * iotaL) :
    V ≤ (-(((j : ℝ) ^ 2 / (2 * l)) * oqj) + dsum' + 1) * logp + 4 * ((j : ℝ) + 1) * iotaL :=
  le_trans hV (paperBound_le_collectionChoiceBound l logp iotaL lam dsum exc oqj dsum' j
    hlogp hlam hD hexc)

/-- Slot supply: the q-generator coefficient `(j²/(2l))·oq` is at most `j²·cP = lambda`. -/
theorem lambdaFromQ_ge_slot (cP : ℝ) {l : ℕ} (hl : 5 ≤ l) (j : ℕ) (hcP : 0 ≤ cP) :
    ((j : ℝ) ^ 2 / (2 * (l : ℝ))) * cP ≤ (j : ℝ) ^ 2 * cP := by
  have hlr : (5 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hl1 : (1 : ℝ) ≤ 2 * (l : ℝ) := by linarith
  have h2l : (0 : ℝ) < 2 * (l : ℝ) := by linarith
  have hle : (j : ℝ) ^ 2 / (2 * (l : ℝ)) ≤ (j : ℝ) ^ 2 := by
    rw [div_le_iff₀ h2l]
    nlinarith [sq_nonneg (j : ℝ), hl1, mul_nonneg (sq_nonneg (j : ℝ)) (sub_nonneg.mpr hl1)]
  exact mul_le_mul_of_nonneg_right hle hcP

#print axioms exceptionalSum_le_four_mul
#print axioms paperBound_le_collectionChoiceBound
#print axioms rowV_le_collectionChoiceBound
#print axioms lambdaFromQ_ge_slot
end LeanFormal.IUT.XiFPaper.Mzk1G1R2RowSupplySupportActual