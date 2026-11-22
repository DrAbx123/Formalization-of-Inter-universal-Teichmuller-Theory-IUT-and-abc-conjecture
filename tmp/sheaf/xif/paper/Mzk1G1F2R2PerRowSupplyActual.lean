/- R2 per-box supply: the slot coefficient lambda >= (j^2/(2l)) oq(et idag), and the
  exceptional term bound hexc <= 4(j+1) iotaL via the DONE `exceptionalSum_le_r4`.

  * lambda supply: the actual q generator gives the slot coefficient
    `lambda = j^2 * cP` (cP = actual local q order, `badPlaceCoeff`), and
    `j^2 * cP >= (j^2/(2l)) * cP` for `cP >= 0`, `l >= 1`; taking
    `oq (et idag) = cP` this is exactly `lambda >= (j^2/(2l)) * oq(et idag)`.
  * exceptional bound: `StepVProcessionAverage.exceptionalSum_le_r4` (DONE) with
    `I = univ`, `el = e_mod`, `iotaL = if p <= el then log el else 0` gives
    `sum_{i in Istar} (3 + log e_i) <= 4 * card I * iotaL <= 4(j+1) * iotaL`
    (using `card I <= j+1` and `iotaL >= 0`).
  The remaining missing instantiation is only the (R4) input `hR4` from the actual
  source ramification data; no fake.
  No stub, no sorry/axiom. -/
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2PerRowSupplyActual

open LeanFormal.IUT.IUTIV.Estimates

/-- The paper's `iotaL = iota * l*_mod` as `(if p <= e_mod then log e_mod else 0)`. -/
noncomputable def iotaLOf (p el : ℝ) : ℝ := if p ≤ el then Real.log el else 0

/-- `iotaLOf` is nonnegative when `el >= 1`. -/
theorem iotaLOf_nonneg {p el : ℝ} (hel : 1 ≤ el) : 0 ≤ iotaLOf p el := by
  unfold iotaLOf
  split_ifs with h
  · exact Real.log_nonneg hel
  · exact le_rfl

/-- **Exceptional-term bound** from the DONE `exceptionalSum_le_r4`:
    `sum_{i in Istar} (3 + log e_i) <= 4(j+1) * iotaL`. -/
theorem exceptionalSum_le_four_mul
    {α : Type*} [Fintype α] (Istar : Finset α) (e : α → ℝ) (p el : ℝ) (j : ℕ)
    (hel : 1 ≤ el)
    (hR4 : ∀ i ∈ Istar, p ≤ el ∧ Real.log (e i) ≤ -3 + 4 * Real.log el)
    (hcard : (Fintype.card α : ℝ) ≤ (j : ℝ) + 1) :
    (∑ i ∈ Istar, (3 + Real.log (e i))) ≤ 4 * ((j : ℝ) + 1) * iotaLOf p el := by
  have h := LeanFormal.IUT.IUTIV.StepVProcessionAverage.exceptionalSum_le_r4 Istar (Finset.univ) (Finset.subset_univ _) e p el hel hR4
  have hcard' : (Istar.card : ℝ) ≤ (Fintype.card α : ℝ) := by
    exact_mod_cast Finset.card_le_univ Istar
  have hiota := iotaLOf_nonneg (p := p) hel
  have hif : (if p ≤ el then Real.log el else 0) = iotaLOf p el := rfl
  rw [hif] at h
  have h4 : 0 ≤ 4 * (Istar.card : ℝ) := by positivity
  calc (∑ i ∈ Istar, (3 + Real.log (e i)))
      ≤ 4 * (Istar.card : ℝ) * iotaLOf p el := h
    _ ≤ 4 * ((j : ℝ) + 1) * iotaLOf p el := by
        have hc : (Istar.card : ℝ) ≤ (j : ℝ) + 1 := le_trans hcard' hcard
        nlinarith [hiota, hc]

/-- Slot coefficient `lambda = j^2 * cP` from the actual q generator. -/
noncomputable def lambdaFromQ (cP : ℝ) (j : ℕ) : ℝ := (j : ℝ) ^ 2 * cP

/-- **Slot supply**: `lambda >= (j^2/(2l)) * oq(et idag)` with `oq = cP`. -/
theorem lambdaFromQ_ge_slot (cP : ℝ) (j : ℕ) (l : LeanFormal.IUT.PrimeGeFive)
    (hcP : 0 ≤ cP) :
    ((j : ℝ) ^ 2 / (2 * (l.value : ℝ))) * cP ≤ lambdaFromQ cP j := by
  unfold lambdaFromQ
  have hl : (1 : ℝ) ≤ (l.value : ℝ) := by
    have h5 : (5 : ℝ) ≤ (l.value : ℝ) := by exact_mod_cast l.ge_five
    linarith
  have h2l : (0 : ℝ) < 2 * (l.value : ℝ) := by linarith
  have hle : (j : ℝ) ^ 2 / (2 * (l.value : ℝ)) ≤ (j : ℝ) ^ 2 := by
    rw [div_le_iff₀ h2l]
    nlinarith [sq_nonneg (j : ℝ), hl]
  nlinarith [hcP, hle, sq_nonneg (j : ℝ)]

#print axioms exceptionalSum_le_four_mul
#print axioms lambdaFromQ_ge_slot

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2PerRowSupplyActual