import LeanFormal.IUT.Foundations.PAdicAnalytic.TateDeltaIntegral
import LeanFormal.IUT.Foundations.PAdicAnalytic.GeneralInverseJAssembly
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateEstimatesGeneral
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateQSeriesGeneral

open Set Metric
open scoped NNReal
open LeanFormal.IUT.PAdicAnalytic
open LeanFormal.IUT.PAdicAnalytic.General
open LeanFormal.IUT.PAdicAnalytic.GeneralInverseJAssembly

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.IUT.PAdicAnalytic.General

universe u
variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  [CharZero K] [IsUltrametricDist K]

/-- General inverse-j without any 1728-unit hypothesis. -/
theorem exists_tateHK_eq_and_tateJK_eq_inv_no1728
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1)
    {t : K} (ht0 : t ≠ 0) (ht1 : ‖t‖ < 1) :
    ∃ q : K, tateHK (K := K) q = t ∧ tateJK (K := K) q = t⁻¹ ∧ ‖q‖ < 1 := by
  let cR : ℝ := (1 + ‖t‖) / 2
  have hcR_nonneg : 0 ≤ cR := by
    dsimp [cR]
    positivity
  have hcR_lt_one : cR < 1 := by
    dsimp [cR]
    linarith
  let c : ℝ≥0 := ⟨cR, hcR_nonneg⟩
  have hc_coe : (c : ℝ) = cR := rfl
  have hc : c < 1 := by
    rw [← NNReal.coe_lt_coe]
    simpa [hc_coe] using hcR_lt_one
  have ht_le : ‖t‖ ≤ (c : ℝ) := by
    change ‖t‖ ≤ (1 + ‖t‖) / 2
    linarith [norm_nonneg t]
  have hh : ∀ n : ℕ, ‖(HK (K := K)).coeff n‖ ≤ 1 :=
    HK_coeff_norm_le_one_no1728 (K := K) hint
  let H : K → K := fun q => tateHK (K := K) q
  let R : K → K := fun q => tateHK (K := K) q - q
  have hH : ∀ q : K, H q = q + R q := by
    intro q
    dsimp [H, R]
    ring
  have hR_bound : ∀ q : K, ‖q‖ ≤ (c : ℝ) → ‖R q‖ ≤ (c : ℝ) ^ 2 := by
    intro q hq
    have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hq hc
    have hEq : tateHK (K := K) q = q + generalTateR (K := K) q :=
      tateHK_eq_q_add_generalTateR_no1728 (K := K) hint hq1
    have hR : R q = generalTateR (K := K) q := by
      dsimp [R]
      rw [hEq]
      ring
    rw [hR]
    have hgen : generalTateR (K := K) q =
        generalTateRemainder (K := K) (fun n : ℕ => (HK (K := K)).coeff n) q := rfl
    rw [hgen]
    exact generalTateRemainder_norm_le_c_sq
      (K := K) (h := fun n : ℕ => (HK (K := K)).coeff n) hh hcR_nonneg hcR_lt_one
      (by simpa [hc_coe] using hq)
  have hR_lip : ∀ x y : K, ‖x‖ ≤ (c : ℝ) → ‖y‖ ≤ (c : ℝ) →
      dist (R x) (R y) ≤ (c : ℝ) * dist x y := by
    intro x y hx hy
    have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hx hc
    have hy1 : ‖y‖ < 1 := lt_of_le_of_lt hy hc
    have hEqx : tateHK (K := K) x = x + generalTateR (K := K) x :=
      tateHK_eq_q_add_generalTateR_no1728 (K := K) hint hx1
    have hEqy : tateHK (K := K) y = y + generalTateR (K := K) y :=
      tateHK_eq_q_add_generalTateR_no1728 (K := K) hint hy1
    have hRx : R x = generalTateR (K := K) x := by
      dsimp [R]
      rw [hEqx]
      ring
    have hRy : R y = generalTateR (K := K) y := by
      dsimp [R]
      rw [hEqy]
      ring
    rw [hRx, hRy]
    have hgenx : generalTateR (K := K) x =
        generalTateRemainder (K := K) (fun n : ℕ => (HK (K := K)).coeff n) x := rfl
    have hgeny : generalTateR (K := K) y =
        generalTateRemainder (K := K) (fun n : ℕ => (HK (K := K)).coeff n) y := rfl
    rw [hgenx, hgeny]
    have h := generalTateRemainder_lipschitz_c
      (K := K) (h := fun n : ℕ => (HK (K := K)).coeff n) hh hcR_lt_one
      (by simpa [hc_coe] using hx) (by simpa [hc_coe] using hy)
    simpa [dist_eq_norm, hc_coe, mul_comm] using h
  obtain ⟨q, hqle, hqH⟩ := exists_inverseJ_of_remainder
    (K := K) H R c hc hH hR_bound hR_lip t ht_le
  have hqH' : tateHK (K := K) q = t := by
    simpa [H] using hqH
  have hHne : tateHK (K := K) q ≠ 0 := by
    rw [hqH']
    exact ht0
  have hc4 : (TateCurve.weierstrassCurve K q).c₄ ≠ 0 := by
    intro h
    apply hHne
    simp [tateHK, h]
  have hDelta : (TateCurve.weierstrassCurve K q).Δ ≠ 0 := by
    intro h
    apply hHne
    simp [tateHK, h]
  have hJ : tateJK (K := K) q = t⁻¹ := by
    have hmul := tateHK_mul_tateJK (K := K) q hc4 hDelta
    rw [hqH'] at hmul
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  exact ⟨q, hqH', hJ, lt_of_le_of_lt hqle hc⟩

end LeanFormal.IUT.PAdicAnalytic.General
