import tmp.sheaf.xif.paper.Mzk1Lemma21dEvenActual
import Mathlib.Tactic

/-! # Mzk1Lemma21dOddActual — [Mzk1] Lemma 2.1(d), n-odd case ASSEMBLED (PROVED)

STEP 0 prior-art: corpus Lemma 2.1 lines 87-105; components GREEN+CITABLE:
Mzk1Lemma21RatioOddActual (f0=-f(r)=|f(r)|, 0<f0, f0<=1, alpha{0,1} special),
Mzk1Lemma21RatioDichotomyActual (alpha>1 dichotomy), Mzk1Lemma21RatioSquaredActual
(squared estimate), Mzk1Lemma21RatioQuarterActual (f0<=1/4 via r=m/(m+n)).

THIS FILE assembles the n-odd case of (d) into one theorem mzk1Lemma21_d_odd. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21dOddActual

open Finset
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22ProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioOddActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioEvenActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioDichotomyActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioSquaredActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioQuarterActual

/-- f(beta) >= beta for beta >= 2 and m,n >= 1. -/
theorem belyi21R_ge_self {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {β : ℝ} (hβ2 : 2 ≤ β) :
    β ≤ belyi21R m n β := by
  have hβ1 : (1 : ℝ) ≤ β := by linarith
  unfold belyi21R
  calc β = β ^ 1 := by ring
    _ ≤ β ^ m := pow_le_pow_right₀ hβ1 hm
    _ ≤ β ^ m * (β - 1) ^ n := by
        have h1 : (1 : ℝ) ≤ (β - 1) ^ n := one_le_pow₀ (by linarith)
        have h2 : 0 < β ^ m := pow_pos (by linarith) m
        nlinarith

/-- n-odd case of Lemma 2.1(d) (finite real form), assembled. -/
theorem mzk1Lemma21_d_odd {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hodd : Odd n)
    (S : Finset ℝ) (β r C : ℝ) (hS : S.Nonempty)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (hr : r ∈ S) (hr0 : 0 < r) (hr1 : r < 1)
    (hbig : ∀ α ∈ S, α ≠ 0 → α ≠ 1 → α ≠ r → 1 < α)
    (hr_eq : r = (m : ℝ) / ((m + n : ℕ) : ℝ))
    (hC2 : 2 ≤ C) (hsep : ∀ α ∈ S, α ≠ 0 → C ≤ β / α) :
    ∀ α ∈ S, α ≠ 0 → α ≠ 1 →
      belyi21R m n α + belyi22f0 (m := m) (n := n) S hS ≠ 0 →
      C ≤ (belyi21R m n β + belyi22f0 (m := m) (n := n) S hS) /
          (belyi21R m n α + belyi22f0 (m := m) (n := n) S hS) := by
  have hC1 : (1 : ℝ) ≤ C := le_trans (by norm_num) hC2
  have hC0 : (0 : ℝ) ≤ C := le_trans (by norm_num) hC2
  have hf0eq : belyi22f0 (m := m) (n := n) S hS = -belyi21R m n r :=
    belyi22f0_eq_neg_of_odd hm hn hodd S hS r hr hr0 hr1 hbig
  have hfrneg : belyi21R m n r < 0 :=
    belyi21R_neg_of_mem_unit (m := m) (n := n) hodd hr0 hr1
  have hf0pos : 0 < belyi22f0 (m := m) (n := n) S hS := by
    rw [hf0eq]; linarith
  have hf0le1 : belyi22f0 (m := m) (n := n) S hS ≤ 1 :=
    belyi22f0_le_one_of_odd hm hn hodd S hS r hr hr0 hr1 hbig
  have hf0quarter : belyi22f0 (m := m) (n := n) S hS ≤ 1 / 4 := by
    rw [hf0eq]
    have hneg : -belyi21R m n r = r ^ m * (1 - r) ^ n := by
      unfold belyi21R
      rw [odd_shift_pow hodd]
      ring
    rw [hneg]
    have h1mr : (1 : ℝ) - r = (n : ℝ) / ((m + n : ℕ) : ℝ) := by
      rw [hr_eq]
      field_simp
      push_cast
      ring
    rw [h1mr, hr_eq]
    exact belyi22_f0_quarter m n hm hn
  have hβC : C ≤ β := by
    have h := hsep 1 h1 (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  have hβ2 : 2 ≤ β := le_trans hC2 hβC
  have hβnonneg : 0 ≤ belyi21R m n β := le_trans (le_of_lt (by linarith : (0:ℝ) < β)) (belyi21R_ge_self hm hn hβ2)
  have hfβC : C ≤ belyi21R m n β := le_trans hβC (belyi21R_ge_self hm hn hβ2)
  intro α hα hα0 hα1 hden
  by_cases hαr : α = r
  · have hzero : belyi21R m n r + belyi22f0 (m := m) (n := n) S hS = 0 := by
      rw [hf0eq]; ring
    rw [hαr] at hden
    exact absurd hzero hden
  · have hαgt : 1 < α := hbig α hα hα0 hα1 hαr
    have hαpos : 0 < α := by linarith
    have hfαpos : 0 < belyi21R m n α :=
      belyi21R_pos_of_one_lt (m := m) (n := n) hαgt
    have hαposden : 0 < belyi21R m n α + belyi22f0 (m := m) (n := n) S hS := by linarith
    have hsepα : C ≤ β / α := hsep α hα hα0
    have hCα : C * α ≤ β := (le_div_iff₀ hαpos).mp hsepα
    have hαβ : α < β := by nlinarith
    have hsq := belyi21R_ratio_ge_sq hm hn hαgt hαβ
    have hbase : (1 : ℝ) ≤ β / α := by
      rw [le_div_iff₀ hαpos]
      linarith
    have hCsq : C ^ 2 ≤ (β / α) ^ 2 := pow_le_pow_left₀ hC0 hsepα 2
    have hbα : 2 * C ≤ (β / α) ^ 2 := by nlinarith [hCsq, hC2]
    have hC2fα : 2 * C * belyi21R m n α ≤ belyi21R m n β := by
      have h := mul_le_mul_of_nonneg_right hbα (le_of_lt hfαpos)
      nlinarith [hsq]
    by_cases hcase : belyi22f0 (m := m) (n := n) S hS ≤ belyi21R m n α
    · exact ratio_ge_of_f0_le_falpha hαposden (le_of_lt hf0pos) hcase hC0 hC2fα
    · have hcase2 : belyi21R m n α ≤ belyi22f0 (m := m) (n := n) S hS := le_of_not_ge hcase
      exact ratio_ge_of_falpha_le_f0 hαposden hf0pos hf0quarter hcase2 hβnonneg hC0 hfβC

#check belyi21R_ge_self
#check mzk1Lemma21_d_odd

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21dOddActual
end
