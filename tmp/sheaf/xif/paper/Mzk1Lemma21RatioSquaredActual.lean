import tmp.sheaf.xif.paper.Mzk1Lemma21RatioDichotomyActual
import Mathlib.Tactic

/-! # Mzk1Lemma21RatioSquaredActual — [Mzk1] Lemma 2.1(d)/estimate (e): squared bound

STEP 0 prior-art: corpus Lemma 2.1 lines 77-81 (property (e): f(beta)/f(alpha) >=
(beta/alpha)^2); Mzk1Lemma21RatioActual (estimate (e) chain), Mzk1Lemma21RatioDichotomyActual
(arithmetic dichotomy).  No fake: this file proves the squared estimate from the exact
factorization f(beta)/f(alpha) = (beta/alpha)^m * ((beta-1)/(alpha-1))^n.

PAPER (e): for alpha > 1, f(beta)/f(alpha) = (beta/alpha)^m * ((beta-1)/(alpha-1))^n
>= (beta/alpha)^{m+n} >= (beta/alpha)^2 >= beta/alpha >= C.  The middle inequality uses
(beta-1)/(alpha-1) >= beta/alpha. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioSquaredActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual

/-- Exact factorization of the f-ratio as a product of the two base ratios. -/
theorem belyi21R_ratio_factor {m n : ℕ} {α β : ℝ} (hα0 : α ≠ 0) (hα1 : α ≠ 1)
    (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) :
    belyi21R m n β / belyi21R m n α = (β / α) ^ m * ((β - 1) / (α - 1)) ^ n := by
  unfold belyi21R
  have hnz1 : α ^ m ≠ 0 := pow_ne_zero m hα0
  have hnz2 : (α - 1) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hα1)
  have hnz3 : β ^ m ≠ 0 := pow_ne_zero m hβ0
  have hnz4 : (β - 1) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hβ1)
  rw [div_pow, div_pow]
  field_simp [hnz1, hnz2, hnz3, hnz4]

/-- Squared estimate (e): for 1 < alpha < beta and m,n >= 1,
(beta/alpha)^2 * f(alpha) <= f(beta). -/
theorem belyi21R_ratio_ge_sq {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {α β : ℝ} (hα1 : 1 < α) (hαβ : α < β) :
    (β / α) ^ 2 * belyi21R m n α ≤ belyi21R m n β := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hαne0 : α ≠ 0 := ne_of_gt hα0
  have hαne1 : α ≠ 1 := by intro h; linarith
  have hβne0 : β ≠ 0 := ne_of_gt hβ0
  have hβne1 : β ≠ 1 := by intro h; linarith
  have hratio := belyi21R_ratio_factor (m := m) (n := n) hαne0 hαne1 hβne0 hβne1
  have hfαpos : 0 < belyi21R m n α := by
    unfold belyi21R
    exact mul_pos (pow_pos hα0 m) (pow_pos (by linarith) n)
  have hbase1 : (1 : ℝ) ≤ β / α := by
    rw [le_div_iff₀ hα0]
    linarith
  have hbase2 : (1 : ℝ) ≤ (β - 1) / (α - 1) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < α - 1)]
    linarith
  have hbase3 : β / α ≤ (β - 1) / (α - 1) := by
    rw [div_le_iff₀ hα0]
    have hdiv : (β - 1) / (α - 1) * α = (β - 1) * α / (α - 1) := by ring
    rw [hdiv]
    rw [le_div_iff₀ (by linarith : (0:ℝ) < α - 1)]
    nlinarith
  have h1 : β / α ≤ (β / α) ^ m := by
    calc β / α = (β / α) ^ 1 := by ring
      _ ≤ (β / α) ^ m := pow_le_pow_right₀ hbase1 hm
  have h2 : (β - 1) / (α - 1) ≤ ((β - 1) / (α - 1)) ^ n := by
    calc (β - 1) / (α - 1) = ((β - 1) / (α - 1)) ^ 1 := by ring
      _ ≤ ((β - 1) / (α - 1)) ^ n := pow_le_pow_right₀ hbase2 hn
  have ha0 : 0 ≤ β / α := le_of_lt (by positivity)
  have hb0 : 0 ≤ (β - 1) / (α - 1) := le_of_lt (by positivity)
  have hb1 : 0 ≤ (β / α) ^ m := pow_nonneg ha0 m
  have hstep1 : (β / α) * (β / α) ≤ (β / α) * ((β - 1) / (α - 1)) :=
    mul_le_mul_of_nonneg_left hbase3 ha0
  have hstep2 : (β / α) * ((β - 1) / (α - 1)) ≤
      (β / α) ^ m * ((β - 1) / (α - 1)) ^ n :=
    mul_le_mul h1 h2 hb0 hb1
  have hprod : (β / α) ^ 2 ≤ (β / α) ^ m * ((β - 1) / (α - 1)) ^ n := by
    calc (β / α) ^ 2 = (β / α) * (β / α) := by ring
      _ ≤ (β / α) * ((β - 1) / (α - 1)) := hstep1
      _ ≤ (β / α) ^ m * ((β - 1) / (α - 1)) ^ n := hstep2
  have hmul := mul_le_mul_of_nonneg_right hprod (le_of_lt hfαpos)
  rw [← hratio, div_mul_cancel₀ _ (ne_of_gt hfαpos)] at hmul
  exact hmul

#check belyi21R_ratio_factor
#check belyi21R_ratio_ge_sq

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioSquaredActual
end
