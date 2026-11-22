import tmp.sheaf.xif.paper.Mzk1Lemma22ProofActual
import Mathlib.Tactic

/-! # Mzk1Lemma21RatioActual — [Mzk1] Lemma 2.1(d) ratio work (alpha > 1, nonnegative-min case)

STEP 0 prior-art: corpus papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.1
lines 44-64, property (d) and estimate (e); Mzk1Lemma21RealActual (monotonicity and
zero/one values PROVED), Mzk1Lemma21ImageActual (property (c) PROVED),
Mzk1Lemma22ProofActual (f0 normalization PROVED); Mathlib pow/mul lemmas reused.

PAPER (d): with f0 := -min_{alpha in S} f(alpha) (see belyi22f0), for alpha in S,
alpha != infinity, with f(alpha)+f0 != 0:  (f(beta)+f0)/(f(alpha)+f0) >= C.

THIS FILE PROVES the multiplicative and shifted inequalities in the case
alpha > 1 with f0 <= 0 (i.e. min_{S} f >= 0, the nonnegative-min case):
* belyi21R_mul_ge_of_one_lt_sep: if 1 < alpha < beta, 1 <= C <= beta/alpha and
  m,n >= 1, then C * f(alpha) <= f(beta)   (this is the paper's estimate (e) chain
  f(beta)/f(alpha) >= (beta/alpha)^2 >= beta/alpha >= C in the form used for (d));
* belyi21R_ratio_shifted_of_one_lt_nonneg: hence for f0 <= 0,
  C * (f(alpha)+f0) <= f(beta)+f0  (the (d) inequality for alpha > 1).

HONEST: the remaining cases alpha = r in (0,1) and the general min sign
(f0 possibly positive) are NOT covered here; they stay in the obligation ledger of
Mzk1Lemma22ProofActual.  No fake proof. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual

/-- The paper's estimate (e) chain, shift-free form: for 1 < alpha < beta and
1 <= C <= beta/alpha, f(beta) >= C * f(alpha). -/
theorem belyi21R_mul_ge_of_one_lt_sep {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {α β C : ℝ} (hα1 : 1 < α) (hαβ : α < β) (hC1 : 1 ≤ C) (hCβ : C ≤ β / α) :
    C * belyi21R m n α ≤ belyi21R m n β := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have hCα : C * α ≤ β := (le_div_iff₀ hα0).mp hCβ
  have hβm : β ≤ β ^ m := by
    calc β = β ^ 1 := by ring
      _ ≤ β ^ m := pow_le_pow_right₀ hβ1 hm
  have hαm : α ≤ α ^ m := by
    calc α = α ^ 1 := by ring
      _ ≤ α ^ m := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ α) hm
  have hsub0 : 0 ≤ α - 1 := by linarith
  have hsub : α - 1 ≤ β - 1 := by linarith
  have hp : (α - 1) ^ n ≤ (β - 1) ^ n := pow_le_pow_left₀ hsub0 hsub n
  have hαn0 : 0 ≤ (α - 1) ^ n := pow_nonneg hsub0 n
  have hβn0 : 0 ≤ (β - 1) ^ n := pow_nonneg (by linarith : 0 ≤ β - 1) n
  have hCα0 : 0 ≤ C * α := by positivity
  have hβmpow : (C * α) ^ m ≤ β ^ m := pow_le_pow_left₀ hCα0 hCα m
  rw [mul_pow] at hβmpow
  have hCm : C ≤ C ^ m := by
    calc C = C ^ 1 := by ring
      _ ≤ C ^ m := pow_le_pow_right₀ hC1 hm
  have hCαm : C * α ^ m ≤ C ^ m * α ^ m := by
    have := mul_le_mul_of_nonneg_right hCm (pow_nonneg (le_of_lt hα0) m)
    nlinarith
  have hkey : C * α ^ m ≤ β ^ m := by nlinarith [hβmpow, hCαm]
  have hstep1 : C * α ^ m * (α - 1) ^ n ≤ β ^ m * (α - 1) ^ n := by
    have := mul_le_mul_of_nonneg_right hkey hαn0
    nlinarith
  have hstep2 : β ^ m * (α - 1) ^ n ≤ β ^ m * (β - 1) ^ n :=
    mul_le_mul_of_nonneg_left hp (pow_nonneg (le_of_lt hβ0) m)
  unfold belyi21R
  nlinarith [hstep1, hstep2]
/-- Shift lemma: a multiplicative lower bound transfers to the f0-shifted ratio when
f0 <= 0 and C >= 1. -/
theorem shift_ratio_of_le {fα fβ f0 C : ℝ}
    (h : C * fα ≤ fβ) (hf0 : f0 ≤ 0) (hC : 1 ≤ C) :
    C * (fα + f0) ≤ fβ + f0 := by nlinarith

/-- The (d) inequality in the case alpha > 1, f0 <= 0. -/
theorem belyi21R_ratio_shifted_of_one_lt_nonneg {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {α β C f0 : ℝ} (hα1 : 1 < α) (hαβ : α < β) (hC1 : 1 ≤ C)
    (hCβ : C ≤ β / α) (hf0 : f0 ≤ 0) :
    C * (belyi21R m n α + f0) ≤ belyi21R m n β + f0 :=
  shift_ratio_of_le
    (belyi21R_mul_ge_of_one_lt_sep hm hn hα1 hαβ hC1 hCβ) hf0 hC1

#check belyi21R_mul_ge_of_one_lt_sep
#check belyi21R_ratio_shifted_of_one_lt_nonneg

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioActual
end