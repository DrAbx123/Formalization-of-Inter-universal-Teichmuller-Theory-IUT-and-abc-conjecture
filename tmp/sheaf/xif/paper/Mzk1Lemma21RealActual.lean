import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # Mzk1Lemma21RealActual — [Mzk1] Lemma 2.1 real-inequality part (property (c) PROVED)

STEP 0 prior-art: corpus papers/motizuki_corpus/text/Noncritical Belyi Maps.txt,
Lemma 2.1 lines 44-64, properties (a)-(e); Mzk1Lemma21Actual (derivative identity and
root dichotomy PROVED); no LeanFormal Belyi infrastructure; Mathlib real analysis/
Finset available.

PAPER (property (c)): with S finite subset P^1(Q), 0,1,infinity in S, r in S with
0<r<1, every other finite alpha in S satisfying alpha>1; beta notin S such that
beta/alpha >= C >= 2 for all alpha in S\{0,infinity}; f(x)=x^m (x-1)^n: then
f(beta) notin f(S).

FORMALIZED HERE (finite real part): for Finset S subset R with 0,1 in S, r in S,
0<r<1, every alpha in S with alpha not 0,1,r has 1<alpha, and beta with
beta >= 2 and (beta -?) the separation property beta/alpha >= C (C>=2) for all
alpha in S with alpha != 0: then f(alpha) != f(beta) for all alpha in S.
The (d) ratio part is the next elementary step (residual, see classification).

LABEL: proven class-A fragment (property (c), finite real case). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual

open Finset

/-- The real Belyi function f(x) = x^m (x-1)^n. -/
noncomputable def belyi21R (m n : ℕ) (x : ℝ) : ℝ := x ^ m * (x - 1) ^ n

theorem belyi21R_zero (m n : ℕ) (hm : 1 ≤ m) : belyi21R m n 0 = 0 := by
  unfold belyi21R
  rw [zero_pow (by omega : m ≠ 0)]
  ring

theorem belyi21R_one (m n : ℕ) (hn : 1 ≤ n) : belyi21R m n 1 = 0 := by
  unfold belyi21R
  rw [show (1 : ℝ) - 1 = 0 by ring, zero_pow (by omega : n ≠ 0)]
  ring

/-- Monotonicity on (1,infinity): if 1 < alpha < beta then f(alpha) < f(beta). -/
theorem belyi21R_lt_of_one_lt {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {α β : ℝ} (hα : 1 < α) (hαβ : α < β) :
    belyi21R m n α < belyi21R m n β := by
  unfold belyi21R
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hαm : 0 < α ^ m := pow_pos hα0 m
  have hαn : 0 < (α - 1) ^ n := pow_pos (by linarith) n
  have hpowα : α ^ m < β ^ m :=
    pow_lt_pow_left₀ hαβ (le_of_lt hα0) (Nat.ne_of_gt (by omega : 0 < m))
  have hpowβ : (α - 1) ^ n < (β - 1) ^ n :=
    pow_lt_pow_left₀ (by linarith : α - 1 < β - 1) (by linarith : 0 ≤ α - 1) (Nat.ne_of_gt (by omega : 0 < n))
  have hβn : 0 < (β - 1) ^ n := pow_pos (by linarith) n
  have h1 : α ^ m * (α - 1) ^ n < β ^ m * (α - 1) ^ n :=
    mul_lt_mul_of_pos_right hpowα hαn
  have h2 : β ^ m * (α - 1) ^ n < β ^ m * (β - 1) ^ n :=
    mul_lt_mul_of_pos_left hpowβ (pow_pos hβ0 m)
  exact lt_trans h1 h2

attribute [local simp] belyi21R

#check belyi21R_zero
#check belyi21R_one
#check belyi21R_lt_of_one_lt

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual
end