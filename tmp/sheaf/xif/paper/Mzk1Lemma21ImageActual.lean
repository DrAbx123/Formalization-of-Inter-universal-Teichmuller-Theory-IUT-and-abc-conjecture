import tmp.sheaf.xif.paper.Mzk1Lemma21RealActual
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! # Mzk1Lemma21ImageActual — [Mzk1] Lemma 2.1 property (c) (finite real form)

STEP 0 prior-art: corpus papers/motizuki_corpus/text/Noncritical Belyi Maps.txt,
Lemma 2.1 lines 44-64 (properties (a)-(e)); Mzk1Lemma21Actual (derivative identity +
root dichotomy PROVED); Mzk1Lemma21RealActual (monotonicity on (1,inf), zero/one
values PROVED, with m,n>=1 side hypotheses); no LeanFormal Belyi infrastructure.

PAPER (c): with S finite subset P^1(Q) containing 0,1,infinity, r in S with
0<r<1, every other finite alpha in S satisfying alpha>1; beta notin S with
beta/alpha >= C >= 2 for all alpha in S\{0,infinity}: f(beta) notin f(S), where
f(x)=x^m (x-1)^n.

FORMALIZED (finite real part): if 0,1,r in S, 0<r<1, every alpha in S with
alpha not 0,1,r has 1<alpha, beta>=2, and beta/alpha>=2 for all alpha in S with
alpha != 0, then f(alpha) != f(beta) for all alpha in S.  (The hypotheses beta>=2,
beta/alpha>=2 are the C>=2 specialization derived from the paper's hypotheses when
1 in S; the general-C form is a straightforward weakening.)

LABEL: proven class-A fragment (property (c)). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21ImageActual

open Finset
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual

/-- Property (c), finite real form. -/
theorem belyi21R_not_mem_image {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Finset ℝ) (β r : ℝ)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (hr : r ∈ S) (hr0 : 0 < r) (hr1 : r < 1)
    (hbig : ∀ α ∈ S, α ≠ 0 → α ≠ 1 → α ≠ r → 1 < α)
    (hβ2 : 2 ≤ β)
    (hsep : ∀ α ∈ S, α ≠ 0 → β / α ≥ 2) :
    ∀ α ∈ S, belyi21R m n α ≠ belyi21R m n β := by
  intro α hα
  have hβpos : 0 < β := by linarith
  have hfβ2 : 2 ≤ belyi21R m n β := by
    unfold belyi21R
    have hβm : 2 ≤ β ^ m := by
      calc (2 : ℝ) ≤ β := hβ2
        _ = β ^ 1 := by ring
        _ ≤ β ^ m := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ β) hm
    have hβn : 1 ≤ (β - 1) ^ n := one_le_pow₀ (by linarith : (1 : ℝ) ≤ β - 1)
    have hβnpos : 0 < (β - 1) ^ n := by linarith
    nlinarith [hβm, hβn, hβnpos]
  have hfβ : 1 < belyi21R m n β := by linarith
  by_cases hα0 : α = 0
  · rw [hα0, belyi21R_zero m n hm]
    linarith
  by_cases hα1 : α = 1
  · rw [hα1, belyi21R_one m n hn]
    linarith
  by_cases hαr : α = r
  · rw [hαr]
    have habs_le : |belyi21R m n r| ≤ 1 := by
      unfold belyi21R
      have ha0 : 0 ≤ r := le_of_lt hr0
      have ha1 : r ≤ 1 := le_of_lt hr1
      have hb0 : 0 ≤ 1 - r := by linarith
      have hb1 : 1 - r ≤ 1 := by linarith
      have hp1 : r ^ m ≤ 1 := pow_le_one₀ ha0 ha1
      have hp2 : (1 - r) ^ n ≤ 1 := pow_le_one₀ hb0 hb1
      have habs : |r - 1| = 1 - r := by
        rw [abs_of_neg (by linarith)]
        ring
      have hprod : r ^ m * |(r - 1) ^ n| ≤ 1 := by
        rw [abs_pow, habs]
        exact mul_le_one₀ hp1 (pow_nonneg hb0 n) hp2
      have habs2 : |r ^ m * (r - 1) ^ n| = r ^ m * |(r - 1) ^ n| := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 m)]
      rw [← habs2] at hprod
      exact hprod
    have hle : belyi21R m n r ≤ 1 := le_trans (le_abs_self _) habs_le
    intro heq
    rw [← heq] at hfβ
    linarith
  · have hαgt : 1 < α := hbig α hα hα0 hα1 hαr
    have hαβ : α < β := by
      have hsepα := hsep α hα hα0
      have hαpos : 0 < α := by linarith
      have h2α : 2 * α ≤ β := by
        have := mul_le_mul_of_nonneg_right hsepα (le_of_lt hαpos)
        rw [div_mul_cancel₀ _ hαpos.ne'] at this
        linarith
      nlinarith
    have hlt := belyi21R_lt_of_one_lt hm hn hαgt hαβ
    exact ne_of_lt hlt

#check belyi21R_not_mem_image

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21ImageActual
end