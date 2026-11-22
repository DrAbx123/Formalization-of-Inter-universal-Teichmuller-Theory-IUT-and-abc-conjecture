import tmp.sheaf.xif.paper.Mzk1Lemma21RatioEvenActual
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-! # Mzk1Lemma21RatioOddActual — [Mzk1] Lemma 2.1(d), n odd: f0 = |f(r)| pieces (PROVED)

STEP 0 prior-art: corpus Lemma 2.1 lines 44-105 (n odd proof lines 87-105);
Mzk1Lemma21Actual/RealActual/ImageActual, Mzk1Lemma22ProofActual, Mzk1Lemma21RatioActual,
Mzk1Lemma21RatioEvenActual; Mathlib Algebra.Ring.Parity (Odd.neg_pow).

PAPER (n odd): f(x) <= 0 for x in [0,1]; f(r) is the minimum of f on S (S\{∞}),
f0 = |f(r)| and 0 < f0 <= 1/4; then for alpha in {0,1}: (f(beta)+f0)/(f(alpha)+f0)
= (f(beta)+f0)/f0 >= f(beta) >= C.

THIS FILE PROVES (finite real form): the odd sign lemmas, the minimum formula
f0 = -f(r) = |f(r)| under the Lemma 2.1 point conditions, 0 < f0, f0 <= 1, and the
alpha in {0,1} ratio case.  The alpha > 1 dichotomy (f(alpha) >= f0 / f(alpha) <= f0)
and the three-case bound 0 < f0 <= 1/4 (using r = m/(m+n)) remain OPEN. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioOddActual

open Finset
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22ProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioEvenActual

/-- n odd: (x-1)^n = -((1-x)^n). -/
theorem odd_shift_pow (hodd : Odd n) (x : ℝ) : (x - 1) ^ n = -((1 - x) ^ n) := by
  rw [show x - 1 = -(1 - x) by ring, Odd.neg_pow hodd]

theorem belyi21R_nonpos_on_unit (hodd : Odd n) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    belyi21R m n x ≤ 0 := by
  unfold belyi21R
  rw [odd_shift_pow hodd]
  have h1 : 0 ≤ x ^ m := pow_nonneg hx0 m
  have h2 : 0 ≤ (1 - x) ^ n := pow_nonneg (by linarith) n
  nlinarith

theorem belyi21R_neg_of_mem_unit (hodd : Odd n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    belyi21R m n x < 0 := by
  unfold belyi21R
  rw [odd_shift_pow hodd]
  have h1 : 0 < x ^ m := pow_pos hx0 m
  have h2 : 0 < (1 - x) ^ n := pow_pos (by linarith) n
  nlinarith

/-- Under the Lemma 2.1 point conditions with n odd, f(r) is the minimum of f on S,
so f0 = -f(r) = |f(r)|. -/
theorem belyi22f0_eq_neg_of_odd {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hodd : Odd n)
    (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ) (hr : r ∈ S) (hr0 : 0 < r) (hr1 : r < 1)
    (hbig : ∀ α ∈ S, α ≠ 0 → α ≠ 1 → α ≠ r → 1 < α) :
    belyi22f0 (m := m) (n := n) S hS = -belyi21R m n r := by
  have hfr_neg : belyi21R m n r < 0 := belyi21R_neg_of_mem_unit (m := m) (n := n) hodd hr0 hr1
  have hfr_le_all : ∀ α ∈ S, belyi21R m n r ≤ belyi21R m n α := by
    intro α hα
    by_cases hα0 : α = 0
    · subst hα0; rw [belyi21R_zero m n hm]; linarith
    by_cases hα1 : α = 1
    · subst hα1; rw [belyi21R_one m n hn]; linarith
    by_cases hαr : α = r
    · subst hαr; exact le_rfl
    · have hαgt : 1 < α := hbig α hα hα0 hα1 hαr
      have hpos : 0 < belyi21R m n α := belyi21R_pos_of_one_lt (m := m) (n := n) hαgt
      linarith
  have hinf : S.inf' hS (fun x => belyi21R m n x) = belyi21R m n r := by
    have hle : S.inf' hS (fun x => belyi21R m n x) ≤ belyi21R m n r :=
      Finset.inf'_le (fun x => belyi21R m n x) hr
    have hge : belyi21R m n r ≤ S.inf' hS (fun x => belyi21R m n x) :=
      Finset.le_inf' hS (fun x => belyi21R m n x) hfr_le_all
    exact le_antisymm hle hge
  simp [belyi22f0, hinf]

theorem belyi22f0_pos_of_odd {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hodd : Odd n)
    (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ) (hr : r ∈ S) (hr0 : 0 < r) (hr1 : r < 1)
    (hbig : ∀ α ∈ S, α ≠ 0 → α ≠ 1 → α ≠ r → 1 < α) :
    0 < belyi22f0 (m := m) (n := n) S hS := by
  rw [belyi22f0_eq_neg_of_odd hm hn hodd S hS r hr hr0 hr1 hbig]
  have := belyi21R_neg_of_mem_unit (m := m) (n := n) hodd hr0 hr1
  linarith

/-- For n odd, f0 = |f(r)| <= 1 (|f(r)| <= 1 on [0,1]). -/
theorem belyi22f0_le_one_of_odd {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hodd : Odd n)
    (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ) (hr : r ∈ S) (hr0 : 0 < r) (hr1 : r < 1)
    (hbig : ∀ α ∈ S, α ≠ 0 → α ≠ 1 → α ≠ r → 1 < α) :
    belyi22f0 (m := m) (n := n) S hS ≤ 1 := by
  rw [belyi22f0_eq_neg_of_odd hm hn hodd S hS r hr hr0 hr1 hbig]
  have hfr : belyi21R m n r < 0 := belyi21R_neg_of_mem_unit (m := m) (n := n) hodd hr0 hr1
  have hfr_abs : |belyi21R m n r| ≤ 1 := by
    unfold belyi21R
    rw [odd_shift_pow hodd]
    have ha0 : 0 ≤ r := le_of_lt hr0
    have ha1 : r ≤ 1 := le_of_lt hr1
    have h1 : r ^ m ≤ 1 := pow_le_one₀ ha0 ha1
    have h2 : (1 - r) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hpos1 : 0 ≤ r ^ m := pow_nonneg ha0 m
    have hpos2 : 0 ≤ (1 - r) ^ n := pow_nonneg (by linarith) n
    calc |r ^ m * -((1 - r) ^ n)| = r ^ m * (1 - r) ^ n := by
          rw [abs_mul, abs_neg, abs_of_nonneg hpos1, abs_of_nonneg hpos2]
      _ ≤ 1 := by nlinarith
  have : -belyi21R m n r = |belyi21R m n r| := by rw [abs_of_neg hfr]
  rw [this]
  exact hfr_abs

/-- The alpha in {0,1} case of (d): when f(alpha)=0 and 0 < f0 <= 1,
(f(beta)+f0)/f0 >= C. -/
theorem belyi21R_ratio_special {fβ f0 C : ℝ} (hf0pos : 0 < f0) (hf0le : f0 ≤ 1)
    (hC : C ≤ fβ) (hβ0 : 0 ≤ fβ) :
    C ≤ (fβ + f0) / f0 := by
  rw [le_div_iff₀ hf0pos]
  have h1 : C * f0 ≤ fβ * f0 := mul_le_mul_of_nonneg_right hC (le_of_lt hf0pos)
  have h2 : fβ * f0 ≤ fβ + f0 := by nlinarith [hf0le, hf0pos, hβ0]
  linarith

#check belyi22f0_eq_neg_of_odd
#check belyi22f0_pos_of_odd
#check belyi22f0_le_one_of_odd
#check belyi21R_ratio_special

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioOddActual
end
