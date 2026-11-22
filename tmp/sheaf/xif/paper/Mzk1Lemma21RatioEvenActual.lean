import tmp.sheaf.xif.paper.Mzk1Lemma21RatioActual
import tmp.sheaf.xif.paper.Mzk1Lemma22ProofActual
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-! # Mzk1Lemma21RatioEvenActual — [Mzk1] Lemma 2.1(d), n even case (PROVED)

STEP 0 prior-art: corpus Lemma 2.1 lines 44-105; Mzk1Lemma21Actual (derivative/root
dichotomy), Mzk1Lemma21RealActual (zero/one values, monotonicity), Mzk1Lemma21ImageActual
(property (c)), Mzk1Lemma22ProofActual (f0 normalization), Mzk1Lemma21RatioActual
(estimate (e) chain + shift); Mathlib Algebra.Parity (Even.pow_nonneg, Even.neg_pow).

PAPER proof of (d) for n even (lines 82-86): f(x) >= 0 for x in [0,1]; f(0)=0, hence
f0 = 0.  For alpha > 1 in S: f(beta)/f(alpha) >= beta/alpha >= C.  For alpha = r:
0 < f(r) <= 1, so f(beta)/f(r) >= f(beta) >= beta >= C.  alpha = 0,1 have
f(alpha)+f0 = 0 and are excluded.

THIS FILE PROVES the n-even case of (d) (finite real form): f0 = 0, and the ratio
bounds for alpha > 1 and alpha = r.  n odd case (f0 = |f(r)| <= 1/4) remains open. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioEvenActual

open Finset
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22ProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioActual

variable {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)

theorem belyi21R_pos_of_one_lt {α : ℝ} (hα : 1 < α) : 0 < belyi21R m n α := by
  unfold belyi21R
  exact mul_pos (pow_pos (by linarith) m) (pow_pos (by linarith) n)

theorem belyi21R_nonneg_on_unit (hne : Even n) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ belyi21R m n x := by
  unfold belyi21R
  exact mul_nonneg (pow_nonneg hx0 m) (Even.pow_nonneg hne (x - 1))

theorem belyi21R_pos_of_mem_unit (hne : Even n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < belyi21R m n x := by
  unfold belyi21R
  exact mul_pos (pow_pos hx0 m) (Even.pow_pos hne (by linarith))

theorem belyi22f0_eq_zero_of_even {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hne : Even n)
    (S : Finset ℝ) (hS : S.Nonempty)
    (h0 : 0 ∈ S)
    (hbig : ∀ α ∈ S, α ≠ 0 → α ≠ 1 → 1 < α) :
    belyi22f0 (m := m) (n := n) S hS = 0 := by
  have hnonneg : ∀ α ∈ S, 0 ≤ belyi21R m n α := by
    intro α hα
    by_cases hα0 : α = 0
    · subst hα0; rw [belyi21R_zero m n hm]
    by_cases hα1 : α = 1
    · subst hα1; rw [belyi21R_one m n hn]
    by_cases hα2 : 0 < α ∧ α < 1
    · exact belyi21R_nonneg_on_unit (m := m) (n := n) hne (le_of_lt hα2.1) (le_of_lt hα2.2)
    · have hαgt : 1 < α := hbig α hα hα0 hα1
      exact le_of_lt (belyi21R_pos_of_one_lt (m := m) (n := n) hαgt)
  have hmin0 : S.inf' hS (fun x => belyi21R m n x) = 0 := by
    have hle : S.inf' hS (fun x => belyi21R m n x) ≤ 0 := by
      have h := Finset.inf'_le (s := S) (f := fun x => belyi21R m n x) h0
      rwa [belyi21R_zero m n hm] at h
    have hge : 0 ≤ S.inf' hS (fun x => belyi21R m n x) :=
      Finset.le_inf' hS (fun x => belyi21R m n x) (fun α hα => hnonneg α hα)
    exact le_antisymm hle hge
  unfold belyi22f0
  rw [hmin0]
  ring

theorem belyi21R_div_ge_of_one_lt_sep {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {α β C : ℝ} (hα1 : 1 < α) (hαβ : α < β)
    (hC1 : 1 ≤ C) (hCβ : C ≤ β / α) :
    C ≤ belyi21R m n β / belyi21R m n α := by
  have hαpos : 0 < belyi21R m n α := belyi21R_pos_of_one_lt (m := m) (n := n) hα1
  rw [le_div_iff₀ hαpos]
  exact belyi21R_mul_ge_of_one_lt_sep hm hn hα1 hαβ hC1 hCβ

theorem belyi21R_div_ge_of_eq_r {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hne : Even n)
    {r β C : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hC1 : 1 ≤ C) (hC : C ≤ β) (hβ2 : 2 ≤ β) :
    C ≤ belyi21R m n β / belyi21R m n r := by
  have hfr_pos : 0 < belyi21R m n r := belyi21R_pos_of_mem_unit (m := m) (n := n) hne hr0 hr1
  have hfr_le : belyi21R m n r ≤ 1 := by
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
    exact (abs_le.mp hprod).2
  have hβm : β ≤ belyi21R m n β := by
    unfold belyi21R
    calc β = β ^ 1 := by ring
      _ ≤ β ^ m := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ β) hm
      _ ≤ β ^ m * (β - 1) ^ n := by
          have h1 : (1 : ℝ) ≤ (β - 1) ^ n := one_le_pow₀ (by linarith)
          nlinarith [pow_pos (by linarith : (0:ℝ) < β) m, h1]
  rw [le_div_iff₀ hfr_pos]
  have hCf : C * belyi21R m n r ≤ C * 1 := by
    exact mul_le_mul_of_nonneg_left hfr_le (by linarith : (0:ℝ) ≤ C)
  have hCfβ : C ≤ belyi21R m n β := le_trans hC hβm
  nlinarith

#check belyi22f0_eq_zero_of_even
#check belyi21R_div_ge_of_one_lt_sep
#check belyi21R_div_ge_of_eq_r

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioEvenActual
end
