/-
# Paper Step (v) display: coefficient lemmas (IUT IV L1757-1763)

The full display identity (proved in a later batch) is

  (1/n) * sum_{j in Icc 1 n} collectionBound (2n+1) D Q S T j
    = (l+5)/4*D - (l+1)/24*Q + S + (l+5)*T,     l = 2n+1.

This file proves the four coefficient components that make it up, so the letter
dictionary is grep-able independently of the full identity:

* sum_{j=1..n}(j+1) = n(n+3)/2        => (1/n)*... = (l+5)/4;
* sum_{j=1..n} j^2   = n(n+1)(2n+1)/6 => (1/n)*sum j^2/(2l) = (l+1)/24;
* sum_{j=1..n} 4(j+1) = 4*n(n+3)/2    => (1/n)*... = l+5;
* sum_{j=1..n} S = n*S (constant slot).

Letters: D = log dK, Q = log q, S = log p (donor collection slot), T = lstar =
l*_mod*log(s<=).
-/
import tmp.sheaf.xif.paper.Mzk1P6StepVAveragesActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULStepVDisplayIdentityActual

open LeanFormal.IUT.IUTIV.StepVProcessionAverage

/-- Sum of (j:ℝ)+1 over j in Icc 1 n: n(n+3)/2. -/
theorem sum_Icc_one_add (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, ((j : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 3) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring

/-- Sum of (j:ℝ)^2 over j in Icc 1 n: n(n+1)(2n+1)/6. -/
theorem sum_Icc_sq (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, (j : ℝ) ^ 2)
      = (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring

/-- Sum of 4(j+1) over j in Icc 1 n: 2n(n+3) = 4*(n(n+3)/2). -/
theorem sum_Icc_four_one_add (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, 4 * ((j : ℝ) + 1)) = 4 * ((n : ℝ) * ((n : ℝ) + 3) / 2) := by
  rw [← Finset.mul_sum, sum_Icc_one_add]

/-- Paper coefficient check 1: (1/n) * sum_{j=1..n} (j+1) = (l+5)/4 for l = 2n+1. -/
theorem paperDisplay_coefficient_D {n : ℕ} (hn : 0 < n) {l : ℝ} (hl : l = 2 * (n : ℝ) + 1) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n, ((j : ℝ) + 1)) = (l + 5) / 4 := by
  rw [sum_Icc_one_add, hl]
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  field_simp
  ring

/-- Paper coefficient check 2: (1/n) * sum_{j=1..n} j^2/(2l) = (l+1)/24 for l = 2n+1. -/
theorem paperDisplay_coefficient_Q {n : ℕ} (hn : 0 < n) {l : ℝ} (hl : l = 2 * (n : ℝ) + 1) :
    (1 / (n : ℝ)) * ((∑ j ∈ Finset.Icc 1 n, (j : ℝ) ^ 2) / (2 * l)) = (l + 1) / 24 := by
  rw [sum_Icc_sq, hl]
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  have hlne : (2 * (2 * (n : ℝ) + 1)) ≠ 0 := by positivity
  field_simp
  ring

/-- Paper coefficient check 3: (1/n) * sum_{j=1..n} 4(j+1) = l+5 for l = 2n+1. -/
theorem paperDisplay_coefficient_T {n : ℕ} (hn : 0 < n) {l : ℝ} (hl : l = 2 * (n : ℝ) + 1) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n, 4 * ((j : ℝ) + 1)) = l + 5 := by
  rw [sum_Icc_four_one_add, hl]
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  field_simp
  ring

/-- Sum of a constant over Icc 1 n is n*S. -/
theorem sum_Icc_const (n : ℕ) (S : ℝ) :
    (∑ _j ∈ Finset.Icc 1 n, S) = (n : ℝ) * S := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring

/-- Paper coefficient check 4 (constant slot): (1/n) * sum_{j=1..n} S = S. -/
theorem paperDisplay_coefficient_S (n : ℕ) (hn : 0 < n) (S : ℝ) :
    (1 / (n : ℝ)) * (∑ _j ∈ Finset.Icc 1 n, S) = S := by
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  rw [sum_Icc_const]
  field_simp

#print axioms sum_Icc_one_add
#print axioms sum_Icc_sq
#print axioms sum_Icc_four_one_add
#print axioms paperDisplay_coefficient_D
#print axioms paperDisplay_coefficient_Q
#print axioms paperDisplay_coefficient_T
#print axioms sum_Icc_const
#print axioms paperDisplay_coefficient_S

end LeanFormal.IUT.XiFPaper.Mzk1ULStepVDisplayIdentityActual
end