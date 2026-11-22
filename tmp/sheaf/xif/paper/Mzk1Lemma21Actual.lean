import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-! # Mzk1Lemma21Actual — [Mzk1] Lemma 2.1 core algebraic facts (PROVED)

STEP 0 prior-art: corpus papers/motizuki_corpus/text/Noncritical Belyi Maps.txt
Lemma 2.1 lines 44-64; no LeanFormal Belyi infrastructure (deep search); Mathlib
Polynomial.derivative API only.  This file proves the derivative identity and the
root dichotomy used by the paper's argument; the remaining real-inequality parts
(paper properties (c),(d)) are the next elementary step.

PAPER: f(x) = x^m * (x-1)^n, r = m/(m+n); property (b): f'(x)=0 (x in C) implies
x in {0, r, 1} (up to the standard identifications).

LABEL: proven class-A fragment (no paper-input claim). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21Actual

open Polynomial

/-- The Belyi polynomial f(x) = x^m (x-1)^n over Q. -/
def belyi21 (m n : ℕ) : ℚ[X] :=
  X ^ m * (X - C 1) ^ n

/-- Derivative identity: f'(x) = x^(m-1) (x-1)^(n-1) ((m+n)x - m). -/
theorem belyi21_derivative (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    derivative (belyi21 m n) =
      X ^ (m - 1) * (X - C 1) ^ (n - 1) * (C ((m + n : ℕ) : ℚ) * X - C (m : ℚ)) := by
  unfold belyi21
  rw [derivative_mul, derivative_X_pow, derivative_X_sub_C_pow]
  have hpow1 : (X : ℚ[X]) ^ m = (X : ℚ[X]) ^ (m - 1) * (X : ℚ[X]) := by
    conv_lhs => rw [show m = m - 1 + 1 by omega]
    rw [pow_succ]
  have hpow2 : ((X : ℚ[X]) - C 1) ^ n = ((X : ℚ[X]) - C 1) ^ (n - 1) * ((X : ℚ[X]) - C 1) := by
    conv_lhs => rw [show n = n - 1 + 1 by omega]
    rw [pow_succ]
  have hcast : ((m + n : ℕ) : ℚ) = (m : ℚ) + (n : ℚ) := by
    push_cast
    ring
  rw [hpow1, hpow2, hcast, map_add]
  ring_nf
  simp

/-- Root dichotomy over C: f'(x) = 0 implies x = 0, x = 1, or (m+n)x = m. -/
theorem belyi21_derivative_root {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {x : ℂ} (h : (Polynomial.aeval x) (derivative (belyi21 m n)) = 0) :
    x = 0 ∨ x = 1 ∨ ((m + n : ℕ) : ℂ) * x = (m : ℂ) := by
  rw [belyi21_derivative m n hm hn] at h
  simp only [map_mul, map_pow, map_sub, map_add, aeval_X, aeval_C, map_one] at h
  have h' : x ^ (m - 1) * (x - 1) ^ (n - 1) * (((m + n : ℕ) : ℂ) * x - (m : ℂ)) = 0 := by
    simpa [mul_assoc] using h
  rcases mul_eq_zero.mp h' with h1 | h3
  · rcases mul_eq_zero.mp h1 with h0 | h2
    · by_cases hm1 : m = 1
      · subst hm1; simp at h0
      · have hm2 : 1 ≤ m - 1 := by omega
        exact Or.inl (pow_eq_zero_iff (by omega : m - 1 ≠ 0) |>.mp h0)
    · by_cases hn1 : n = 1
      · subst hn1; simp at h2
      · have hn2 : 1 ≤ n - 1 := by omega
        have hx : x - 1 = 0 := pow_eq_zero_iff (by omega : n - 1 ≠ 0) |>.mp h2
        exact Or.inr (Or.inl (sub_eq_zero.mp hx))
  · have hx : ((m + n : ℕ) : ℂ) * x - (m : ℂ) = 0 := h3
    exact Or.inr (Or.inr (sub_eq_zero.mp hx))

#check belyi21_derivative
#check belyi21_derivative_root

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21Actual
end