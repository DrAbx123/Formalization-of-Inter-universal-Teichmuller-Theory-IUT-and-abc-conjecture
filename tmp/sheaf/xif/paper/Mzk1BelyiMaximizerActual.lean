/-
# Mzk1BelyiMaximizerActual — uniqueness of the maximizer of the Belyi polynomial

For m, n >= 1 and rational x in (0,1), the Belyi polynomial
B_{m,n}(x) = ((m+n)^(m+n)/(m^m n^n)) x^m (1-x)^n takes the value 1 exactly at the
normalized maximizer x = m/(m+n):

    B_{m,n}(x) = 1  iff  (m+n) x = m.

This is the key lemma needed to remove the "uniqueness of the maximizer" blocker in
Mzk1BetaAvoidingReductionActual (branch B_{m,n}(u) = 1 for the rational u = A(beta) in (0,1)
forced by the affine normalization).

## Route

The elementary weighted AM-GM bound gives, for real x in (0,1),

    x^m (1-x)^n <= (m/(m+n))^m (n/(m+n))^n,

with equality exactly when (m+n) x = m. Multiplying by the (positive) normalizing
constant and using TauCeti.eval_div_belyiPolynomial (the value at m/(m+n) is 1)
turns this into B_{m,n}(x) <= 1 with equality exactly at the maximizer. The rational and
complex statements are transported from the real one along Q -> R and Q -> C.

## Main declarations

* belyiPolynomial_eval_div_eq_one: re-export of the normalization identity B(m/(m+n)) = 1.
* belyi_max_lt: strict AM-GM bound off the maximizer.
* belyi_max_ineq: the weighted AM-GM inequality used.
* belyi_max_eq_iff: equality case of that inequality.
* eval_belyiPolynomial_lt_one / eval_belyiPolynomial_le_one: B_{m,n}(x) < 1 off the
  maximizer and B_{m,n}(x) <= 1 on (0,1).
* belyiPolynomial_eval_eq_one_iff_real: the exact-value statement over R.
* belyiPolynomial_eval_eq_one_iff: the requested statement over Q.
* belyiPolynomial_eval_eq_one_iff_complex: the same statement over C for rational
  points (the form consumed by the critical-value machinery).
* BelyiMaximizerStatement / belyiMaximizerStatement_proved: the named (formerly open)
  statement of the STEP-0 skeleton, now proved.

No sorry, no new axioms, no PUnit/True placeholders.
-/
import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

open Polynomial
open TauCeti

namespace LeanFormal.IUT.XiFPaper.Mzk1BelyiMaximizerActual

/-- The normalization identity B_{m,n}(m/(m+n)) = 1 (ported theorem, re-exported). -/
theorem belyiPolynomial_eval_div_eq_one {K : Type*} [Field K] [CharZero K] (m n : ℕ) :
    (belyiPolynomial K m n).eval ((m : K) / ((m : K) + n)) = 1 :=
  eval_div_belyiPolynomial (K := K) m n

/-- Formerly-named uniqueness statement of the STEP-0 skeleton (now proved by
belyiMaximizerStatement_proved). -/
def BelyiMaximizerStatement : Prop :=
  ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ x : ℝ, 0 < x → x < 1 →
    ((belyiPolynomial ℝ m n).eval x = 1 ↔ ((m : ℝ) + (n : ℝ)) * x = (m : ℝ))

/-- **Strict weighted-AM-GM bound off the maximizer.**  For m, n >= 1 and real x in (0,1)
with (m+n) x != m,

    x^m (1-x)^n < (m/(m+n))^m (n/(m+n))^n.

Proof: write p = m/(m+n), q = n/(m+n), u = x/p, v = (1-x)/q; then p u + q v = 1 and
u != v, so (strict) weighted AM-GM gives u^p v^q < 1. Raising to the (m+n)-th power gives
u^m v^n < 1, i.e. x^m (1-x)^n < p^m q^n. -/
theorem belyi_max_lt (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hne : ((m + n : ℕ) : ℝ) * x ≠ (m : ℝ)) :
    x ^ m * (1 - x) ^ n <
      ((m : ℝ) / ((m : ℝ) + n)) ^ m * ((n : ℝ) / ((m : ℝ) + n)) ^ n := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr : (0 : ℝ) < (m : ℝ) + n := by linarith
  set p : ℝ := (m : ℝ) / ((m : ℝ) + n) with hp
  set q : ℝ := (n : ℝ) / ((m : ℝ) + n) with hq
  have hp_pos : 0 < p := by rw [hp]; exact div_pos hmR hr
  have hq_pos : 0 < q := by rw [hq]; exact div_pos hnR hr
  have hpq : p + q = 1 := by
    rw [hp, hq]
    field_simp
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hq_ne : q ≠ 0 := hq_pos.ne'
  set u : ℝ := x / p with hu_def
  set v : ℝ := (1 - x) / q with hv_def
  have hu_nonneg : 0 ≤ u := (div_pos hx0 hp_pos).le
  have hv_nonneg : 0 ≤ v := (div_pos (by linarith : (0 : ℝ) < 1 - x) hq_pos).le
  have hsum : p * u + q * v = 1 := by
    rw [hu_def, hv_def]
    field_simp
    ring
  have hpm : ((m + n : ℕ) : ℝ) * p = (m : ℝ) := by
    push_cast
    rw [hp]
    field_simp
  have huv_iff : u = v ↔ x = p := by
    rw [hu_def, hv_def, div_eq_div_iff hp_ne hq_ne]
    constructor
    · intro h
      linear_combination h - x * hpq
    · intro hx
      rw [hx]
      calc p * q = p * (1 - p) := by rw [show q = 1 - p by linarith [hpq]]
        _ = (1 - p) * p := by ring
  have huv_ne : u ≠ v := by
    intro huv
    exact hne (by rw [huv_iff.mp huv]; exact hpm)
  have hAGM : u ^ p * v ^ q < 1 := by
    have h := (Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos hp_pos hq_pos hu_nonneg
      hv_nonneg hpq).mpr huv_ne
    rwa [hsum] at h
  have hWnonneg : 0 ≤ u ^ p * v ^ q :=
    mul_nonneg (Real.rpow_nonneg hu_nonneg p) (Real.rpow_nonneg hv_nonneg q)
  have hpow : (u ^ p * v ^ q) ^ ((m : ℝ) + n) < 1 := by
    have h := Real.rpow_lt_rpow hWnonneg hAGM hr
    rwa [Real.one_rpow] at h
  have hpu : p * ((m : ℝ) + n) = (m : ℝ) := by rw [hp]; field_simp
  have hqv : q * ((m : ℝ) + n) = (n : ℝ) := by rw [hq]; field_simp
  have hW : (u ^ p * v ^ q) ^ ((m : ℝ) + n) = u ^ m * v ^ n := by
    rw [Real.mul_rpow (Real.rpow_nonneg hu_nonneg p) (Real.rpow_nonneg hv_nonneg q)]
    rw [← Real.rpow_mul hu_nonneg p ((m : ℝ) + n),
      ← Real.rpow_mul hv_nonneg q ((m : ℝ) + n), hpu, hqv, Real.rpow_natCast,
      Real.rpow_natCast]
  rw [hW] at hpow
  have hconv : u ^ m * v ^ n = (x ^ m * (1 - x) ^ n) / (p ^ m * q ^ n) := by
    have h1 : (x / p) ^ m = x ^ m / p ^ m := by rw [div_pow]
    have h2 : ((1 - x) / q) ^ n = (1 - x) ^ n / q ^ n := by rw [div_pow]
    rw [hu_def, hv_def, h1, h2, div_mul_div_comm]
  rw [hconv] at hpow
  have hpos : 0 < p ^ m * q ^ n := mul_pos (pow_pos hp_pos m) (pow_pos hq_pos n)
  rw [div_lt_one hpos] at hpow
  simpa only [hp, hq] using hpow

/-- **Weighted-AM-GM bound.**  For m, n >= 1 and real x in (0,1),
x^m (1-x)^n <= (m/(m+n))^m (n/(m+n))^n. -/
theorem belyi_max_ineq (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ m * (1 - x) ^ n ≤
      ((m : ℝ) / ((m : ℝ) + n)) ^ m * ((n : ℝ) / ((m : ℝ) + n)) ^ n := by
  have hr : (0 : ℝ) < (m : ℝ) + n := by
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  rcases eq_or_ne (((m + n : ℕ) : ℝ) * x) (m : ℝ) with h | h
  · have hmn : ((m : ℝ) + n) ≠ 0 := hr.ne'
    have hx : x = (m : ℝ) / ((m : ℝ) + n) := by
      rw [eq_div_iff hmn]
      push_cast at h
      rw [mul_comm]
      exact h
    have h1p : 1 - (m : ℝ) / ((m : ℝ) + n) = (n : ℝ) / ((m : ℝ) + n) := by
      field_simp
      ring
    rw [hx, h1p]
  · exact (belyi_max_lt m n hm hn hx0 hx1 h).le

/-- **Equality case of the weighted-AM-GM bound.**  For m, n >= 1 and real x in (0,1),
the bound x^m (1-x)^n <= (m/(m+n))^m (n/(m+n))^n is an equality exactly at the maximizer
x = m/(m+n). -/
theorem belyi_max_eq_iff (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ m * (1 - x) ^ n =
        ((m : ℝ) / ((m : ℝ) + n)) ^ m * ((n : ℝ) / ((m : ℝ) + n)) ^ n ↔
      ((m + n : ℕ) : ℝ) * x = (m : ℝ) := by
  have hr : (0 : ℝ) < (m : ℝ) + n := by
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  constructor
  · intro h
    by_contra hne
    have hlt := belyi_max_lt m n hm hn hx0 hx1 hne
    rw [h] at hlt
    exact lt_irrefl _ hlt
  · intro h
    have hmn : ((m : ℝ) + n) ≠ 0 := hr.ne'
    have hx : x = (m : ℝ) / ((m : ℝ) + n) := by
      rw [eq_div_iff hmn]
      push_cast at h
      rw [mul_comm]
      exact h
    have h1p : 1 - (m : ℝ) / ((m : ℝ) + n) = (n : ℝ) / ((m : ℝ) + n) := by
      field_simp
      ring
    rw [hx, h1p]

/-- **Off the maximizer the Belyi polynomial is strictly below one.** -/
theorem eval_belyiPolynomial_lt_one (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hne : ((m + n : ℕ) : ℝ) * x ≠ (m : ℝ)) :
    (belyiPolynomial ℝ m n).eval x < 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr : (0 : ℝ) < (m : ℝ) + n := by linarith
  set C : ℝ := ((m : ℝ) + n) ^ (m + n) / ((m : ℝ) ^ m * (n : ℝ) ^ n) with hC
  have hCpos : 0 < C := by
    rw [hC]
    exact div_pos (pow_pos hr _) (mul_pos (pow_pos hmR _) (pow_pos hnR _))
  have hBform : ∀ y : ℝ, (belyiPolynomial ℝ m n).eval y = C * (y ^ m * (1 - y) ^ n) := by
    intro y
    rw [eval_belyiPolynomial, hC]
    ring
  have hone : C * (((m : ℝ) / ((m : ℝ) + n)) ^ m * ((n : ℝ) / ((m : ℝ) + n)) ^ n) = 1 := by
    have h := eval_div_belyiPolynomial (K := ℝ) m n
    rw [hBform] at h
    have h1 : 1 - (m : ℝ) / ((m : ℝ) + n) = (n : ℝ) / ((m : ℝ) + n) := by
      field_simp
      ring
    rwa [h1] at h
  rw [hBform x]
  calc C * (x ^ m * (1 - x) ^ n)
      < C * (((m : ℝ) / ((m : ℝ) + n)) ^ m * ((n : ℝ) / ((m : ℝ) + n)) ^ n) :=
        mul_lt_mul_of_pos_left (belyi_max_lt m n hm hn hx0 hx1 hne) hCpos
    _ = 1 := hone

/-- **The Belyi polynomial is at most one on (0,1).** -/
theorem eval_belyiPolynomial_le_one (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    (belyiPolynomial ℝ m n).eval x ≤ 1 := by
  by_cases hne : ((m + n : ℕ) : ℝ) * x = (m : ℝ)
  · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hr : (0 : ℝ) < (m : ℝ) + n := by
      have : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    have hmn : ((m : ℝ) + n) ≠ 0 := hr.ne'
    have hx : x = (m : ℝ) / ((m : ℝ) + n) := by
      rw [eq_div_iff hmn]
      push_cast at hne
      rw [mul_comm]
      exact hne
    rw [hx]
    exact (eval_div_belyiPolynomial (K := ℝ) m n).le
  · exact (eval_belyiPolynomial_lt_one m n hm hn hx0 hx1 hne).le

/-- **Uniqueness of the maximizer over the reals.**  For m, n >= 1 and real x in (0,1),
B_{m,n}(x) = 1 exactly at x = m/(m+n), i.e. exactly when (m+n) x = m. -/
theorem belyiPolynomial_eval_eq_one_iff_real (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    (belyiPolynomial ℝ m n).eval x = 1 ↔ ((m + n : ℕ) : ℝ) * x = (m : ℝ) := by
  constructor
  · intro h
    by_contra hne
    have hlt := eval_belyiPolynomial_lt_one m n hm hn hx0 hx1 hne
    rw [h] at hlt
    exact lt_irrefl _ hlt
  · intro h
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hr : (0 : ℝ) < (m : ℝ) + n := by
      have : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith
    have hmn : ((m : ℝ) + n) ≠ 0 := hr.ne'
    have hx : x = (m : ℝ) / ((m : ℝ) + n) := by
      rw [eq_div_iff hmn]
      push_cast at h
      rw [mul_comm]
      exact h
    rw [hx]
    exact eval_div_belyiPolynomial (K := ℝ) m n

/-- **Uniqueness of the maximizer over the rationals** (the requested lemma).  For m, n >= 1
and rational x in (0,1), B_{m,n}(x) = 1 exactly when (m+n) x = m. -/
theorem belyiPolynomial_eval_eq_one_iff (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (x : ℚ)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (belyiPolynomial ℚ m n).eval x = 1 ↔ ((m + n : ℕ) : ℚ) * x = (m : ℚ) := by
  constructor
  · intro h
    have hx0R : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
    have hx1R : (x : ℝ) < 1 := by exact_mod_cast hx1
    have hmap : (belyiPolynomial ℝ m n).eval (x : ℝ) =
        (((belyiPolynomial ℚ m n).eval x : ℚ) : ℝ) := by
      have h := Polynomial.eval_map_apply (f := algebraMap ℚ ℝ) (x := x)
        (p := belyiPolynomial ℚ m n)
      simpa using h
    have hreal : (belyiPolynomial ℝ m n).eval (x : ℝ) = 1 := by
      rw [hmap, h]
      norm_num
    have h' := (belyiPolynomial_eval_eq_one_iff_real m n hm hn hx0R hx1R).mp hreal
    have h'' : ((m : ℚ) + n) * x = (m : ℚ) := by
      apply Rat.cast_injective (α := ℝ)
      push_cast at h' ⊢
      exact h'
    simpa only [Nat.cast_add] using h''
  · intro h
    have h' : ((m : ℚ) + n) * x = (m : ℚ) := by
      push_cast at h ⊢
      exact h
    have hmQ : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
    have hnQ : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    have hmn : ((m : ℚ) + n) ≠ 0 := by linarith
    have hx : x = (m : ℚ) / ((m : ℚ) + n) := by
      rw [eq_div_iff hmn, mul_comm]
      exact h'
    rw [hx]
    exact eval_div_belyiPolynomial (K := ℚ) m n

/-- **Uniqueness of the maximizer over the complex numbers, at rational points.**  For
m, n >= 1 and rational x in (0,1), B_{m,n}(x) = 1 in C exactly when (m+n) x = m. -/
theorem belyiPolynomial_eval_eq_one_iff_complex (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (x : ℚ)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (belyiPolynomial ℂ m n).eval (x : ℂ) = 1 ↔ ((m + n : ℕ) : ℂ) * (x : ℂ) = (m : ℂ) := by
  have hmap : (belyiPolynomial ℂ m n).eval (x : ℂ) =
      (((belyiPolynomial ℚ m n).eval x : ℚ) : ℂ) := by
    have h := Polynomial.eval_map_apply (f := algebraMap ℚ ℂ) (x := x)
      (p := belyiPolynomial ℚ m n)
    simpa using h
  rw [hmap]
  constructor
  · intro h
    have h' : (belyiPolynomial ℚ m n).eval x = 1 := by
      apply Rat.cast_injective (α := ℂ)
      rw [Rat.cast_one]
      exact h
    have h'' := (belyiPolynomial_eval_eq_one_iff m n hm hn x hx0 hx1).mp h'
    push_cast
    exact_mod_cast h''
  · intro h
    have h' : ((m + n : ℕ) : ℚ) * x = (m : ℚ) := by
      apply Rat.cast_injective (α := ℂ)
      push_cast at h ⊢
      exact h
    have h'' := (belyiPolynomial_eval_eq_one_iff m n hm hn x hx0 hx1).mpr h'
    rw [h'']
    norm_num

/-- The STEP-0 named statement BelyiMaximizerStatement, proved. -/
theorem belyiMaximizerStatement_proved : BelyiMaximizerStatement := by
  intro m n hm hn x hx0 hx1
  have h := belyiPolynomial_eval_eq_one_iff_real m n hm hn hx0 hx1
  simpa [Nat.cast_add] using h

/-- Recovery rows: every entry is now PROVED. -/
def belyiMaximizerRows : List (String × String × String) :=
  [ ("normalization identity B(r)=1", "A", "PROVED belyiPolynomial_eval_div_eq_one (ported eval_div_belyiPolynomial)")
  , ("weighted AM-GM bound x^m(1-x)^n <= (m/(m+n))^m(n/(m+n))^n", "A", "PROVED belyi_max_ineq / belyi_max_lt / belyi_max_eq_iff")
  , ("(0,1) unique maximizer B(x)=1 iff (m+n)x=m over R", "A", "PROVED belyiPolynomial_eval_eq_one_iff_real / eval_belyiPolynomial_le_one / eval_belyiPolynomial_lt_one")
  , ("transfer to Q (requested form)", "A", "PROVED belyiPolynomial_eval_eq_one_iff")
  , ("transfer to C at rational points", "A", "PROVED belyiPolynomial_eval_eq_one_iff_complex")
  , ("STEP-0 named statement", "A", "PROVED belyiMaximizerStatement_proved") ]

theorem belyiMaximizerRows_length : belyiMaximizerRows.length = 6 := rfl

#check belyiPolynomial_eval_eq_one_iff
#check belyiMaximizerStatement_proved

end LeanFormal.IUT.XiFPaper.Mzk1BelyiMaximizerActual
end
