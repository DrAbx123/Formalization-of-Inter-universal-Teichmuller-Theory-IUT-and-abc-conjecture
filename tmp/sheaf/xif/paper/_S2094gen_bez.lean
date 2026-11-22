import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def f : (ZMod 29)[X] :=
  monomial 0 (10 : ZMod 29) +
  monomial 1 (24 : ZMod 29) +
  monomial 2 (16 : ZMod 29) +
  monomial 3 (14 : ZMod 29) +
  monomial 4 (24 : ZMod 29) +
  monomial 5 (8 : ZMod 29) +
  monomial 6 (5 : ZMod 29) +
  monomial 7 (7 : ZMod 29) +
  monomial 9 (25 : ZMod 29) +
  monomial 10 (1 : ZMod 29)

def P2 : (ZMod 29)[X] :=
  monomial 0 (3 : ZMod 29) +
  monomial 1 (27 : ZMod 29) +
  monomial 2 (23 : ZMod 29) +
  monomial 3 (6 : ZMod 29) +
  monomial 4 (12 : ZMod 29) +
  monomial 5 (21 : ZMod 29) +
  monomial 6 (26 : ZMod 29) +
  monomial 7 (8 : ZMod 29) +
  monomial 8 (10 : ZMod 29) +
  monomial 9 (26 : ZMod 29)

def P5 : (ZMod 29)[X] :=
  monomial 0 (10 : ZMod 29) +
  monomial 1 (17 : ZMod 29) +
  monomial 2 (23 : ZMod 29) +
  monomial 3 (11 : ZMod 29) +
  monomial 4 (26 : ZMod 29) +
  monomial 5 (27 : ZMod 29) +
  monomial 6 (4 : ZMod 29) +
  monomial 7 (9 : ZMod 29) +
  monomial 8 (8 : ZMod 29) +
  monomial 9 (12 : ZMod 29)

def G2 : (ZMod 29)[X] :=
  monomial 0 (3 : ZMod 29) +
  monomial 1 (26 : ZMod 29) +
  monomial 2 (23 : ZMod 29) +
  monomial 3 (6 : ZMod 29) +
  monomial 4 (12 : ZMod 29) +
  monomial 5 (21 : ZMod 29) +
  monomial 6 (26 : ZMod 29) +
  monomial 7 (8 : ZMod 29) +
  monomial 8 (10 : ZMod 29) +
  monomial 9 (26 : ZMod 29)

def G5 : (ZMod 29)[X] :=
  monomial 0 (10 : ZMod 29) +
  monomial 1 (16 : ZMod 29) +
  monomial 2 (23 : ZMod 29) +
  monomial 3 (11 : ZMod 29) +
  monomial 4 (26 : ZMod 29) +
  monomial 5 (27 : ZMod 29) +
  monomial 6 (4 : ZMod 29) +
  monomial 7 (9 : ZMod 29) +
  monomial 8 (8 : ZMod 29) +
  monomial 9 (12 : ZMod 29)

def A2 : (ZMod 29)[X] :=
  monomial 0 (27 : ZMod 29) +
  monomial 1 (23 : ZMod 29) +
  monomial 2 (4 : ZMod 29) +
  monomial 3 (17 : ZMod 29) +
  monomial 4 (24 : ZMod 29) +
  monomial 5 (24 : ZMod 29) +
  monomial 6 (18 : ZMod 29) +
  monomial 7 (14 : ZMod 29) +
  monomial 8 (13 : ZMod 29)

def B2 : (ZMod 29)[X] :=
  monomial 0 (7 : ZMod 29) +
  monomial 1 (14 : ZMod 29) +
  monomial 2 (25 : ZMod 29) +
  monomial 3 (11 : ZMod 29) +
  monomial 4 (5 : ZMod 29) +
  monomial 5 (8 : ZMod 29) +
  monomial 7 (22 : ZMod 29) +
  monomial 8 (5 : ZMod 29) +
  monomial 9 (14 : ZMod 29)

def A5 : (ZMod 29)[X] :=
  monomial 0 (2 : ZMod 29) +
  monomial 1 (18 : ZMod 29) +
  monomial 2 (24 : ZMod 29) +
  monomial 3 (26 : ZMod 29) +
  monomial 4 (15 : ZMod 29) +
  monomial 5 (11 : ZMod 29) +
  monomial 6 (11 : ZMod 29) +
  monomial 7 (12 : ZMod 29) +
  monomial 8 (17 : ZMod 29)

def B5 : (ZMod 29)[X] :=
  monomial 0 (1 : ZMod 29) +
  monomial 1 (22 : ZMod 29) +
  monomial 2 (11 : ZMod 29) +
  monomial 3 (4 : ZMod 29) +
  monomial 4 (19 : ZMod 29) +
  monomial 5 (23 : ZMod 29) +
  monomial 6 (1 : ZMod 29) +
  monomial 7 (19 : ZMod 29) +
  monomial 8 (4 : ZMod 29) +
  monomial 9 (1 : ZMod 29)

lemma cert_bez2 : A2 * f + B2 * G2 = (1 : (ZMod 29)[X]) := by
  ext k
  by_cases hk : k ≤ 19
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [A2, B2, f, G2, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (A2 * f + B2 * G2).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := A2 * f + B2 * G2)
    have hdeg : (A2 * f + B2 * G2).natDegree < 20 := by
      simp only [A2, B2, f, G2]
      compute_degree!
    omega
  have hR : ((1 : (ZMod 29)[X])).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (1 : (ZMod 29)[X]))
    have hdeg : ((1 : (ZMod 29)[X])).natDegree < 20 := by
      norm_num
    omega
  rw [hL, hR]

lemma cert_bez5 : A5 * f + B5 * G5 = (1 : (ZMod 29)[X]) := by
  ext k
  by_cases hk : k ≤ 19
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [A5, B5, f, G5, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (A5 * f + B5 * G5).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := A5 * f + B5 * G5)
    have hdeg : (A5 * f + B5 * G5).natDegree < 20 := by
      simp only [A5, B5, f, G5]
      compute_degree!
    omega
  have hR : ((1 : (ZMod 29)[X])).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (1 : (ZMod 29)[X]))
    have hdeg : ((1 : (ZMod 29)[X])).natDegree < 20 := by
      norm_num
    omega
  rw [hL, hR]
