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

def P1 : (ZMod 29)[X] :=
  monomial 0 (13 : ZMod 29) +
  monomial 1 (1 : ZMod 29) +
  monomial 2 (26 : ZMod 29) +
  monomial 3 (24 : ZMod 29) +
  monomial 4 (4 : ZMod 29) +
  monomial 5 (10 : ZMod 29) +
  monomial 6 (25 : ZMod 29) +
  monomial 7 (23 : ZMod 29) +
  monomial 8 (18 : ZMod 29) +
  monomial 9 (20 : ZMod 29)

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

def P3 : (ZMod 29)[X] :=
  monomial 0 (7 : ZMod 29) +
  monomial 1 (23 : ZMod 29) +
  monomial 2 (10 : ZMod 29) +
  monomial 3 (10 : ZMod 29) +
  monomial 4 (13 : ZMod 29) +
  monomial 5 (21 : ZMod 29) +
  monomial 6 (7 : ZMod 29) +
  monomial 7 (12 : ZMod 29) +
  monomial 8 (14 : ZMod 29) +
  monomial 9 (19 : ZMod 29)

def P4 : (ZMod 29)[X] :=
  monomial 0 (12 : ZMod 29) +
  monomial 1 (14 : ZMod 29) +
  monomial 3 (6 : ZMod 29) +
  monomial 4 (11 : ZMod 29) +
  monomial 5 (18 : ZMod 29) +
  monomial 6 (18 : ZMod 29) +
  monomial 7 (28 : ZMod 29) +
  monomial 8 (13 : ZMod 29) +
  monomial 9 (1 : ZMod 29)

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

def P6 : (ZMod 29)[X] :=
  monomial 0 (10 : ZMod 29) +
  monomial 1 (4 : ZMod 29) +
  monomial 2 (12 : ZMod 29) +
  monomial 3 (17 : ZMod 29) +
  monomial 4 (24 : ZMod 29) +
  monomial 5 (26 : ZMod 29) +
  monomial 6 (16 : ZMod 29) +
  monomial 7 (28 : ZMod 29) +
  monomial 8 (9 : ZMod 29) +
  monomial 9 (11 : ZMod 29)

def P7 : (ZMod 29)[X] :=
  monomial 0 (20 : ZMod 29) +
  monomial 1 (15 : ZMod 29) +
  monomial 2 (19 : ZMod 29) +
  monomial 3 (26 : ZMod 29) +
  monomial 4 (16 : ZMod 29) +
  monomial 5 (25 : ZMod 29) +
  monomial 6 (13 : ZMod 29) +
  monomial 7 (14 : ZMod 29) +
  monomial 8 (2 : ZMod 29) +
  monomial 9 (15 : ZMod 29)

def P8 : (ZMod 29)[X] :=
  monomial 0 (25 : ZMod 29) +
  monomial 1 (23 : ZMod 29) +
  monomial 3 (23 : ZMod 29) +
  monomial 4 (22 : ZMod 29) +
  monomial 5 (13 : ZMod 29) +
  monomial 6 (11 : ZMod 29) +
  monomial 7 (9 : ZMod 29) +
  monomial 8 (16 : ZMod 29) +
  monomial 9 (17 : ZMod 29)

def P9 : (ZMod 29)[X] :=
  monomial 0 (20 : ZMod 29) +
  monomial 1 (20 : ZMod 29) +
  monomial 2 (3 : ZMod 29) +
  monomial 3 (22 : ZMod 29) +
  monomial 4 (17 : ZMod 29) +
  monomial 5 (13 : ZMod 29) +
  monomial 6 (25 : ZMod 29) +
  monomial 7 (14 : ZMod 29) +
  monomial 8 (26 : ZMod 29) +
  monomial 9 (24 : ZMod 29)

def P10 : (ZMod 29)[X] :=
  monomial 1 (1 : ZMod 29)

def R0 : (ZMod 29)[X] :=
  monomial 0 (1 : ZMod 29)

def R1 : (ZMod 29)[X] :=
  monomial 0 (13 : ZMod 29) +
  monomial 1 (1 : ZMod 29) +
  monomial 2 (26 : ZMod 29) +
  monomial 3 (24 : ZMod 29) +
  monomial 4 (4 : ZMod 29) +
  monomial 5 (10 : ZMod 29) +
  monomial 6 (25 : ZMod 29) +
  monomial 7 (23 : ZMod 29) +
  monomial 8 (18 : ZMod 29) +
  monomial 9 (20 : ZMod 29)

def R2 : (ZMod 29)[X] :=
  monomial 0 (19 : ZMod 29) +
  monomial 1 (8 : ZMod 29) +
  monomial 2 (1 : ZMod 29) +
  monomial 3 (11 : ZMod 29) +
  monomial 4 (13 : ZMod 29) +
  monomial 5 (27 : ZMod 29) +
  monomial 6 (6 : ZMod 29) +
  monomial 7 (10 : ZMod 29) +
  monomial 8 (1 : ZMod 29) +
  monomial 9 (1 : ZMod 29)

def R3 : (ZMod 29)[X] :=
  monomial 0 (21 : ZMod 29) +
  monomial 1 (4 : ZMod 29) +
  monomial 2 (16 : ZMod 29) +
  monomial 3 (17 : ZMod 29) +
  monomial 4 (27 : ZMod 29) +
  monomial 5 (10 : ZMod 29) +
  monomial 6 (5 : ZMod 29) +
  monomial 7 (9 : ZMod 29) +
  monomial 8 (4 : ZMod 29) +
  monomial 9 (24 : ZMod 29)

def R4 : (ZMod 29)[X] :=
  monomial 0 (28 : ZMod 29) +
  monomial 1 (10 : ZMod 29) +
  monomial 2 (13 : ZMod 29) +
  monomial 3 (25 : ZMod 29) +
  monomial 4 (21 : ZMod 29) +
  monomial 5 (4 : ZMod 29) +
  monomial 6 (19 : ZMod 29) +
  monomial 7 (21 : ZMod 29) +
  monomial 8 (19 : ZMod 29) +
  monomial 9 (1 : ZMod 29)

def R5 : (ZMod 29)[X] :=
  monomial 0 (10 : ZMod 29) +
  monomial 1 (5 : ZMod 29) +
  monomial 3 (20 : ZMod 29) +
  monomial 4 (22 : ZMod 29) +
  monomial 5 (5 : ZMod 29) +
  monomial 6 (16 : ZMod 29) +
  monomial 7 (4 : ZMod 29) +
  monomial 8 (7 : ZMod 29) +
  monomial 9 (3 : ZMod 29)

def R6 : (ZMod 29)[X] :=
  monomial 0 (7 : ZMod 29) +
  monomial 1 (8 : ZMod 29) +
  monomial 2 (1 : ZMod 29) +
  monomial 3 (20 : ZMod 29) +
  monomial 4 (26 : ZMod 29) +
  monomial 5 (16 : ZMod 29) +
  monomial 6 (4 : ZMod 29) +
  monomial 7 (7 : ZMod 29) +
  monomial 8 (24 : ZMod 29)

def R7 : (ZMod 29)[X] :=
  monomial 0 (24 : ZMod 29) +
  monomial 1 (2 : ZMod 29) +
  monomial 2 (14 : ZMod 29) +
  monomial 4 (5 : ZMod 29) +
  monomial 5 (8 : ZMod 29) +
  monomial 6 (5 : ZMod 29) +
  monomial 7 (25 : ZMod 29) +
  monomial 8 (20 : ZMod 29) +
  monomial 9 (6 : ZMod 29)

def R8 : (ZMod 29)[X] :=
  monomial 0 (20 : ZMod 29) +
  monomial 1 (14 : ZMod 29) +
  monomial 2 (21 : ZMod 29) +
  monomial 3 (10 : ZMod 29) +
  monomial 4 (10 : ZMod 29) +
  monomial 5 (2 : ZMod 29) +
  monomial 6 (8 : ZMod 29) +
  monomial 7 (1 : ZMod 29) +
  monomial 8 (6 : ZMod 29) +
  monomial 9 (28 : ZMod 29)

def R9 : (ZMod 29)[X] :=
  monomial 1 (6 : ZMod 29) +
  monomial 2 (13 : ZMod 29) +
  monomial 3 (14 : ZMod 29) +
  monomial 4 (9 : ZMod 29) +
  monomial 5 (25 : ZMod 29) +
  monomial 7 (28 : ZMod 29) +
  monomial 8 (9 : ZMod 29) +
  monomial 9 (6 : ZMod 29)

def Q1 : (ZMod 29)[X] :=
  monomial 0 (19 : ZMod 29) +
  monomial 1 (21 : ZMod 29) +
  monomial 2 (21 : ZMod 29) +
  monomial 3 (3 : ZMod 29) +
  monomial 4 (23 : ZMod 29) +
  monomial 5 (18 : ZMod 29) +
  monomial 6 (28 : ZMod 29) +
  monomial 7 (16 : ZMod 29) +
  monomial 8 (10 : ZMod 29) +
  monomial 9 (13 : ZMod 29) +
  monomial 10 (7 : ZMod 29) +
  monomial 11 (8 : ZMod 29) +
  monomial 12 (6 : ZMod 29) +
  monomial 13 (24 : ZMod 29) +
  monomial 14 (2 : ZMod 29) +
  monomial 15 (21 : ZMod 29) +
  monomial 16 (28 : ZMod 29) +
  monomial 17 (16 : ZMod 29) +
  monomial 18 (4 : ZMod 29) +
  monomial 19 (1 : ZMod 29)

def S2 : (ZMod 29)[X] :=
  monomial 0 (15 : ZMod 29) +
  monomial 1 (18 : ZMod 29) +
  monomial 2 (12 : ZMod 29) +
  monomial 3 (14 : ZMod 29) +
  monomial 4 (11 : ZMod 29) +
  monomial 5 (2 : ZMod 29) +
  monomial 6 (26 : ZMod 29) +
  monomial 8 (23 : ZMod 29)

def S3 : (ZMod 29)[X] :=
  monomial 0 (11 : ZMod 29) +
  monomial 2 (12 : ZMod 29) +
  monomial 3 (3 : ZMod 29) +
  monomial 4 (18 : ZMod 29) +
  monomial 5 (15 : ZMod 29) +
  monomial 6 (17 : ZMod 29) +
  monomial 7 (2 : ZMod 29) +
  monomial 8 (20 : ZMod 29)

def S4 : (ZMod 29)[X] :=
  monomial 0 (10 : ZMod 29) +
  monomial 1 (20 : ZMod 29) +
  monomial 2 (25 : ZMod 29) +
  monomial 3 (5 : ZMod 29) +
  monomial 4 (28 : ZMod 29) +
  monomial 5 (21 : ZMod 29) +
  monomial 6 (5 : ZMod 29) +
  monomial 7 (25 : ZMod 29) +
  monomial 8 (16 : ZMod 29)

def S5 : (ZMod 29)[X] :=
  monomial 0 (18 : ZMod 29) +
  monomial 1 (4 : ZMod 29) +
  monomial 2 (3 : ZMod 29) +
  monomial 3 (5 : ZMod 29) +
  monomial 4 (2 : ZMod 29) +
  monomial 5 (7 : ZMod 29) +
  monomial 7 (14 : ZMod 29) +
  monomial 8 (20 : ZMod 29)

def S6 : (ZMod 29)[X] :=
  monomial 0 (21 : ZMod 29) +
  monomial 1 (23 : ZMod 29) +
  monomial 2 (13 : ZMod 29) +
  monomial 3 (10 : ZMod 29) +
  monomial 4 (21 : ZMod 29) +
  monomial 5 (16 : ZMod 29) +
  monomial 6 (10 : ZMod 29) +
  monomial 7 (28 : ZMod 29) +
  monomial 8 (2 : ZMod 29)

def S7 : (ZMod 29)[X] :=
  monomial 0 (27 : ZMod 29) +
  monomial 1 (7 : ZMod 29) +
  monomial 2 (14 : ZMod 29) +
  monomial 3 (13 : ZMod 29) +
  monomial 4 (10 : ZMod 29) +
  monomial 5 (25 : ZMod 29) +
  monomial 6 (27 : ZMod 29) +
  monomial 7 (16 : ZMod 29)

def S8 : (ZMod 29)[X] :=
  monomial 0 (6 : ZMod 29) +
  monomial 1 (24 : ZMod 29) +
  monomial 2 (26 : ZMod 29) +
  monomial 3 (12 : ZMod 29) +
  monomial 4 (22 : ZMod 29) +
  monomial 5 (23 : ZMod 29) +
  monomial 6 (20 : ZMod 29) +
  monomial 7 (2 : ZMod 29) +
  monomial 8 (4 : ZMod 29)

def S9 : (ZMod 29)[X] :=
  monomial 0 (26 : ZMod 29) +
  monomial 1 (21 : ZMod 29) +
  monomial 2 (28 : ZMod 29) +
  monomial 3 (16 : ZMod 29) +
  monomial 4 (1 : ZMod 29) +
  monomial 5 (14 : ZMod 29) +
  monomial 6 (19 : ZMod 29) +
  monomial 7 (22 : ZMod 29) +
  monomial 8 (9 : ZMod 29)

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

lemma cert_P1 : (X : (ZMod 29)[X])^29 - P1 = f * Q1 := by
  ext k
  by_cases hk : k ≤ 29
  · interval_cases k <;>
      (try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [f, P1, Q1, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : ((X : (ZMod 29)[X])^29 - P1).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (X : (ZMod 29)[X])^29 - P1)
    have hdeg : ((X : (ZMod 29)[X])^29 - P1).natDegree < 30 := by
      simp only [f, P1, Q1]
      compute_degree!
    omega
  have hR : (f * Q1).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := f * Q1)
    have hdeg : (f * Q1).natDegree < 30 := by
      simp only [f, P1, Q1]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_R2 : R1 * P1 - R2 = f * S2 := by
  ext k
  by_cases hk : k ≤ 18
  · interval_cases k <;>
      (try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [R1, P1, R2, f, S2, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (R1 * P1 - R2).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := R1 * P1 - R2)
    have hdeg : (R1 * P1 - R2).natDegree < 19 := by
      simp only [R1, P1, R2, f, S2]
      compute_degree!
    omega
  have hR : (f * S2).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := f * S2)
    have hdeg : (f * S2).natDegree < 19 := by
      simp only [R1, P1, R2, f, S2]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_R3 : R2 * P1 - R3 = f * S3 := by
  ext k
  by_cases hk : k ≤ 18
  · interval_cases k <;>
      (try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [R2, P1, R3, f, S3, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (R2 * P1 - R3).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := R2 * P1 - R3)
    have hdeg : (R2 * P1 - R3).natDegree < 19 := by
      simp only [R2, P1, R3, f, S3]
      compute_degree!
    omega
  have hR : (f * S3).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := f * S3)
    have hdeg : (f * S3).natDegree < 19 := by
      simp only [R2, P1, R3, f, S3]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_R4 : R3 * P1 - R4 = f * S4 := by
  ext k
  by_cases hk : k ≤ 18
  · interval_cases k <;>
      (try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [R3, P1, R4, f, S4, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (R3 * P1 - R4).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := R3 * P1 - R4)
    have hdeg : (R3 * P1 - R4).natDegree < 19 := by
      simp only [R3, P1, R4, f, S4]
      compute_degree!
    omega
  have hR : (f * S4).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := f * S4)
    have hdeg : (f * S4).natDegree < 19 := by
      simp only [R3, P1, R4, f, S4]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_R5 : R4 * P1 - R5 = f * S5 := by
  ext k
  by_cases hk : k ≤ 18
  · interval_cases k <;>
      (try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [R4, P1, R5, f, S5, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (R4 * P1 - R5).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := R4 * P1 - R5)
    have hdeg : (R4 * P1 - R5).natDegree < 19 := by
      simp only [R4, P1, R5, f, S5]
      compute_degree!
    omega
  have hR : (f * S5).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := f * S5)
    have hdeg : (f * S5).natDegree < 19 := by
      simp only [R4, P1, R5, f, S5]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_R6 : R5 * P1 - R6 = f * S6 := by
  ext k
  by_cases hk : k ≤ 18
  · interval_cases k <;>
      (try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [R5, P1, R6, f, S6, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (R5 * P1 - R6).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := R5 * P1 - R6)
    have hdeg : (R5 * P1 - R6).natDegree < 19 := by
      simp only [R5, P1, R6, f, S6]
      compute_degree!
    omega
  have hR : (f * S6).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := f * S6)
    have hdeg : (f * S6).natDegree < 19 := by
      simp only [R5, P1, R6, f, S6]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_R7 : R6 * P1 - R7 = f * S7 := by
  ext k
  by_cases hk : k ≤ 18
  · interval_cases k <;>
      (try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [R6, P1, R7, f, S7, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (R6 * P1 - R7).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := R6 * P1 - R7)
    have hdeg : (R6 * P1 - R7).natDegree < 19 := by
      simp only [R6, P1, R7, f, S7]
      compute_degree!
    omega
  have hR : (f * S7).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := f * S7)
    have hdeg : (f * S7).natDegree < 19 := by
      simp only [R6, P1, R7, f, S7]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_R8 : R7 * P1 - R8 = f * S8 := by
  ext k
  by_cases hk : k ≤ 18
  · interval_cases k <;>
      (try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [R7, P1, R8, f, S8, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (R7 * P1 - R8).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := R7 * P1 - R8)
    have hdeg : (R7 * P1 - R8).natDegree < 19 := by
      simp only [R7, P1, R8, f, S8]
      compute_degree!
    omega
  have hR : (f * S8).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := f * S8)
    have hdeg : (f * S8).natDegree < 19 := by
      simp only [R7, P1, R8, f, S8]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_R9 : R8 * P1 - R9 = f * S9 := by
  ext k
  by_cases hk : k ≤ 18
  · interval_cases k <;>
      (try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [R8, P1, R9, f, S9, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (R8 * P1 - R9).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := R8 * P1 - R9)
    have hdeg : (R8 * P1 - R9).natDegree < 19 := by
      simp only [R8, P1, R9, f, S9]
      compute_degree!
    omega
  have hR : (f * S9).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := f * S9)
    have hdeg : (f * S9).natDegree < 19 := by
      simp only [R8, P1, R9, f, S9]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_lin1 : P2 = (C (P1.coeff 0) * R0 + C (P1.coeff 1) * R1 + C (P1.coeff 2) * R2 + C (P1.coeff 3) * R3 + C (P1.coeff 4) * R4 + C (P1.coeff 5) * R5 + C (P1.coeff 6) * R6 + C (P1.coeff 7) * R7 + C (P1.coeff 8) * R8 + C (P1.coeff 9) * R9) := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [P2, P1, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (P2).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P2)
    have hdeg : (P2).natDegree < 10 := by
      simp only [P2, P1, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  have hR : ((C (P1.coeff 0) * R0 + C (P1.coeff 1) * R1 + C (P1.coeff 2) * R2 + C (P1.coeff 3) * R3 + C (P1.coeff 4) * R4 + C (P1.coeff 5) * R5 + C (P1.coeff 6) * R6 + C (P1.coeff 7) * R7 + C (P1.coeff 8) * R8 + C (P1.coeff 9) * R9)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (C (P1.coeff 0) * R0 + C (P1.coeff 1) * R1 + C (P1.coeff 2) * R2 + C (P1.coeff 3) * R3 + C (P1.coeff 4) * R4 + C (P1.coeff 5) * R5 + C (P1.coeff 6) * R6 + C (P1.coeff 7) * R7 + C (P1.coeff 8) * R8 + C (P1.coeff 9) * R9))
    have hdeg : ((C (P1.coeff 0) * R0 + C (P1.coeff 1) * R1 + C (P1.coeff 2) * R2 + C (P1.coeff 3) * R3 + C (P1.coeff 4) * R4 + C (P1.coeff 5) * R5 + C (P1.coeff 6) * R6 + C (P1.coeff 7) * R7 + C (P1.coeff 8) * R8 + C (P1.coeff 9) * R9)).natDegree < 10 := by
      simp only [P2, P1, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_lin2 : P3 = (C (P2.coeff 0) * R0 + C (P2.coeff 1) * R1 + C (P2.coeff 2) * R2 + C (P2.coeff 3) * R3 + C (P2.coeff 4) * R4 + C (P2.coeff 5) * R5 + C (P2.coeff 6) * R6 + C (P2.coeff 7) * R7 + C (P2.coeff 8) * R8 + C (P2.coeff 9) * R9) := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [P3, P2, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (P3).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P3)
    have hdeg : (P3).natDegree < 10 := by
      simp only [P3, P2, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  have hR : ((C (P2.coeff 0) * R0 + C (P2.coeff 1) * R1 + C (P2.coeff 2) * R2 + C (P2.coeff 3) * R3 + C (P2.coeff 4) * R4 + C (P2.coeff 5) * R5 + C (P2.coeff 6) * R6 + C (P2.coeff 7) * R7 + C (P2.coeff 8) * R8 + C (P2.coeff 9) * R9)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (C (P2.coeff 0) * R0 + C (P2.coeff 1) * R1 + C (P2.coeff 2) * R2 + C (P2.coeff 3) * R3 + C (P2.coeff 4) * R4 + C (P2.coeff 5) * R5 + C (P2.coeff 6) * R6 + C (P2.coeff 7) * R7 + C (P2.coeff 8) * R8 + C (P2.coeff 9) * R9))
    have hdeg : ((C (P2.coeff 0) * R0 + C (P2.coeff 1) * R1 + C (P2.coeff 2) * R2 + C (P2.coeff 3) * R3 + C (P2.coeff 4) * R4 + C (P2.coeff 5) * R5 + C (P2.coeff 6) * R6 + C (P2.coeff 7) * R7 + C (P2.coeff 8) * R8 + C (P2.coeff 9) * R9)).natDegree < 10 := by
      simp only [P3, P2, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_lin3 : P4 = (C (P3.coeff 0) * R0 + C (P3.coeff 1) * R1 + C (P3.coeff 2) * R2 + C (P3.coeff 3) * R3 + C (P3.coeff 4) * R4 + C (P3.coeff 5) * R5 + C (P3.coeff 6) * R6 + C (P3.coeff 7) * R7 + C (P3.coeff 8) * R8 + C (P3.coeff 9) * R9) := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [P4, P3, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (P4).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P4)
    have hdeg : (P4).natDegree < 10 := by
      simp only [P4, P3, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  have hR : ((C (P3.coeff 0) * R0 + C (P3.coeff 1) * R1 + C (P3.coeff 2) * R2 + C (P3.coeff 3) * R3 + C (P3.coeff 4) * R4 + C (P3.coeff 5) * R5 + C (P3.coeff 6) * R6 + C (P3.coeff 7) * R7 + C (P3.coeff 8) * R8 + C (P3.coeff 9) * R9)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (C (P3.coeff 0) * R0 + C (P3.coeff 1) * R1 + C (P3.coeff 2) * R2 + C (P3.coeff 3) * R3 + C (P3.coeff 4) * R4 + C (P3.coeff 5) * R5 + C (P3.coeff 6) * R6 + C (P3.coeff 7) * R7 + C (P3.coeff 8) * R8 + C (P3.coeff 9) * R9))
    have hdeg : ((C (P3.coeff 0) * R0 + C (P3.coeff 1) * R1 + C (P3.coeff 2) * R2 + C (P3.coeff 3) * R3 + C (P3.coeff 4) * R4 + C (P3.coeff 5) * R5 + C (P3.coeff 6) * R6 + C (P3.coeff 7) * R7 + C (P3.coeff 8) * R8 + C (P3.coeff 9) * R9)).natDegree < 10 := by
      simp only [P4, P3, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_lin4 : P5 = (C (P4.coeff 0) * R0 + C (P4.coeff 1) * R1 + C (P4.coeff 2) * R2 + C (P4.coeff 3) * R3 + C (P4.coeff 4) * R4 + C (P4.coeff 5) * R5 + C (P4.coeff 6) * R6 + C (P4.coeff 7) * R7 + C (P4.coeff 8) * R8 + C (P4.coeff 9) * R9) := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [P5, P4, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (P5).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P5)
    have hdeg : (P5).natDegree < 10 := by
      simp only [P5, P4, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  have hR : ((C (P4.coeff 0) * R0 + C (P4.coeff 1) * R1 + C (P4.coeff 2) * R2 + C (P4.coeff 3) * R3 + C (P4.coeff 4) * R4 + C (P4.coeff 5) * R5 + C (P4.coeff 6) * R6 + C (P4.coeff 7) * R7 + C (P4.coeff 8) * R8 + C (P4.coeff 9) * R9)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (C (P4.coeff 0) * R0 + C (P4.coeff 1) * R1 + C (P4.coeff 2) * R2 + C (P4.coeff 3) * R3 + C (P4.coeff 4) * R4 + C (P4.coeff 5) * R5 + C (P4.coeff 6) * R6 + C (P4.coeff 7) * R7 + C (P4.coeff 8) * R8 + C (P4.coeff 9) * R9))
    have hdeg : ((C (P4.coeff 0) * R0 + C (P4.coeff 1) * R1 + C (P4.coeff 2) * R2 + C (P4.coeff 3) * R3 + C (P4.coeff 4) * R4 + C (P4.coeff 5) * R5 + C (P4.coeff 6) * R6 + C (P4.coeff 7) * R7 + C (P4.coeff 8) * R8 + C (P4.coeff 9) * R9)).natDegree < 10 := by
      simp only [P5, P4, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_lin5 : P6 = (C (P5.coeff 0) * R0 + C (P5.coeff 1) * R1 + C (P5.coeff 2) * R2 + C (P5.coeff 3) * R3 + C (P5.coeff 4) * R4 + C (P5.coeff 5) * R5 + C (P5.coeff 6) * R6 + C (P5.coeff 7) * R7 + C (P5.coeff 8) * R8 + C (P5.coeff 9) * R9) := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [P6, P5, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (P6).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P6)
    have hdeg : (P6).natDegree < 10 := by
      simp only [P6, P5, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  have hR : ((C (P5.coeff 0) * R0 + C (P5.coeff 1) * R1 + C (P5.coeff 2) * R2 + C (P5.coeff 3) * R3 + C (P5.coeff 4) * R4 + C (P5.coeff 5) * R5 + C (P5.coeff 6) * R6 + C (P5.coeff 7) * R7 + C (P5.coeff 8) * R8 + C (P5.coeff 9) * R9)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (C (P5.coeff 0) * R0 + C (P5.coeff 1) * R1 + C (P5.coeff 2) * R2 + C (P5.coeff 3) * R3 + C (P5.coeff 4) * R4 + C (P5.coeff 5) * R5 + C (P5.coeff 6) * R6 + C (P5.coeff 7) * R7 + C (P5.coeff 8) * R8 + C (P5.coeff 9) * R9))
    have hdeg : ((C (P5.coeff 0) * R0 + C (P5.coeff 1) * R1 + C (P5.coeff 2) * R2 + C (P5.coeff 3) * R3 + C (P5.coeff 4) * R4 + C (P5.coeff 5) * R5 + C (P5.coeff 6) * R6 + C (P5.coeff 7) * R7 + C (P5.coeff 8) * R8 + C (P5.coeff 9) * R9)).natDegree < 10 := by
      simp only [P6, P5, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_lin6 : P7 = (C (P6.coeff 0) * R0 + C (P6.coeff 1) * R1 + C (P6.coeff 2) * R2 + C (P6.coeff 3) * R3 + C (P6.coeff 4) * R4 + C (P6.coeff 5) * R5 + C (P6.coeff 6) * R6 + C (P6.coeff 7) * R7 + C (P6.coeff 8) * R8 + C (P6.coeff 9) * R9) := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [P7, P6, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (P7).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P7)
    have hdeg : (P7).natDegree < 10 := by
      simp only [P7, P6, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  have hR : ((C (P6.coeff 0) * R0 + C (P6.coeff 1) * R1 + C (P6.coeff 2) * R2 + C (P6.coeff 3) * R3 + C (P6.coeff 4) * R4 + C (P6.coeff 5) * R5 + C (P6.coeff 6) * R6 + C (P6.coeff 7) * R7 + C (P6.coeff 8) * R8 + C (P6.coeff 9) * R9)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (C (P6.coeff 0) * R0 + C (P6.coeff 1) * R1 + C (P6.coeff 2) * R2 + C (P6.coeff 3) * R3 + C (P6.coeff 4) * R4 + C (P6.coeff 5) * R5 + C (P6.coeff 6) * R6 + C (P6.coeff 7) * R7 + C (P6.coeff 8) * R8 + C (P6.coeff 9) * R9))
    have hdeg : ((C (P6.coeff 0) * R0 + C (P6.coeff 1) * R1 + C (P6.coeff 2) * R2 + C (P6.coeff 3) * R3 + C (P6.coeff 4) * R4 + C (P6.coeff 5) * R5 + C (P6.coeff 6) * R6 + C (P6.coeff 7) * R7 + C (P6.coeff 8) * R8 + C (P6.coeff 9) * R9)).natDegree < 10 := by
      simp only [P7, P6, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_lin7 : P8 = (C (P7.coeff 0) * R0 + C (P7.coeff 1) * R1 + C (P7.coeff 2) * R2 + C (P7.coeff 3) * R3 + C (P7.coeff 4) * R4 + C (P7.coeff 5) * R5 + C (P7.coeff 6) * R6 + C (P7.coeff 7) * R7 + C (P7.coeff 8) * R8 + C (P7.coeff 9) * R9) := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [P8, P7, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (P8).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P8)
    have hdeg : (P8).natDegree < 10 := by
      simp only [P8, P7, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  have hR : ((C (P7.coeff 0) * R0 + C (P7.coeff 1) * R1 + C (P7.coeff 2) * R2 + C (P7.coeff 3) * R3 + C (P7.coeff 4) * R4 + C (P7.coeff 5) * R5 + C (P7.coeff 6) * R6 + C (P7.coeff 7) * R7 + C (P7.coeff 8) * R8 + C (P7.coeff 9) * R9)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (C (P7.coeff 0) * R0 + C (P7.coeff 1) * R1 + C (P7.coeff 2) * R2 + C (P7.coeff 3) * R3 + C (P7.coeff 4) * R4 + C (P7.coeff 5) * R5 + C (P7.coeff 6) * R6 + C (P7.coeff 7) * R7 + C (P7.coeff 8) * R8 + C (P7.coeff 9) * R9))
    have hdeg : ((C (P7.coeff 0) * R0 + C (P7.coeff 1) * R1 + C (P7.coeff 2) * R2 + C (P7.coeff 3) * R3 + C (P7.coeff 4) * R4 + C (P7.coeff 5) * R5 + C (P7.coeff 6) * R6 + C (P7.coeff 7) * R7 + C (P7.coeff 8) * R8 + C (P7.coeff 9) * R9)).natDegree < 10 := by
      simp only [P8, P7, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_lin8 : P9 = (C (P8.coeff 0) * R0 + C (P8.coeff 1) * R1 + C (P8.coeff 2) * R2 + C (P8.coeff 3) * R3 + C (P8.coeff 4) * R4 + C (P8.coeff 5) * R5 + C (P8.coeff 6) * R6 + C (P8.coeff 7) * R7 + C (P8.coeff 8) * R8 + C (P8.coeff 9) * R9) := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [P9, P8, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (P9).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P9)
    have hdeg : (P9).natDegree < 10 := by
      simp only [P9, P8, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  have hR : ((C (P8.coeff 0) * R0 + C (P8.coeff 1) * R1 + C (P8.coeff 2) * R2 + C (P8.coeff 3) * R3 + C (P8.coeff 4) * R4 + C (P8.coeff 5) * R5 + C (P8.coeff 6) * R6 + C (P8.coeff 7) * R7 + C (P8.coeff 8) * R8 + C (P8.coeff 9) * R9)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (C (P8.coeff 0) * R0 + C (P8.coeff 1) * R1 + C (P8.coeff 2) * R2 + C (P8.coeff 3) * R3 + C (P8.coeff 4) * R4 + C (P8.coeff 5) * R5 + C (P8.coeff 6) * R6 + C (P8.coeff 7) * R7 + C (P8.coeff 8) * R8 + C (P8.coeff 9) * R9))
    have hdeg : ((C (P8.coeff 0) * R0 + C (P8.coeff 1) * R1 + C (P8.coeff 2) * R2 + C (P8.coeff 3) * R3 + C (P8.coeff 4) * R4 + C (P8.coeff 5) * R5 + C (P8.coeff 6) * R6 + C (P8.coeff 7) * R7 + C (P8.coeff 8) * R8 + C (P8.coeff 9) * R9)).natDegree < 10 := by
      simp only [P9, P8, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_lin9 : P10 = (C (P9.coeff 0) * R0 + C (P9.coeff 1) * R1 + C (P9.coeff 2) * R2 + C (P9.coeff 3) * R3 + C (P9.coeff 4) * R4 + C (P9.coeff 5) * R5 + C (P9.coeff 6) * R6 + C (P9.coeff 7) * R7 + C (P9.coeff 8) * R8 + C (P9.coeff 9) * R9) := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [P10, P9, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (P10).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P10)
    have hdeg : (P10).natDegree < 10 := by
      simp only [P10, P9, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  have hR : ((C (P9.coeff 0) * R0 + C (P9.coeff 1) * R1 + C (P9.coeff 2) * R2 + C (P9.coeff 3) * R3 + C (P9.coeff 4) * R4 + C (P9.coeff 5) * R5 + C (P9.coeff 6) * R6 + C (P9.coeff 7) * R7 + C (P9.coeff 8) * R8 + C (P9.coeff 9) * R9)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (C (P9.coeff 0) * R0 + C (P9.coeff 1) * R1 + C (P9.coeff 2) * R2 + C (P9.coeff 3) * R3 + C (P9.coeff 4) * R4 + C (P9.coeff 5) * R5 + C (P9.coeff 6) * R6 + C (P9.coeff 7) * R7 + C (P9.coeff 8) * R8 + C (P9.coeff 9) * R9))
    have hdeg : ((C (P9.coeff 0) * R0 + C (P9.coeff 1) * R1 + C (P9.coeff 2) * R2 + C (P9.coeff 3) * R3 + C (P9.coeff 4) * R4 + C (P9.coeff 5) * R5 + C (P9.coeff 6) * R6 + C (P9.coeff 7) * R7 + C (P9.coeff 8) * R8 + C (P9.coeff 9) * R9)).natDegree < 10 := by
      simp only [P10, P9, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  rw [hL,hR]

lemma hG2 : G2 = P2 - X := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [G2, P2, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (G2).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := G2)
    have hdeg : (G2).natDegree < 10 := by
      simp only [G2, P2]
      compute_degree!
    omega
  have hR : (P2 - X).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P2 - X)
    have hdeg : (P2 - X).natDegree < 10 := by
      simp only [G2, P2]
      compute_degree!
    omega
  rw [hL,hR]

lemma hG5 : G5 = P5 - X := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
       try simp [G5, P5, coeff_monomial, coeff_X_pow, coeff_X, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
       try reduce_mod_char)
  have hL : (G5).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := G5)
    have hdeg : (G5).natDegree < 10 := by
      simp only [G5, P5]
      compute_degree!
    omega
  have hR : (P5 - X).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P5 - X)
    have hdeg : (P5 - X).natDegree < 10 := by
      simp only [G5, P5]
      compute_degree!
    omega
  rw [hL,hR]

lemma cert_bez2 : A2 * f + B2 * G2 = (1 : (ZMod 29)[X]) := by
  ext k
  by_cases hk : k ≤ 19
  · interval_cases k <;>
      (try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
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
  rw [hL,hR]

lemma cert_bez5 : A5 * f + B5 * G5 = (1 : (ZMod 29)[X]) := by
  ext k
  by_cases hk : k ≤ 19
  · interval_cases k <;>
      (try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp only [coeff_add, coeff_sub]
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
  rw [hL,hR]
