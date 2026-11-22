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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
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
  rw [hL,hR]

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
  rw [hL,hR]


def Rfun : ℕ → (ZMod 29)[X]
  | 0 => R0
  | 1 => R1
  | 2 => R2
  | 3 => R3
  | 4 => R4
  | 5 => R5
  | 6 => R6
  | 7 => R7
  | 8 => R8
  | 9 => R9
  | _ => 0

lemma hfdeg : f.natDegree = 10 := by
  unfold f
  compute_degree!

lemma hfmonic : f.Monic := by
  rw [Monic, hfdeg]
  unfold f
  norm_num

lemma hP1deg : P1.natDegree < 10 := by
  unfold P1
  compute_degree!

lemma hP2deg : P2.natDegree < 10 := by
  unfold P2
  compute_degree!

lemma hP3deg : P3.natDegree < 10 := by
  unfold P3
  compute_degree!

lemma hP4deg : P4.natDegree < 10 := by
  unfold P4
  compute_degree!

lemma hP5deg : P5.natDegree < 10 := by
  unfold P5
  compute_degree!

lemma hP6deg : P6.natDegree < 10 := by
  unfold P6
  compute_degree!

lemma hP7deg : P7.natDegree < 10 := by
  unfold P7
  compute_degree!

lemma hP8deg : P8.natDegree < 10 := by
  unfold P8
  compute_degree!

lemma hP9deg : P9.natDegree < 10 := by
  unfold P9
  compute_degree!

lemma hP10deg : P10.natDegree < 10 := by
  unfold P10
  compute_degree!

lemma hlin1' : P2 = ∑ j ∈ Finset.range 10, C (P1.coeff j) * Rfun j := by
  rw [cert_lin1]
  simp [Finset.sum_range_succ, Rfun]

lemma hlin2' : P3 = ∑ j ∈ Finset.range 10, C (P2.coeff j) * Rfun j := by
  rw [cert_lin2]
  simp [Finset.sum_range_succ, Rfun]

lemma hlin3' : P4 = ∑ j ∈ Finset.range 10, C (P3.coeff j) * Rfun j := by
  rw [cert_lin3]
  simp [Finset.sum_range_succ, Rfun]

lemma hlin4' : P5 = ∑ j ∈ Finset.range 10, C (P4.coeff j) * Rfun j := by
  rw [cert_lin4]
  simp [Finset.sum_range_succ, Rfun]

lemma hlin5' : P6 = ∑ j ∈ Finset.range 10, C (P5.coeff j) * Rfun j := by
  rw [cert_lin5]
  simp [Finset.sum_range_succ, Rfun]

lemma hlin6' : P7 = ∑ j ∈ Finset.range 10, C (P6.coeff j) * Rfun j := by
  rw [cert_lin6]
  simp [Finset.sum_range_succ, Rfun]

lemma hlin7' : P8 = ∑ j ∈ Finset.range 10, C (P7.coeff j) * Rfun j := by
  rw [cert_lin7]
  simp [Finset.sum_range_succ, Rfun]

lemma hlin8' : P9 = ∑ j ∈ Finset.range 10, C (P8.coeff j) * Rfun j := by
  rw [cert_lin8]
  simp [Finset.sum_range_succ, Rfun]

lemma hlin9' : P10 = ∑ j ∈ Finset.range 10, C (P9.coeff j) * Rfun j := by
  rw [cert_lin9]
  simp [Finset.sum_range_succ, Rfun]


lemma X_pow_card_sub_X_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Fintype K] :
    ((X : K[X]) ^ Nat.card K - X) ∣ ((X : K[X]) ^ (Nat.card K)^2 - X) := by
  have hqpos : 0 < Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have hq : 1 ≤ Nat.card K := hqpos
  have hdiv : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
    have h := Nat.pow_sub_one_dvd_pow_sub_one (x := Nat.card K) (m := 1) (k := 2) (by norm_num)
    simpa using h
  obtain ⟨c, hc⟩ := hdiv
  have hpoly : (X : K[X]) ^ (Nat.card K - 1) - 1 ∣ (X : K[X]) ^ (Nat.card K ^ 2 - 1) - 1 := by
    rw [hc]
    exact pow_one_sub_dvd_pow_mul_sub_one X (Nat.card K - 1) c
  have hmul := mul_dvd_mul_left (X : K[X]) hpoly
  convert hmul using 1
  · rw [mul_sub, mul_one, ← pow_succ']
    rw [Nat.sub_add_cancel hq]
  · rw [mul_sub, mul_one, ← pow_succ']
    rw [Nat.sub_add_cancel (Nat.one_le_pow 2 (Nat.card K) hqpos)]

lemma irreducible_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Fintype K] {g : K[X]} (hg : Irreducible g) :
    g ∣ (X : K[X]) ^ (Nat.card K) ^ g.natDegree - X := by
  haveI : Fact (Irreducible g) := ⟨hg⟩
  letI : Field (AdjoinRoot g) := AdjoinRoot.instField
  letI : Algebra K (AdjoinRoot g) := inferInstance
  let pb : PowerBasis K (AdjoinRoot g) := AdjoinRoot.powerBasis hg.ne_zero
  haveI : Module.Finite K (AdjoinRoot g) := pb.finite
  haveI : Fintype (AdjoinRoot g) := Fintype.ofEquiv (Fin pb.dim → K) pb.basis.equivFun.symm.toEquiv
  have hfr : Module.finrank K (AdjoinRoot g) = g.natDegree := by
    rw [pb.finrank]
    rfl
  have hcard : Nat.card (AdjoinRoot g) = Nat.card K ^ g.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := K), hfr]
  have hroot : aeval (AdjoinRoot.root g) ((X : K[X]) ^ (Nat.card K) ^ g.natDegree - X) = 0 := by
    simp only [map_sub, map_pow, aeval_X]
    have hpow : (AdjoinRoot.root g) ^ (Nat.card K ^ g.natDegree) = AdjoinRoot.root g := by
      rw [← hcard]
      simpa [Nat.card_eq_fintype_card] using (FiniteField.pow_card (AdjoinRoot.root g))
    rw [hpow, sub_self]
  have hdvd : minpoly K (AdjoinRoot.root g) ∣ (X : K[X]) ^ (Nat.card K) ^ g.natDegree - X :=
    minpoly.dvd K _ hroot
  have hmin : minpoly K (AdjoinRoot.root g) = g * C g.leadingCoeff⁻¹ :=
    AdjoinRoot.minpoly_root hg.ne_zero
  have hgdvd : g ∣ minpoly K (AdjoinRoot.root g) := by
    rw [hmin]
    exact dvd_mul_right _ _
  exact hgdvd.trans hdvd

theorem irreducible_of_degree_ten
    {K : Type*} [Field K] [Fintype K] {f : K[X]}
    (hm : f.Monic) (hdeg : f.natDegree = 10)
    (hdvd : f ∣ (X : K[X]) ^ (Nat.card K) ^ 10 - X)
    (h2 : IsCoprime f ((X : K[X]) ^ (Nat.card K) ^ 2 - X))
    (h5 : IsCoprime f ((X : K[X]) ^ (Nat.card K) ^ 5 - X)) :
    Irreducible f := by
  by_contra hf
  have hf0 : f ≠ 0 := hm.ne_zero
  have hfunit : ¬ IsUnit f := by
    intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg_irr, hg_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hfunit hf0
  have hg_dvd_E : g ∣ (X : K[X]) ^ (Nat.card K) ^ 10 - X := hg_dvd.trans hdvd
  have hdvd10 : g.natDegree ∣ 10 :=
    Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hg_irr hg_dvd_E
  have hgpos : 0 < g.natDegree := Irreducible.natDegree_pos hg_irr
  have hgle : g.natDegree ≤ 10 := by
    rw [← hdeg]
    exact natDegree_le_of_dvd hg_dvd hf0
  have hgne : g.natDegree ≠ 10 := by
    intro h10
    have hassoc : Associated g f := associated_of_dvd_of_natDegree_le hg_dvd hf0 (by omega)
    exact hf (hassoc.irreducible hg_irr)
  set d := g.natDegree with hddef
  have hdvd10' : d ∣ 10 := by simpa [hddef] using hdvd10
  have hlt' : d < 10 := by simpa [hddef] using lt_of_le_of_ne hgle hgne
  have hpos' : 0 < d := by simpa [hddef] using hgpos
  have hcases : d = 1 ∨ d = 2 ∨ d = 5 := by
    interval_cases d <;> norm_num at hdvd10' <;> norm_num
  rcases hcases with h1 | h2d | h5d
  · have hgd : g.natDegree = 1 := by omega
    have hg1 : g ∣ (X : K[X]) ^ (Nat.card K) ^ g.natDegree - X :=
      irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    have hg1' : g ∣ (X : K[X]) ^ Nat.card K - X := by simpa [hgd] using hg1
    have hg2 : g ∣ (X : K[X]) ^ (Nat.card K) ^ 2 - X :=
      hg1'.trans (X_pow_card_sub_X_dvd_X_pow_card_pow_sub_X (K := K))
    exact hg_irr.not_isUnit (h2.isUnit_of_dvd' hg_dvd hg2)
  · have hgd : g.natDegree = 2 := by omega
    have hg2 : g ∣ (X : K[X]) ^ (Nat.card K) ^ 2 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_isUnit (h2.isUnit_of_dvd' hg_dvd hg2)
  · have hgd : g.natDegree = 5 := by omega
    have hg5 : g ∣ (X : K[X]) ^ (Nat.card K) ^ 5 - X := by
      simpa [hgd] using irreducible_dvd_X_pow_card_pow_sub_X hg_irr
    exact hg_irr.not_isUnit (h5.isUnit_of_dvd' hg_dvd hg5)


theorem s2094_f_irreducible : Irreducible f := by
  let x : AdjoinRoot f := AdjoinRoot.root f
  haveI : CharP (AdjoinRoot f) 29 := by
    have hdeg0 : f.degree ≠ 0 := by
      rw [degree_eq_natDegree hfmonic.ne_zero, hfdeg]
      norm_num
    have hinj : Function.Injective (algebraMap (ZMod 29) (AdjoinRoot f)) := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.of.injective_of_degree_ne_zero hdeg0
    exact charP_of_injective_algebraMap hinj 29
  have hpow1 : x ^ 29 = aeval x P1 := by
    have h : aeval x ((X : (ZMod 29)[X]) ^ 29 - P1) = 0 := by
      rw [cert_P1]
      simp [AdjoinRoot.aeval_eq]
    have h' : x ^ 29 - aeval x P1 = 0 := by simpa using h
    exact sub_eq_zero.mp h'
  have hR0 : (aeval x P1)^0 = aeval x (Rfun 0) := by simp [Rfun, R0]
  have hR1 : (aeval x P1)^1 = aeval x (Rfun 1) := by simp [Rfun, R1, P1]
  have hR2 : (aeval x P1)^2 = aeval x (Rfun 2) := by
    have h : aeval x (R1 * P1 - R2) = 0 := by
      rw [cert_R2]
      simp [AdjoinRoot.aeval_eq]
    have h' : aeval x (R1 * P1) = aeval x R2 := sub_eq_zero.mp h
    calc
      (aeval x P1)^2 = (aeval x P1)^1 * aeval x P1 := by
        rw [show 2 = 1 + 1 by norm_num, pow_succ]
      _ = aeval x R1 * aeval x P1 := by rw [hR1]
      _ = aeval x (R1 * P1) := by rw [map_mul]
      _ = aeval x R2 := h'
      _ = aeval x (Rfun 2) := by simp [Rfun, R2]
  have hR3 : (aeval x P1)^3 = aeval x (Rfun 3) := by
    have h : aeval x (R2 * P1 - R3) = 0 := by
      rw [cert_R3]
      simp [AdjoinRoot.aeval_eq]
    have h' : aeval x (R2 * P1) = aeval x R3 := sub_eq_zero.mp h
    calc
      (aeval x P1)^3 = (aeval x P1)^2 * aeval x P1 := by
        rw [show 3 = 2 + 1 by norm_num, pow_succ]
      _ = aeval x R2 * aeval x P1 := by rw [hR2]
      _ = aeval x (R2 * P1) := by rw [map_mul]
      _ = aeval x R3 := h'
      _ = aeval x (Rfun 3) := by simp [Rfun, R3]
  have hR4 : (aeval x P1)^4 = aeval x (Rfun 4) := by
    have h : aeval x (R3 * P1 - R4) = 0 := by
      rw [cert_R4]
      simp [AdjoinRoot.aeval_eq]
    have h' : aeval x (R3 * P1) = aeval x R4 := sub_eq_zero.mp h
    calc
      (aeval x P1)^4 = (aeval x P1)^3 * aeval x P1 := by
        rw [show 4 = 3 + 1 by norm_num, pow_succ]
      _ = aeval x R3 * aeval x P1 := by rw [hR3]
      _ = aeval x (R3 * P1) := by rw [map_mul]
      _ = aeval x R4 := h'
      _ = aeval x (Rfun 4) := by simp [Rfun, R4]
  have hR5 : (aeval x P1)^5 = aeval x (Rfun 5) := by
    have h : aeval x (R4 * P1 - R5) = 0 := by
      rw [cert_R5]
      simp [AdjoinRoot.aeval_eq]
    have h' : aeval x (R4 * P1) = aeval x R5 := sub_eq_zero.mp h
    calc
      (aeval x P1)^5 = (aeval x P1)^4 * aeval x P1 := by
        rw [show 5 = 4 + 1 by norm_num, pow_succ]
      _ = aeval x R4 * aeval x P1 := by rw [hR4]
      _ = aeval x (R4 * P1) := by rw [map_mul]
      _ = aeval x R5 := h'
      _ = aeval x (Rfun 5) := by simp [Rfun, R5]
  have hR6 : (aeval x P1)^6 = aeval x (Rfun 6) := by
    have h : aeval x (R5 * P1 - R6) = 0 := by
      rw [cert_R6]
      simp [AdjoinRoot.aeval_eq]
    have h' : aeval x (R5 * P1) = aeval x R6 := sub_eq_zero.mp h
    calc
      (aeval x P1)^6 = (aeval x P1)^5 * aeval x P1 := by
        rw [show 6 = 5 + 1 by norm_num, pow_succ]
      _ = aeval x R5 * aeval x P1 := by rw [hR5]
      _ = aeval x (R5 * P1) := by rw [map_mul]
      _ = aeval x R6 := h'
      _ = aeval x (Rfun 6) := by simp [Rfun, R6]
  have hR7 : (aeval x P1)^7 = aeval x (Rfun 7) := by
    have h : aeval x (R6 * P1 - R7) = 0 := by
      rw [cert_R7]
      simp [AdjoinRoot.aeval_eq]
    have h' : aeval x (R6 * P1) = aeval x R7 := sub_eq_zero.mp h
    calc
      (aeval x P1)^7 = (aeval x P1)^6 * aeval x P1 := by
        rw [show 7 = 6 + 1 by norm_num, pow_succ]
      _ = aeval x R6 * aeval x P1 := by rw [hR6]
      _ = aeval x (R6 * P1) := by rw [map_mul]
      _ = aeval x R7 := h'
      _ = aeval x (Rfun 7) := by simp [Rfun, R7]
  have hR8 : (aeval x P1)^8 = aeval x (Rfun 8) := by
    have h : aeval x (R7 * P1 - R8) = 0 := by
      rw [cert_R8]
      simp [AdjoinRoot.aeval_eq]
    have h' : aeval x (R7 * P1) = aeval x R8 := sub_eq_zero.mp h
    calc
      (aeval x P1)^8 = (aeval x P1)^7 * aeval x P1 := by
        rw [show 8 = 7 + 1 by norm_num, pow_succ]
      _ = aeval x R7 * aeval x P1 := by rw [hR7]
      _ = aeval x (R7 * P1) := by rw [map_mul]
      _ = aeval x R8 := h'
      _ = aeval x (Rfun 8) := by simp [Rfun, R8]
  have hR9 : (aeval x P1)^9 = aeval x (Rfun 9) := by
    have h : aeval x (R8 * P1 - R9) = 0 := by
      rw [cert_R9]
      simp [AdjoinRoot.aeval_eq]
    have h' : aeval x (R8 * P1) = aeval x R9 := sub_eq_zero.mp h
    calc
      (aeval x P1)^9 = (aeval x P1)^8 * aeval x P1 := by
        rw [show 9 = 8 + 1 by norm_num, pow_succ]
      _ = aeval x R8 * aeval x P1 := by rw [hR8]
      _ = aeval x (R8 * P1) := by rw [map_mul]
      _ = aeval x R9 := h'
      _ = aeval x (Rfun 9) := by simp [Rfun, R9]
  have hRpow : ∀ j, j < 10 → (aeval x P1)^j = aeval x (Rfun j) := by
    intro j hj
    interval_cases j
    · exact hR0
    · exact hR1
    · exact hR2
    · exact hR3
    · exact hR4
    · exact hR5
    · exact hR6
    · exact hR7
    · exact hR8
    · exact hR9
  have hpow2 : x ^ (29 ^ 2) = aeval x P2 := by
    calc
      x ^ (29 ^ 2) = (x ^ (29 ^ 1)) ^ 29 := by
        rw [show 29 ^ 2 = 29 ^ 1 * 29 by norm_num, pow_mul]
      _ = (aeval x P1) ^ 29 := by rw [hpow1]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P1).coeff j) * (x ^ 29) ^ j :=
          aeval_pow_char_29 x hP1deg
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P1).coeff j) * (aeval x P1) ^ j := by
          rw [hpow1]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P1).coeff j) * aeval x (Rfun j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hRpow j (by simpa using hj)]
      _ = aeval x (∑ j ∈ Finset.range 10, C ((P1).coeff j) * Rfun j) := by
          simp [map_sum, map_mul, aeval_C]
      _ = aeval x P2 := by rw [hlin1']
  have hpow3 : x ^ (29 ^ 3) = aeval x P3 := by
    calc
      x ^ (29 ^ 3) = (x ^ (29 ^ 2)) ^ 29 := by
        rw [show 29 ^ 3 = 29 ^ 2 * 29 by norm_num, pow_mul]
      _ = (aeval x P2) ^ 29 := by rw [hpow2]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P2).coeff j) * (x ^ 29) ^ j :=
          aeval_pow_char_29 x hP2deg
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P2).coeff j) * (aeval x P1) ^ j := by
          rw [hpow1]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P2).coeff j) * aeval x (Rfun j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hRpow j (by simpa using hj)]
      _ = aeval x (∑ j ∈ Finset.range 10, C ((P2).coeff j) * Rfun j) := by
          simp [map_sum, map_mul, aeval_C]
      _ = aeval x P3 := by rw [hlin2']
  have hpow4 : x ^ (29 ^ 4) = aeval x P4 := by
    calc
      x ^ (29 ^ 4) = (x ^ (29 ^ 3)) ^ 29 := by
        rw [show 29 ^ 4 = 29 ^ 3 * 29 by norm_num, pow_mul]
      _ = (aeval x P3) ^ 29 := by rw [hpow3]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P3).coeff j) * (x ^ 29) ^ j :=
          aeval_pow_char_29 x hP3deg
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P3).coeff j) * (aeval x P1) ^ j := by
          rw [hpow1]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P3).coeff j) * aeval x (Rfun j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hRpow j (by simpa using hj)]
      _ = aeval x (∑ j ∈ Finset.range 10, C ((P3).coeff j) * Rfun j) := by
          simp [map_sum, map_mul, aeval_C]
      _ = aeval x P4 := by rw [hlin3']
  have hpow5 : x ^ (29 ^ 5) = aeval x P5 := by
    calc
      x ^ (29 ^ 5) = (x ^ (29 ^ 4)) ^ 29 := by
        rw [show 29 ^ 5 = 29 ^ 4 * 29 by norm_num, pow_mul]
      _ = (aeval x P4) ^ 29 := by rw [hpow4]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P4).coeff j) * (x ^ 29) ^ j :=
          aeval_pow_char_29 x hP4deg
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P4).coeff j) * (aeval x P1) ^ j := by
          rw [hpow1]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P4).coeff j) * aeval x (Rfun j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hRpow j (by simpa using hj)]
      _ = aeval x (∑ j ∈ Finset.range 10, C ((P4).coeff j) * Rfun j) := by
          simp [map_sum, map_mul, aeval_C]
      _ = aeval x P5 := by rw [hlin4']
  have hpow6 : x ^ (29 ^ 6) = aeval x P6 := by
    calc
      x ^ (29 ^ 6) = (x ^ (29 ^ 5)) ^ 29 := by
        rw [show 29 ^ 6 = 29 ^ 5 * 29 by norm_num, pow_mul]
      _ = (aeval x P5) ^ 29 := by rw [hpow5]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P5).coeff j) * (x ^ 29) ^ j :=
          aeval_pow_char_29 x hP5deg
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P5).coeff j) * (aeval x P1) ^ j := by
          rw [hpow1]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P5).coeff j) * aeval x (Rfun j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hRpow j (by simpa using hj)]
      _ = aeval x (∑ j ∈ Finset.range 10, C ((P5).coeff j) * Rfun j) := by
          simp [map_sum, map_mul, aeval_C]
      _ = aeval x P6 := by rw [hlin5']
  have hpow7 : x ^ (29 ^ 7) = aeval x P7 := by
    calc
      x ^ (29 ^ 7) = (x ^ (29 ^ 6)) ^ 29 := by
        rw [show 29 ^ 7 = 29 ^ 6 * 29 by norm_num, pow_mul]
      _ = (aeval x P6) ^ 29 := by rw [hpow6]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P6).coeff j) * (x ^ 29) ^ j :=
          aeval_pow_char_29 x hP6deg
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P6).coeff j) * (aeval x P1) ^ j := by
          rw [hpow1]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P6).coeff j) * aeval x (Rfun j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hRpow j (by simpa using hj)]
      _ = aeval x (∑ j ∈ Finset.range 10, C ((P6).coeff j) * Rfun j) := by
          simp [map_sum, map_mul, aeval_C]
      _ = aeval x P7 := by rw [hlin6']
  have hpow8 : x ^ (29 ^ 8) = aeval x P8 := by
    calc
      x ^ (29 ^ 8) = (x ^ (29 ^ 7)) ^ 29 := by
        rw [show 29 ^ 8 = 29 ^ 7 * 29 by norm_num, pow_mul]
      _ = (aeval x P7) ^ 29 := by rw [hpow7]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P7).coeff j) * (x ^ 29) ^ j :=
          aeval_pow_char_29 x hP7deg
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P7).coeff j) * (aeval x P1) ^ j := by
          rw [hpow1]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P7).coeff j) * aeval x (Rfun j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hRpow j (by simpa using hj)]
      _ = aeval x (∑ j ∈ Finset.range 10, C ((P7).coeff j) * Rfun j) := by
          simp [map_sum, map_mul, aeval_C]
      _ = aeval x P8 := by rw [hlin7']
  have hpow9 : x ^ (29 ^ 9) = aeval x P9 := by
    calc
      x ^ (29 ^ 9) = (x ^ (29 ^ 8)) ^ 29 := by
        rw [show 29 ^ 9 = 29 ^ 8 * 29 by norm_num, pow_mul]
      _ = (aeval x P8) ^ 29 := by rw [hpow8]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P8).coeff j) * (x ^ 29) ^ j :=
          aeval_pow_char_29 x hP8deg
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P8).coeff j) * (aeval x P1) ^ j := by
          rw [hpow1]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P8).coeff j) * aeval x (Rfun j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hRpow j (by simpa using hj)]
      _ = aeval x (∑ j ∈ Finset.range 10, C ((P8).coeff j) * Rfun j) := by
          simp [map_sum, map_mul, aeval_C]
      _ = aeval x P9 := by rw [hlin8']
  have hpow10 : x ^ (29 ^ 10) = aeval x P10 := by
    calc
      x ^ (29 ^ 10) = (x ^ (29 ^ 9)) ^ 29 := by
        rw [show 29 ^ 10 = 29 ^ 9 * 29 by norm_num, pow_mul]
      _ = (aeval x P9) ^ 29 := by rw [hpow9]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P9).coeff j) * (x ^ 29) ^ j :=
          aeval_pow_char_29 x hP9deg
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P9).coeff j) * (aeval x P1) ^ j := by
          rw [hpow1]
      _ = ∑ j ∈ Finset.range 10, algebraMap (ZMod 29) (AdjoinRoot f) ((P9).coeff j) * aeval x (Rfun j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hRpow j (by simpa using hj)]
      _ = aeval x (∑ j ∈ Finset.range 10, C ((P9).coeff j) * Rfun j) := by
          simp [map_sum, map_mul, aeval_C]
      _ = aeval x P10 := by rw [hlin9']
  have hpow10x : x ^ (29 ^ 10) = x := by
    rw [hpow10]
    simp [P10]
  have hdvd : f ∣ (X : (ZMod 29)[X]) ^ (29 ^ 10) - X := by
    rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
    have : aeval x ((X : (ZMod 29)[X]) ^ (29 ^ 10) - X) = 0 := by
      simpa [map_sub, map_pow, aeval_X, hpow10x]
    exact this
  have hdiv2 : f ∣ (X : (ZMod 29)[X]) ^ (29 ^ 2) - P2 := by
    rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
    have : aeval x ((X : (ZMod 29)[X]) ^ (29 ^ 2) - P2) = 0 := by
      simpa [map_sub, map_pow, aeval_X, hpow2]
    exact this
  rcases hdiv2 with ⟨q2, hq2⟩
  have hcop2 : IsCoprime f (P2 - X) := by
    refine ⟨A2, B2, ?_⟩
    rw [← hG2]
    exact cert_bez2
  have h2 : IsCoprime f ((X : (ZMod 29)[X]) ^ (29 ^ 2) - X) := by
    have hEq : (X : (ZMod 29)[X]) ^ (29 ^ 2) - X = (P2 - X) + f * q2 := by
      rw [← hq2]
      ring
    rw [hEq]
    exact hcop2.add_mul_left_right q2
  have hdiv5 : f ∣ (X : (ZMod 29)[X]) ^ (29 ^ 5) - P5 := by
    rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
    have : aeval x ((X : (ZMod 29)[X]) ^ (29 ^ 5) - P5) = 0 := by
      simpa [map_sub, map_pow, aeval_X, hpow5]
    exact this
  rcases hdiv5 with ⟨q5, hq5⟩
  have hcop5 : IsCoprime f (P5 - X) := by
    refine ⟨A5, B5, ?_⟩
    rw [← hG5]
    exact cert_bez5
  have h5 : IsCoprime f ((X : (ZMod 29)[X]) ^ (29 ^ 5) - X) := by
    have hEq : (X : (ZMod 29)[X]) ^ (29 ^ 5) - X = (P5 - X) + f * q5 := by
      rw [← hq5]
      ring
    rw [hEq]
    exact hcop5.add_mul_left_right q5
  exact irreducible_of_degree_ten hfmonic hfdeg
    (by simpa [Nat.card_zmod] using hdvd)
    (by simpa [Nat.card_zmod] using h2)
    (by simpa [Nat.card_zmod] using h5)
