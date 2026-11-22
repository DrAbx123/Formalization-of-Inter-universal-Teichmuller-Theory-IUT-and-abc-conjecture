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

lemma cert_P1 : (X : (ZMod 29)[X])^29 - P1 = f * Q1 := by
  ext k
  by_cases hk : k ≤ 29
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [f, P1, Q1, coeff_monomial, coeff_X_pow, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
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
  rw [hL, hR]

lemma cert_R2 : R1 * P1 - R2 = f * S2 := by
  ext k
  by_cases hk : k ≤ 18
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [R1, P1, R2, f, S2, coeff_monomial, coeff_X_pow, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ]
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
  rw [hL, hR]
