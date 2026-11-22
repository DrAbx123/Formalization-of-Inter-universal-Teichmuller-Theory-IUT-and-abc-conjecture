import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

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

lemma cert_lin1 : P2 = (∑ j ∈ Finset.range 10, C (P1.coeff j) * Rfun j) := by
  ext k
  by_cases hk : k ≤ 9
  · interval_cases k <;>
      (try simp only [coeff_add, coeff_sub]
       try repeat rw [coeff_mul]
       try repeat rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
       try simp [P2, P1, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, coeff_monomial, coeff_X_pow, coeff_C, coeff_C_mul, coeff_sum, coeff_one, Finset.sum_range_succ, Rfun]
       try reduce_mod_char)
  have hL : (P2).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := P2)
    have hdeg : (P2).natDegree < 10 := by
      simp only [P2, P1, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  have hR : ((∑ j ∈ Finset.range 10, C (P1.coeff j) * Rfun j)).coeff k = 0 := by
    apply coeff_eq_zero_of_natDegree_lt (p := (∑ j ∈ Finset.range 10, C (P1.coeff j) * Rfun j))
    have hdeg : ((∑ j ∈ Finset.range 10, C (P1.coeff j) * Rfun j)).natDegree < 10 := by
      simp only [P2, P1, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]
      compute_degree!
    omega
  rw [hL,hR]
