import Mathlib

open Polynomial

local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

lemma aeval_eq_sum_range {R : Type*} [CommRing R] [Algebra (ZMod 29) R]
    (x : R) (p : (ZMod 29)[X]) (n : ℕ) (hp : p.natDegree < n) :
    aeval x p = ∑ i ∈ Finset.range n, (p.coeff i) * x ^ i := by
  conv_lhs => rw [p.as_sum_range' n hp]
  simp [map_sum, aeval_monomial, mul_comm]

lemma aeval_pow_char_29 {R : Type*} [CommRing R] [Algebra (ZMod 29) R] [CharP R 29]
    (x : R) {p : (ZMod 29)[X]} (hp : p.natDegree < 10) :
    (aeval x p) ^ 29 = ∑ i ∈ Finset.range 10, (p.coeff i) * (x ^ 29) ^ i := by
  rw [aeval_eq_sum_range x p 10 hp, sum_pow_char_pow]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow, aeval_monomial]
  rw [ZMod.pow_card_pow]
  rw [pow_mul, pow_mul]
  congr 1
  omega
