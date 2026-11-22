import Mathlib
open Polynomial
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

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
    congr 1
    exact Nat.sub_add_cancel hq
  · rw [mul_sub, mul_one, ← pow_succ']
    congr 1
    exact Nat.sub_add_cancel (Nat.one_le_pow 2 (Nat.card K) hqpos)
