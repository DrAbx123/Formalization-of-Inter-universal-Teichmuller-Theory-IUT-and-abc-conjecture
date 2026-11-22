import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

example : ((X : (ZMod 29)[X])^29 - X) ∣ ((X : (ZMod 29)[X])^(29^2) - X) := by
  have h : ((X : (ZMod 29)[X])^28 - 1) ∣ (X^840 - 1) := by
    have := pow_one_sub_dvd_pow_mul_sub_one (X : (ZMod 29)[X]) 28 30
    simpa using this
  have hmul := mul_dvd_mul_left (X : (ZMod 29)[X]) h
  convert hmul using 1 <;> ring_nf
