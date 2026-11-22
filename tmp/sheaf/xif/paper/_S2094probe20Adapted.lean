import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
example : (C (((24 : ℕ) : ZMod 29)) * C (((7 : ℕ) : ZMod 29)) : (ZMod 29)[X]) = C (((23 : ℕ) : ZMod 29)) := by
  rw [← C_mul]
  rw [← Nat.cast_mul]
  rw [ZMod.natCast_eq_natCast_iff']
  norm_num
example : (C (((168 : ℕ) : ZMod 29)) : (ZMod 29)[X]) = C (((23 : ℕ) : ZMod 29)) := by
  rw [ZMod.natCast_eq_natCast_iff']
  norm_num
