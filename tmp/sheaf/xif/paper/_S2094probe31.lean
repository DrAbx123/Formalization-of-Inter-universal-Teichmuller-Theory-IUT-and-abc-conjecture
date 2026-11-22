import Mathlib
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
example : (((168 : ℕ) : ZMod 29)) = ((23 : ℕ) : ZMod 29) := by
  rw [ZMod.natCast_eq_natCast_iff']
example : (((24 : ℕ) : ZMod 29) * ((7:ℕ):ZMod 29)) = ((23 : ℕ) : ZMod 29) := by
  rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
