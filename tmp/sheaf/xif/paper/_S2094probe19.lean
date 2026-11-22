import Mathlib
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
example : ((168 : ℕ) : ZMod 29) = ((23 : ℕ) : ZMod 29) := by
  rw [ZMod.natCast_eq_natCast_iff]
  norm_num [Nat.ModEq]
example : ((168 : ℕ) : ZMod 29) = ((23 : ℕ) : ZMod 29) := by
  rw [ZMod.natCast_eq_natCast_iff']
  norm_num
example : ((168 : ℕ) : ZMod 29) = ((23 : ℕ) : ZMod 29) := by
  decide
