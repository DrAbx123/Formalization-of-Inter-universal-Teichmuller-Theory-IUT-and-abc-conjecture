import Mathlib
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
example : (168 : ZMod 29) = 23 := by
  rw [ZMod.natCast_eq_natCast_iff]
  norm_num [Nat.ModEq]
example : (168 : ZMod 29) = 23 := by
  rw [ZMod.natCast_eq_natCast_iff']
  norm_num
