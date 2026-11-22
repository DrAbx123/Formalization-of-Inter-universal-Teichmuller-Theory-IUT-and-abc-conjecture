import Mathlib
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
example : (168 : ZMod 29) = 23 := by decide
example : (168 : ZMod 29) = 23 := by norm_num
example : (168 : ZMod 29) = 23 := by native_decide
example : (168 : ZMod 29) = 23 := by omega
