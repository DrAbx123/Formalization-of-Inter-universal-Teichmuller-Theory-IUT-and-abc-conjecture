import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
example : (168 : (ZMod 29)[X]) = (23 : (ZMod 29)[X]) := by ring
example : ((24 : (ZMod 29)[X]) * (7 : (ZMod 29)[X])) = (23 : (ZMod 29)[X]) := by ring
example : ((24 : ZMod 29) * 7) = 23 := by ring
