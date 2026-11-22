import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
example : (X^2 * (3 : (ZMod 29)[X]) * (4 : (ZMod 29)[X])) = (12 : (ZMod 29)[X]) * X^2 := by ring
example : ((168 : (ZMod 29)[X])) = (23 : (ZMod 29)[X]) := by norm_num
