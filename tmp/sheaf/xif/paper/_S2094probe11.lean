import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
example : (C (3 : ZMod 29) * C 4 : (ZMod 29)[X]) = C 12 := by
  rw [← C_mul]
  norm_num
example : (X^2 * C (3 : ZMod 29) * C 4 : (ZMod 29)[X]) = C 12 * X^2 := by
  rw [← C_mul]
  norm_num
  ring
