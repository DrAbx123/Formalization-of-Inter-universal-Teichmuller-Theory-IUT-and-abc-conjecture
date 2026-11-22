import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
set_option maxRecDepth 10000
example : (X^2 * C (3 : ZMod 29) * C 4 : (ZMod 29)[X]) = C 12 * X^2 := by
  simp only [mul_assoc]
  simp only [← C_mul]
  norm_num
  ring
