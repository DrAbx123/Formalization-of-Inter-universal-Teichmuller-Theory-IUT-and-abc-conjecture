import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
example : (C (168 : ZMod 29) : (ZMod 29)[X]) = C 23 := by
  reduce_mod_char
example : (X^2 * C (168 : ZMod 29) : (ZMod 29)[X]) = C 23 * X^2 := by
  reduce_mod_char
