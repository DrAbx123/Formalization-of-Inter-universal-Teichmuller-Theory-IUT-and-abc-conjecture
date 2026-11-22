import Mathlib
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
example : (C (168 : ZMod 29) : (ZMod 29)[X]) = C 23 := by
  norm_num
example : (C (168 : ZMod 29) : (ZMod 29)[X]) = C 23 := by
  rw [Polynomial.C_eq_natCast, Polynomial.C_eq_natCast]
  norm_num
example : (C ((24 : ZMod 29) * 7) : (ZMod 29)[X]) = C 23 := by
  norm_num
