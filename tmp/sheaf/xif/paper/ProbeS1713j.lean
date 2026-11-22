import Mathlib.Tactic
example : (64 : ZMod 5) = 4 := by norm_num
example : (256 : ZMod 5) = 1 := by norm_num
example : (1024 : ZMod 5) = 4 := by norm_num
example : ((64 : ℕ) : ZMod 5) = 4 := by norm_num
example : ((64 : ℕ) : ZMod 5) = 4 := by decide
example : (256 : ZMod 5) = 1 := by decide
example : (1024 : ZMod 5) = 4 := by decide
example : ((-4 : ZMod 5) = 1) := by norm_num
example : ((-4 : ZMod 5) = 1) := by decide
