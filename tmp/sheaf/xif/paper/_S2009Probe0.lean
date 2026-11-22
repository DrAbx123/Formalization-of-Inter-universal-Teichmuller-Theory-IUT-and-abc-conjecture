import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

example : (5 : K5) = 0 := by decide
example : (5 : K5) = 0 := by rfl
example : (5 : K5) = 0 := by simp
example : (5 : K5) = 0 := by norm_num
example : (2 : K5) + 3 = 0 := by decide
example : (2 : K5) + 3 = 0 := by norm_num
example : ((2 : K5) + 3) = 0 := by ring
