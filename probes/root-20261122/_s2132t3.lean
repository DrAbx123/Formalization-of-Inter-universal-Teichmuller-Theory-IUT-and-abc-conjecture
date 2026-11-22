import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

example : ∀ x : ZMod 29, x^2 + 6*x + 12 ≠ 0 := by decide

example (x : ZMod 29) : x^2 + 6*x + 12 ≠ 0 := by
  fin_cases x <;> decide

example : ¬ ∃ y : ZMod 29, y^2 = 26 := by
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    intro h; rw [h] at hy; norm_num at hy
  have h := ZMod.pow_card_sub_one_eq_one y hy0
  rw [← hy] at h
  norm_num at h
