import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
example : (7322650804224 : ZMod 29) = 19 := by norm_num
example (x : ZMod 29) : x^2 * (176 : ZMod 29) = x^2 * 2 := by norm_num
example (x : ZMod 29) : x^2 * (176 : ZMod 29) = x^2 * 2 := by ring_nf
