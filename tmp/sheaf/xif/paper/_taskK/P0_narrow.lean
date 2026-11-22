import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

example : (2 : ℚ) + 2 = 4 := by norm_num
example (x : ℝ) (h : x ≤ 1) : 2*x - x ≤ 1 := by linarith
example (x y : ℝ) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by grind
