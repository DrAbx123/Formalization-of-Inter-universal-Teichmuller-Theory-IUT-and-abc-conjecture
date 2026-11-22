import Mathlib

example : (2 : ℚ) + 2 = 4 := by norm_num

example (x : ℝ) (h : x ≤ 1) : 2*x - x ≤ 1 := by linarith

example (x : ℝ) (hx : 0 < x) : 0 < x^2 + 1 := by positivity

example (x y : ℝ) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by grind
