import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
open Polynomial
example (a b : ZMod 29) : (C a * X) * (C b * X) = C (a*b) * X^2 := by
  rw [← C_mul]; ring
example : (C (12 : ZMod 29) + C 6 * X + X^2) * (C 10) = C 120 + C 60 * X + C 10 * X^2 := by
  rw [mul_add, mul_add, ← C_mul, ← C_mul, ← C_mul]; ring
