import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Field.Rat
open Polynomial

example (q : ℚ) : (C q : ℚ[X]) = (q : ℚ[X]) := by
  rw [Polynomial.C_eq_algebraMap, map_ratCast]

example (a b : ℚ) : (C a * C b * X ^ 2 : ℚ[X]) = ((a * b : ℚ) : ℚ[X]) * X ^ 2 := by
  rw [← Polynomial.C_mul]
  norm_num

example (a b : ℚ) : (C a * C b * X ^ 2 : ℚ[X]) = ((a * b : ℚ) : ℚ[X]) * X ^ 2 := by
  simp [← Polynomial.C_mul]

#print axioms Polynomial.C_eq_algebraMap
