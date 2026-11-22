import Mathlib.Tactic
set_option maxHeartbeats 1000000
open Polynomial

lemma quadratic_splits_of_square {K : Type*} [Field K] (d r : K) (hr : r ^ 2 = d) :
    (X^2 - C d : K[X]).Splits := by
  have hfactor : (X^2 - C d : K[X]) = (X - C r) * (X + C r) := by
    rw [← hr, map_pow]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul (Polynomial.Splits.X_add_C r)

example : (X^2 - C (-1) : (ZMod 5)[X]).Splits := by
  exact quadratic_splits_of_square (-1) 2 (by decide)

example : (X^2 + 1 : (ZMod 5)[X]).Splits := by
  rw [show (X^2 + 1 : (ZMod 5)[X]) = (X^2 - C (-1) : (ZMod 5)[X]) by
    rw [show C (-1 : ZMod 5) = (-1 : (ZMod 5)[X]) by rw [Polynomial.C_neg, Polynomial.C_1]]
    ring]
  exact quadratic_splits_of_square (-1) 2 (by decide)
