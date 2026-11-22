import Mathlib.Tactic
set_option maxHeartbeats 2000000
open Polynomial

lemma quadratic_splits_of_square {K : Type*} [Field K] (d r : K) (hr : r ^ 2 = d) :
    (X^2 - C d : K[X]).Splits := by
  have hfactor : (X^2 - C d : K[X]) = (X - C r) * (X + C r) := by
    rw [← hr, map_pow]
    ring
  rw [hfactor]
  exact (Polynomial.Splits.X_sub_C r).mul (Polynomial.Splits.X_add_C r)

example : (X^2 + 1 : (ZMod 5)[X]) = (X^2 - C (-1) : (ZMod 5)[X]) := by
  have hC : C (-1 : ZMod 5) = (-1 : (ZMod 5)[X]) := by simp
  rw [hC]
  ring

example : (X^2 + 1 : (ZMod 5)[X]).Splits := by
  have h : (X^2 + 1 : (ZMod 5)[X]) = (X^2 - C (-1) : (ZMod 5)[X]) := by
    have hC : C (-1 : ZMod 5) = (-1 : (ZMod 5)[X]) := by simp
    rw [hC]
    ring
  rw [h]
  exact quadratic_splits_of_square (-1) 2 (by decide)
