import Mathlib

open Polynomial

def p : (ZMod 29)[X] :=
  C 10 + C 24 * X + C 16 * X^2 + C 14 * X^3 + C 24 * X^4 + C 8 * X^5 +
  C 5 * X^6 + C 7 * X^7 + C 0 * X^8 + C 25 * X^9

def f : (ZMod 29)[X] := X^10 + p

example : p.degree < 10 := by
  unfold p
  compute_degree!

example : f.Monic := by
  unfold f
  apply monic_X_pow_add
  unfold p
  compute_degree!

example : f.natDegree = 10 := by
  unfold f
  rw [natDegree_add_eq_left_of_degree_lt]
  · rw [natDegree_X_pow]
  · rw [degree_X_pow]
    unfold p
    compute_degree!
