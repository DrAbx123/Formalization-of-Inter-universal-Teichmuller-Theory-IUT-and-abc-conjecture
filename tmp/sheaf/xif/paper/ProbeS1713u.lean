import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
open Polynomial

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  have h1 : (X^2 + 1 : (ZMod 5)[X]).degree ≤ 2 := by compute_degree
  have h2 : ((X - C 2) * (X + C 2) : (ZMod 5)[X]).degree ≤ 2 := by compute_degree
  rw [Polynomial.eq_quadratic_of_degree_le_two h1,
      Polynomial.eq_quadratic_of_degree_le_two h2]
  have c2 : (X^2 + 1 : (ZMod 5)[X]).coeff 2 = ((X - C 2) * (X + C 2) : (ZMod 5)[X]).coeff 2 := by decide
  have c1 : (X^2 + 1 : (ZMod 5)[X]).coeff 1 = ((X - C 2) * (X + C 2) : (ZMod 5)[X]).coeff 1 := by decide
  have c0 : (X^2 + 1 : (ZMod 5)[X]).coeff 0 = ((X - C 2) * (X + C 2) : (ZMod 5)[X]).coeff 0 := by decide
  rw [c2, c1, c0]

example : (X^2 + 1 : (ZMod 5)[X]).Splits := by
  have hfac : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
    have h1 : (X^2 + 1 : (ZMod 5)[X]).degree ≤ 2 := by compute_degree
    have h2 : ((X - C 2) * (X + C 2) : (ZMod 5)[X]).degree ≤ 2 := by compute_degree
    rw [Polynomial.eq_quadratic_of_degree_le_two h1,
        Polynomial.eq_quadratic_of_degree_le_two h2]
    have c2 : (X^2 + 1 : (ZMod 5)[X]).coeff 2 = ((X - C 2) * (X + C 2) : (ZMod 5)[X]).coeff 2 := by decide
    have c1 : (X^2 + 1 : (ZMod 5)[X]).coeff 1 = ((X - C 2) * (X + C 2) : (ZMod 5)[X]).coeff 1 := by decide
    have c0 : (X^2 + 1 : (ZMod 5)[X]).coeff 0 = ((X - C 2) * (X + C 2) : (ZMod 5)[X]).coeff 0 := by decide
    rw [c2, c1, c0]
  rw [hfac]
  exact (Polynomial.Splits.X_sub_C 2).mul (Polynomial.Splits.X_add_C 2)
