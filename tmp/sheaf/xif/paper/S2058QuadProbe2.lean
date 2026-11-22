import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
open Polynomial
#check Polynomial.irreducible_of_degree_le_three_of_not_isRoot
example : Irreducible (C (12 : ZMod 29) + C 6 * X + X^2) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · decide
  · intro x
    decide
