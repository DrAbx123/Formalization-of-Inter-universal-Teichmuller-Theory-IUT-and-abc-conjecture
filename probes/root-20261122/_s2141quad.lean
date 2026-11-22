import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import Mathlib.Algebra.Polynomial.SpecificDegree
open Polynomial
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
example : Irreducible S2132Factor2 := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · decide
  · intro x
    decide
example : S2132Factor2.natDegree = 2 := by
  unfold S2132Factor2
  compute_degree!
example : (C (4:ZMod29) * S2132Factor10).natDegree = 10 := by
  unfold S2132Factor10
  rw [S2132Factor10_eq_s2126]
  compute_degree!
