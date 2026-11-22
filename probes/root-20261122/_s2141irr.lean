import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import Mathlib.Algebra.Polynomial.SpecificDegree
open Polynomial
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
example : Irreducible S2132Factor2 := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (p := S2132Factor2) (by decide) (by decide)]
  decide
