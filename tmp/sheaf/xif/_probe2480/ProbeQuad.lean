import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
open Polynomial
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
#check Polynomial.irreducible_of_degree_le_three_of_not_isRoot
#check Polynomial.irreducible_of_degree_eq_two
#check Polynomial.natDegree_quadratic
#check Polynomial.eval₂_at_apply

example : Irreducible (S2132F2Z.map (Int.castRingHom (ZMod 29))) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [S2132F2Z]
    norm_num
  · intro x hx
    rw [Polynomial.IsRoot] at hx
    simp [S2132F2Z] at hx
    -- hx : 19 + x*24 + x^2*4 = 0 perhaps
    have h : (4 * x^2 + 24 * x + 19 : ZMod 29) = 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using hx
    -- finite check
    revert h
    decide
