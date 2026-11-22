import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
open Polynomial
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual

example : (S2132F2Z.map (Int.castRingHom (ZMod 29))) =
    (C (19 : ZMod 29) + C 24 * X + C 4 * X ^ 2) := by
  simp only [S2132F2Z, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat]
  norm_num

example : (C (4 : ZMod 29) * X ^ 2 + C 24 * X + C 19).natDegree = 2 := by
  apply Polynomial.natDegree_quadratic
  decide

example : Irreducible (C (4 : ZMod 29) * X ^ 2 + C 24 * X + C 19) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Polynomial.natDegree_quadratic (by decide : (4 : ZMod 29) ≠ 0)]
    simp
  · intro x hx
    rw [Polynomial.IsRoot] at hx
    revert hx
    decide
